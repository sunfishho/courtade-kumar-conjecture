import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf4813Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4813Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090044416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2046727599/1073741824) }, upper := { exponent := 0, mantissa := (31529/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180300781/10180088832) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4813InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4813LocalValidity :
    LeafFacts leaf4813Box leaf4813Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4813Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090044416) }) = true
      norm_num [leaf4813Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4813CertificateValid :
    WideCertificateValid leaf4813Box leaf4813Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi277ValidityFacts
    leaf4813LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4813CoverageChecked :
    coverageCheck (innerAD leaf4813Box) leaf4813InnerLog = true := by
  rfl'

private theorem leaf4813InnerLogValid :
    leaf4813InnerLog.Valid 8 (innerAD leaf4813Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4813CoverageChecked

private noncomputable def leaf4813InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4813InputLogOnePlusV_eq :
    leaf4813InputLogOnePlusV = outerEnclosure 24
      (leaf4813Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4813RoundedFacts : LeafRoundedFacts 8
    leaf4813Certificate.logOnePlusV leaf4813InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4813InputLogOnePlusV_eq }

private noncomputable def leaf4813Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4813InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4813LowerChecked :
    lowerCheck 24 leaf4813Box leaf4813Inputs = true := by
  rfl'

private theorem leaf4813CoversExact : CoversExact 8
    leaf4813Box leaf4813Certificate leaf4813InnerLog leaf4813Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4813RoundedFacts (by rfl)

private theorem leaf4813FlatSound : Sound leaf4813Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4813CertificateValid
    leaf4813InnerLogValid leaf4813CoversExact leaf4813LowerChecked

private noncomputable def leaf4814Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4814Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431165952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2050921645/1073741824) }, upper := { exponent := 0, mantissa := (15797/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868087807/274862331904) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4814InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4814LocalValidity :
    LeafFacts leaf4814Box leaf4814Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4814Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431165952) }) = true
      norm_num [leaf4814Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4814CertificateValid :
    WideCertificateValid leaf4814Box leaf4814Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi277ValidityFacts
    leaf4814LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4814CoverageChecked :
    coverageCheck (innerAD leaf4814Box) leaf4814InnerLog = true := by
  rfl'

private theorem leaf4814InnerLogValid :
    leaf4814InnerLog.Valid 8 (innerAD leaf4814Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4814CoverageChecked

private noncomputable def leaf4814InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4814InputLogOnePlusV_eq :
    leaf4814InputLogOnePlusV = outerEnclosure 24
      (leaf4814Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4814RoundedFacts : LeafRoundedFacts 8
    leaf4814Certificate.logOnePlusV leaf4814InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4814InputLogOnePlusV_eq }

private noncomputable def leaf4814Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4814InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4814LowerChecked :
    lowerCheck 24 leaf4814Box leaf4814Inputs = true := by
  rfl'

private theorem leaf4814CoversExact : CoversExact 8
    leaf4814Box leaf4814Certificate leaf4814InnerLog leaf4814Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4814RoundedFacts (by rfl)

private theorem leaf4814FlatSound : Sound leaf4814Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4814CertificateValid
    leaf4814InnerLogValid leaf4814CoversExact leaf4814LowerChecked

private noncomputable def leaf4815Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4815Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431079936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2061931021/1073741824) }, upper := { exponent := 0, mantissa := (15881/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868001791/274862159872) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4815InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4815LocalValidity :
    LeafFacts leaf4815Box leaf4815Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4815Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431079936) }) = true
      norm_num [leaf4815Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4815CertificateValid :
    WideCertificateValid leaf4815Box leaf4815Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi278ValidityFacts
    leaf4815LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4815CoverageChecked :
    coverageCheck (innerAD leaf4815Box) leaf4815InnerLog = true := by
  rfl'

private theorem leaf4815InnerLogValid :
    leaf4815InnerLog.Valid 8 (innerAD leaf4815Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4815CoverageChecked

private noncomputable def leaf4815InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4815InputLogOnePlusV_eq :
    leaf4815InputLogOnePlusV = outerEnclosure 24
      (leaf4815Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4815RoundedFacts : LeafRoundedFacts 8
    leaf4815Certificate.logOnePlusV leaf4815InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4815InputLogOnePlusV_eq }

private noncomputable def leaf4815Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi278InputQChi innerPair233Input
    leaf4815InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4815LowerChecked :
    lowerCheck 24 leaf4815Box leaf4815Inputs = true := by
  rfl'

private theorem leaf4815CoversExact : CoversExact 8
    leaf4815Box leaf4815Certificate leaf4815InnerLog leaf4815Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi278RoundedFacts
    innerPair233RoundedFacts leaf4815RoundedFacts (by rfl)

private theorem leaf4815FlatSound : Sound leaf4815Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4815CertificateValid
    leaf4815InnerLogValid leaf4815CoversExact leaf4815LowerChecked

private noncomputable def leaf4816Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4816Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431046144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2066190599/1073741824) }, upper := { exponent := 0, mantissa := (7957/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867967999/274862092288) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4816InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4816LocalValidity :
    LeafFacts leaf4816Box leaf4816Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4816Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431046144) }) = true
      norm_num [leaf4816Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4816CertificateValid :
    WideCertificateValid leaf4816Box leaf4816Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi278ValidityFacts
    leaf4816LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4816CoverageChecked :
    coverageCheck (innerAD leaf4816Box) leaf4816InnerLog = true := by
  rfl'

private theorem leaf4816InnerLogValid :
    leaf4816InnerLog.Valid 8 (innerAD leaf4816Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4816CoverageChecked

private noncomputable def leaf4816InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4816InputLogOnePlusV_eq :
    leaf4816InputLogOnePlusV = outerEnclosure 24
      (leaf4816Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4816RoundedFacts : LeafRoundedFacts 8
    leaf4816Certificate.logOnePlusV leaf4816InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4816InputLogOnePlusV_eq }

private noncomputable def leaf4816Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi278InputQChi innerPair304Input
    leaf4816InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4816LowerChecked :
    lowerCheck 24 leaf4816Box leaf4816Inputs = true := by
  rfl'

private theorem leaf4816CoversExact : CoversExact 8
    leaf4816Box leaf4816Certificate leaf4816InnerLog leaf4816Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi278RoundedFacts
    innerPair304RoundedFacts leaf4816RoundedFacts (by rfl)

private theorem leaf4816FlatSound : Sound leaf4816Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4816CertificateValid
    leaf4816InnerLogValid leaf4816CoversExact leaf4816LowerChecked

private noncomputable def leaf4817Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4817Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431132672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2055115691/1073741824) }, upper := { exponent := 0, mantissa := (31659/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868054527/274862265344) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4817InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4817LocalValidity :
    LeafFacts leaf4817Box leaf4817Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4817Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431132672) }) = true
      norm_num [leaf4817Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4817CertificateValid :
    WideCertificateValid leaf4817Box leaf4817Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi277ValidityFacts
    leaf4817LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4817CoverageChecked :
    coverageCheck (innerAD leaf4817Box) leaf4817InnerLog = true := by
  rfl'

private theorem leaf4817InnerLogValid :
    leaf4817InnerLog.Valid 8 (innerAD leaf4817Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4817CoverageChecked

private noncomputable def leaf4817InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4817InputLogOnePlusV_eq :
    leaf4817InputLogOnePlusV = outerEnclosure 24
      (leaf4817Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4817RoundedFacts : LeafRoundedFacts 8
    leaf4817Certificate.logOnePlusV leaf4817InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4817InputLogOnePlusV_eq }

private noncomputable def leaf4817Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4817InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4817LowerChecked :
    lowerCheck 24 leaf4817Box leaf4817Inputs = true := by
  rfl'

private theorem leaf4817CoversExact : CoversExact 8
    leaf4817Box leaf4817Certificate leaf4817InnerLog leaf4817Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4817RoundedFacts (by rfl)

private theorem leaf4817FlatSound : Sound leaf4817Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4817CertificateValid
    leaf4817InnerLogValid leaf4817CoversExact leaf4817LowerChecked

private noncomputable def leaf4818Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4818Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810366464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2059309737/1073741824) }, upper := { exponent := 0, mantissa := (7931/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622673749/91620732928) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4818InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4818LocalValidity :
    LeafFacts leaf4818Box leaf4818Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4818Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810366464) }) = true
      norm_num [leaf4818Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4818CertificateValid :
    WideCertificateValid leaf4818Box leaf4818Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi277ValidityFacts
    leaf4818LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4818CoverageChecked :
    coverageCheck (innerAD leaf4818Box) leaf4818InnerLog = true := by
  rfl'

private theorem leaf4818InnerLogValid :
    leaf4818InnerLog.Valid 8 (innerAD leaf4818Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4818CoverageChecked

private noncomputable def leaf4818InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4818InputLogOnePlusV_eq :
    leaf4818InputLogOnePlusV = outerEnclosure 24
      (leaf4818Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4818RoundedFacts : LeafRoundedFacts 8
    leaf4818Certificate.logOnePlusV leaf4818InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4818InputLogOnePlusV_eq }

private noncomputable def leaf4818Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4818InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4818LowerChecked :
    lowerCheck 24 leaf4818Box leaf4818Inputs = true := by
  rfl'

private theorem leaf4818CoversExact : CoversExact 8
    leaf4818Box leaf4818Certificate leaf4818InnerLog leaf4818Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4818RoundedFacts (by rfl)

private theorem leaf4818FlatSound : Sound leaf4818Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4818CertificateValid
    leaf4818InnerLogValid leaf4818CoversExact leaf4818LowerChecked

private noncomputable def leaf4819Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4819Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431012352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2070450177/1073741824) }, upper := { exponent := 0, mantissa := (15947/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867934207/274862024704) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4819InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4819LocalValidity :
    LeafFacts leaf4819Box leaf4819Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4819Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431012352) }) = true
      norm_num [leaf4819Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4819CertificateValid :
    WideCertificateValid leaf4819Box leaf4819Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi278ValidityFacts
    leaf4819LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4819CoverageChecked :
    coverageCheck (innerAD leaf4819Box) leaf4819InnerLog = true := by
  rfl'

private theorem leaf4819InnerLogValid :
    leaf4819InnerLog.Valid 8 (innerAD leaf4819Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4819CoverageChecked

private noncomputable def leaf4819InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4819InputLogOnePlusV_eq :
    leaf4819InputLogOnePlusV = outerEnclosure 24
      (leaf4819Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4819RoundedFacts : LeafRoundedFacts 8
    leaf4819Certificate.logOnePlusV leaf4819InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4819InputLogOnePlusV_eq }

private noncomputable def leaf4819Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi278InputQChi innerPair304Input
    leaf4819InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4819LowerChecked :
    lowerCheck 24 leaf4819Box leaf4819Inputs = true := by
  rfl'

private theorem leaf4819CoversExact : CoversExact 8
    leaf4819Box leaf4819Certificate leaf4819InnerLog leaf4819Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi278RoundedFacts
    innerPair304RoundedFacts leaf4819RoundedFacts (by rfl)

private theorem leaf4819FlatSound : Sound leaf4819Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4819CertificateValid
    leaf4819InnerLogValid leaf4819CoversExact leaf4819LowerChecked

private noncomputable def leaf4820Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4820Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486195712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2074709755/1073741824) }, upper := { exponent := 0, mantissa := (3995/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973580083/54972391424) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4820InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4820LocalValidity :
    LeafFacts leaf4820Box leaf4820Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4820Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486195712) }) = true
      norm_num [leaf4820Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4820CertificateValid :
    WideCertificateValid leaf4820Box leaf4820Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi278ValidityFacts
    leaf4820LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4820CoverageChecked :
    coverageCheck (innerAD leaf4820Box) leaf4820InnerLog = true := by
  rfl'

private theorem leaf4820InnerLogValid :
    leaf4820InnerLog.Valid 8 (innerAD leaf4820Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4820CoverageChecked

private noncomputable def leaf4820InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4820InputLogOnePlusV_eq :
    leaf4820InputLogOnePlusV = outerEnclosure 24
      (leaf4820Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4820RoundedFacts : LeafRoundedFacts 8
    leaf4820Certificate.logOnePlusV leaf4820InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4820InputLogOnePlusV_eq }

private noncomputable def leaf4820Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi278InputQChi innerPair304Input
    leaf4820InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4820LowerChecked :
    lowerCheck 24 leaf4820Box leaf4820Inputs = true := by
  rfl'

private theorem leaf4820CoversExact : CoversExact 8
    leaf4820Box leaf4820Certificate leaf4820InnerLog leaf4820Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi278RoundedFacts
    innerPair304RoundedFacts leaf4820RoundedFacts (by rfl)

private theorem leaf4820FlatSound : Sound leaf4820Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4820CertificateValid
    leaf4820InnerLogValid leaf4820CoversExact leaf4820LowerChecked

private noncomputable def leaf4821Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4821Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486192128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2077134443/1073741824) }, upper := { exponent := 0, mantissa := (31995/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973576499/54972384256) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4821InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4821LocalValidity :
    LeafFacts leaf4821Box leaf4821Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4821Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486192128) }) = true
      norm_num [leaf4821Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4821CertificateValid :
    WideCertificateValid leaf4821Box leaf4821Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi275ValidityFacts
    leaf4821LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4821CoverageChecked :
    coverageCheck (innerAD leaf4821Box) leaf4821InnerLog = true := by
  rfl'

private theorem leaf4821InnerLogValid :
    leaf4821InnerLog.Valid 8 (innerAD leaf4821Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4821CoverageChecked

private noncomputable def leaf4821InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4821InputLogOnePlusV_eq :
    leaf4821InputLogOnePlusV = outerEnclosure 24
      (leaf4821Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4821RoundedFacts : LeafRoundedFacts 8
    leaf4821Certificate.logOnePlusV leaf4821InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4821InputLogOnePlusV_eq }

private noncomputable def leaf4821Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi275InputQChi innerPair101Input
    leaf4821InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4821LowerChecked :
    lowerCheck 24 leaf4821Box leaf4821Inputs = true := by
  rfl'

private theorem leaf4821CoversExact : CoversExact 8
    leaf4821Box leaf4821Certificate leaf4821InnerLog leaf4821Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi275RoundedFacts
    innerPair101RoundedFacts leaf4821RoundedFacts (by rfl)

private theorem leaf4821FlatSound : Sound leaf4821Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4821CertificateValid
    leaf4821InnerLogValid leaf4821CoversExact leaf4821LowerChecked

private noncomputable def leaf4822Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4822Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430926336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2081459553/1073741824) }, upper := { exponent := 0, mantissa := (16031/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867848191/274861852672) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4822InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4822LocalValidity :
    LeafFacts leaf4822Box leaf4822Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4822Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430926336) }) = true
      norm_num [leaf4822Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4822CertificateValid :
    WideCertificateValid leaf4822Box leaf4822Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi275ValidityFacts
    leaf4822LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4822CoverageChecked :
    coverageCheck (innerAD leaf4822Box) leaf4822InnerLog = true := by
  rfl'

private theorem leaf4822InnerLogValid :
    leaf4822InnerLog.Valid 8 (innerAD leaf4822Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4822CoverageChecked

private noncomputable def leaf4822InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4822InputLogOnePlusV_eq :
    leaf4822InputLogOnePlusV = outerEnclosure 24
      (leaf4822Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4822RoundedFacts : LeafRoundedFacts 8
    leaf4822Certificate.logOnePlusV leaf4822InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4822InputLogOnePlusV_eq }

private noncomputable def leaf4822Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4822InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4822LowerChecked :
    lowerCheck 24 leaf4822Box leaf4822Inputs = true := by
  rfl'

private theorem leaf4822CoversExact : CoversExact 8
    leaf4822Box leaf4822Certificate leaf4822InnerLog leaf4822Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4822RoundedFacts (by rfl)

private theorem leaf4822FlatSound : Sound leaf4822Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4822CertificateValid
    leaf4822InnerLogValid leaf4822CoversExact leaf4822LowerChecked

private noncomputable def leaf4823Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4823Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810280448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2092337865/1073741824) }, upper := { exponent := 0, mantissa := (8057/4096) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622587733/91620560896) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4823InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4823LocalValidity :
    LeafFacts leaf4823Box leaf4823Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4823Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810280448) }) = true
      norm_num [leaf4823Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4823CertificateValid :
    WideCertificateValid leaf4823Box leaf4823Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi276ValidityFacts
    leaf4823LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4823CoverageChecked :
    coverageCheck (innerAD leaf4823Box) leaf4823InnerLog = true := by
  rfl'

private theorem leaf4823InnerLogValid :
    leaf4823InnerLog.Valid 8 (innerAD leaf4823Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4823CoverageChecked

private noncomputable def leaf4823InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4823InputLogOnePlusV_eq :
    leaf4823InputLogOnePlusV = outerEnclosure 24
      (leaf4823Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4823RoundedFacts : LeafRoundedFacts 8
    leaf4823Certificate.logOnePlusV leaf4823InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4823InputLogOnePlusV_eq }

private noncomputable def leaf4823Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4823InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4823LowerChecked :
    lowerCheck 24 leaf4823Box leaf4823Inputs = true := by
  rfl'

private theorem leaf4823CoversExact : CoversExact 8
    leaf4823Box leaf4823Certificate leaf4823InnerLog leaf4823Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4823RoundedFacts (by rfl)

private theorem leaf4823FlatSound : Sound leaf4823Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4823CertificateValid
    leaf4823InnerLogValid leaf4823CoversExact leaf4823LowerChecked

private noncomputable def leaf4824Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4824Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430806528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2096728507/1073741824) }, upper := { exponent := 0, mantissa := (4037/2048) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867728383/274861613056) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4824InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4824LocalValidity :
    LeafFacts leaf4824Box leaf4824Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4824Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430806528) }) = true
      norm_num [leaf4824Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4824CertificateValid :
    WideCertificateValid leaf4824Box leaf4824Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi276ValidityFacts
    leaf4824LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4824CoverageChecked :
    coverageCheck (innerAD leaf4824Box) leaf4824InnerLog = true := by
  rfl'

private theorem leaf4824InnerLogValid :
    leaf4824InnerLog.Valid 8 (innerAD leaf4824Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4824CoverageChecked

private noncomputable def leaf4824InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4824InputLogOnePlusV_eq :
    leaf4824InputLogOnePlusV = outerEnclosure 24
      (leaf4824Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4824RoundedFacts : LeafRoundedFacts 8
    leaf4824Certificate.logOnePlusV leaf4824InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4824InputLogOnePlusV_eq }

private noncomputable def leaf4824Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4824InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4824LowerChecked :
    lowerCheck 24 leaf4824Box leaf4824Inputs = true := by
  rfl'

private theorem leaf4824CoversExact : CoversExact 8
    leaf4824Box leaf4824Certificate leaf4824InnerLog leaf4824Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4824RoundedFacts (by rfl)

private theorem leaf4824FlatSound : Sound leaf4824Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4824CertificateValid
    leaf4824InnerLogValid leaf4824CoversExact leaf4824LowerChecked

private noncomputable def leaf4825Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4825Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810297344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2085784663/1073741824) }, upper := { exponent := 0, mantissa := (32129/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622604629/91620594688) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4825InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4825LocalValidity :
    LeafFacts leaf4825Box leaf4825Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4825Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810297344) }) = true
      norm_num [leaf4825Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4825CertificateValid :
    WideCertificateValid leaf4825Box leaf4825Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi275ValidityFacts
    leaf4825LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4825CoverageChecked :
    coverageCheck (innerAD leaf4825Box) leaf4825InnerLog = true := by
  rfl'

private theorem leaf4825InnerLogValid :
    leaf4825InnerLog.Valid 8 (innerAD leaf4825Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4825CoverageChecked

private noncomputable def leaf4825InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4825InputLogOnePlusV_eq :
    leaf4825InputLogOnePlusV = outerEnclosure 24
      (leaf4825Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4825RoundedFacts : LeafRoundedFacts 8
    leaf4825Certificate.logOnePlusV leaf4825InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4825InputLogOnePlusV_eq }

private noncomputable def leaf4825Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4825InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4825LowerChecked :
    lowerCheck 24 leaf4825Box leaf4825Inputs = true := by
  rfl'

private theorem leaf4825CoversExact : CoversExact 8
    leaf4825Box leaf4825Certificate leaf4825InnerLog leaf4825Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4825RoundedFacts (by rfl)

private theorem leaf4825FlatSound : Sound leaf4825Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4825CertificateValid
    leaf4825InnerLogValid leaf4825CoversExact leaf4825LowerChecked

private noncomputable def leaf4826Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4826Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430857728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2090109773/1073741824) }, upper := { exponent := 0, mantissa := (8049/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867779583/274861715456) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4826InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4826LocalValidity :
    LeafFacts leaf4826Box leaf4826Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4826Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430857728) }) = true
      norm_num [leaf4826Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4826CertificateValid :
    WideCertificateValid leaf4826Box leaf4826Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi275ValidityFacts
    leaf4826LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4826CoverageChecked :
    coverageCheck (innerAD leaf4826Box) leaf4826InnerLog = true := by
  rfl'

private theorem leaf4826InnerLogValid :
    leaf4826InnerLog.Valid 8 (innerAD leaf4826Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4826CoverageChecked

private noncomputable def leaf4826InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4826InputLogOnePlusV_eq :
    leaf4826InputLogOnePlusV = outerEnclosure 24
      (leaf4826Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4826RoundedFacts : LeafRoundedFacts 8
    leaf4826Certificate.logOnePlusV leaf4826InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4826InputLogOnePlusV_eq }

private noncomputable def leaf4826Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4826InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4826LowerChecked :
    lowerCheck 24 leaf4826Box leaf4826Inputs = true := by
  rfl'

private theorem leaf4826CoversExact : CoversExact 8
    leaf4826Box leaf4826Certificate leaf4826InnerLog leaf4826Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4826RoundedFacts (by rfl)

private theorem leaf4826FlatSound : Sound leaf4826Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4826CertificateValid
    leaf4826InnerLogValid leaf4826CoversExact leaf4826LowerChecked

private noncomputable def leaf4827Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4827Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430771712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2101119149/1073741824) }, upper := { exponent := 0, mantissa := (8091/4096) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867693567/274861543424) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4827InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4827LocalValidity :
    LeafFacts leaf4827Box leaf4827Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4827Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430771712) }) = true
      norm_num [leaf4827Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4827CertificateValid :
    WideCertificateValid leaf4827Box leaf4827Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi276ValidityFacts
    leaf4827LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4827CoverageChecked :
    coverageCheck (innerAD leaf4827Box) leaf4827InnerLog = true := by
  rfl'

private theorem leaf4827InnerLogValid :
    leaf4827InnerLog.Valid 8 (innerAD leaf4827Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4827CoverageChecked

private noncomputable def leaf4827InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4827InputLogOnePlusV_eq :
    leaf4827InputLogOnePlusV = outerEnclosure 24
      (leaf4827Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4827RoundedFacts : LeafRoundedFacts 8
    leaf4827Certificate.logOnePlusV leaf4827InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4827InputLogOnePlusV_eq }

private noncomputable def leaf4827Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4827InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4827LowerChecked :
    lowerCheck 24 leaf4827Box leaf4827Inputs = true := by
  rfl'

private theorem leaf4827CoversExact : CoversExact 8
    leaf4827Box leaf4827Certificate leaf4827InnerLog leaf4827Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4827RoundedFacts (by rfl)

private theorem leaf4827FlatSound : Sound leaf4827Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4827CertificateValid
    leaf4827InnerLogValid leaf4827CoversExact leaf4827LowerChecked

private noncomputable def leaf4828Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4828Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810245632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2105509791/1073741824) }, upper := { exponent := 0, mantissa := (2027/1024) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622552917/91620491264) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4828InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4828LocalValidity :
    LeafFacts leaf4828Box leaf4828Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4828Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810245632) }) = true
      norm_num [leaf4828Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4828CertificateValid :
    WideCertificateValid leaf4828Box leaf4828Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi276ValidityFacts
    leaf4828LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4828CoverageChecked :
    coverageCheck (innerAD leaf4828Box) leaf4828InnerLog = true := by
  rfl'

private theorem leaf4828InnerLogValid :
    leaf4828InnerLog.Valid 8 (innerAD leaf4828Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4828CoverageChecked

private noncomputable def leaf4828InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4828InputLogOnePlusV_eq :
    leaf4828InputLogOnePlusV = outerEnclosure 24
      (leaf4828Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4828RoundedFacts : LeafRoundedFacts 8
    leaf4828Certificate.logOnePlusV leaf4828InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4828InputLogOnePlusV_eq }

private noncomputable def leaf4828Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4828InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4828LowerChecked :
    lowerCheck 24 leaf4828Box leaf4828Inputs = true := by
  rfl'

private theorem leaf4828CoversExact : CoversExact 8
    leaf4828Box leaf4828Certificate leaf4828InnerLog leaf4828Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4828RoundedFacts (by rfl)

private theorem leaf4828FlatSound : Sound leaf4828Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4828CertificateValid
    leaf4828InnerLogValid leaf4828CoversExact leaf4828LowerChecked

private noncomputable def leaf4829Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4829Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431066112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2063503783/1073741824) }, upper := { exponent := 0, mantissa := (31789/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867987967/274862132224) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4829InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf4829LocalValidity :
    LeafFacts leaf4829Box leaf4829Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4829Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431066112) }) = true
      norm_num [leaf4829Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4829CertificateValid :
    WideCertificateValid leaf4829Box leaf4829Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi277ValidityFacts
    leaf4829LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4829CoverageChecked :
    coverageCheck (innerAD leaf4829Box) leaf4829InnerLog = true := by
  rfl'

private theorem leaf4829InnerLogValid :
    leaf4829InnerLog.Valid 8 (innerAD leaf4829Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf4829CoverageChecked

private noncomputable def leaf4829InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4829InputLogOnePlusV_eq :
    leaf4829InputLogOnePlusV = outerEnclosure 24
      (leaf4829Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4829RoundedFacts : LeafRoundedFacts 8
    leaf4829Certificate.logOnePlusV leaf4829InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4829InputLogOnePlusV_eq }

private noncomputable def leaf4829Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi277InputQChi innerPair233Input
    leaf4829InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4829LowerChecked :
    lowerCheck 24 leaf4829Box leaf4829Inputs = true := by
  rfl'

private theorem leaf4829CoversExact : CoversExact 8
    leaf4829Box leaf4829Certificate leaf4829InnerLog leaf4829Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi277RoundedFacts
    innerPair233RoundedFacts leaf4829RoundedFacts (by rfl)

private theorem leaf4829FlatSound : Sound leaf4829Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4829CertificateValid
    leaf4829InnerLogValid leaf4829CoversExact leaf4829LowerChecked

private noncomputable def leaf4830Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4830Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431032832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2067697829/1073741824) }, upper := { exponent := 0, mantissa := (15927/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867954687/274862065664) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4830InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4830LocalValidity :
    LeafFacts leaf4830Box leaf4830Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4830Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431032832) }) = true
      norm_num [leaf4830Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4830CertificateValid :
    WideCertificateValid leaf4830Box leaf4830Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi277ValidityFacts
    leaf4830LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4830CoverageChecked :
    coverageCheck (innerAD leaf4830Box) leaf4830InnerLog = true := by
  rfl'

private theorem leaf4830InnerLogValid :
    leaf4830InnerLog.Valid 8 (innerAD leaf4830Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4830CoverageChecked

private noncomputable def leaf4830InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4830InputLogOnePlusV_eq :
    leaf4830InputLogOnePlusV = outerEnclosure 24
      (leaf4830Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4830RoundedFacts : LeafRoundedFacts 8
    leaf4830Certificate.logOnePlusV leaf4830InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4830InputLogOnePlusV_eq }

private noncomputable def leaf4830Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi277InputQChi innerPair304Input
    leaf4830InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4830LowerChecked :
    lowerCheck 24 leaf4830Box leaf4830Inputs = true := by
  rfl'

private theorem leaf4830CoversExact : CoversExact 8
    leaf4830Box leaf4830Certificate leaf4830InnerLog leaf4830Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi277RoundedFacts
    innerPair304RoundedFacts leaf4830RoundedFacts (by rfl)

private theorem leaf4830FlatSound : Sound leaf4830Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4830CertificateValid
    leaf4830InnerLogValid leaf4830CoversExact leaf4830LowerChecked

private noncomputable def leaf4831Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4831Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430944768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2078969333/1073741824) }, upper := { exponent := 0, mantissa := (16013/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867866623/274861889536) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4831InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf4831LocalValidity :
    LeafFacts leaf4831Box leaf4831Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4831Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430944768) }) = true
      norm_num [leaf4831Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4831CertificateValid :
    WideCertificateValid leaf4831Box leaf4831Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi278ValidityFacts
    leaf4831LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4831CoverageChecked :
    coverageCheck (innerAD leaf4831Box) leaf4831InnerLog = true := by
  rfl'

private theorem leaf4831InnerLogValid :
    leaf4831InnerLog.Valid 8 (innerAD leaf4831Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf4831CoverageChecked

private noncomputable def leaf4831InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4831InputLogOnePlusV_eq :
    leaf4831InputLogOnePlusV = outerEnclosure 24
      (leaf4831Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4831RoundedFacts : LeafRoundedFacts 8
    leaf4831Certificate.logOnePlusV leaf4831InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4831InputLogOnePlusV_eq }

private noncomputable def leaf4831Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi278InputQChi innerPair306Input
    leaf4831InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4831LowerChecked :
    lowerCheck 24 leaf4831Box leaf4831Inputs = true := by
  rfl'

private theorem leaf4831CoversExact : CoversExact 8
    leaf4831Box leaf4831Certificate leaf4831InnerLog leaf4831Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi278RoundedFacts
    innerPair306RoundedFacts leaf4831RoundedFacts (by rfl)

private theorem leaf4831FlatSound : Sound leaf4831Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4831CertificateValid
    leaf4831InnerLogValid leaf4831CoversExact leaf4831LowerChecked

private noncomputable def leaf4832Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4832Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430910976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2083228911/1073741824) }, upper := { exponent := 0, mantissa := (8023/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867832831/274861821952) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4832InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4832LocalValidity :
    LeafFacts leaf4832Box leaf4832Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4832Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430910976) }) = true
      norm_num [leaf4832Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4832CertificateValid :
    WideCertificateValid leaf4832Box leaf4832Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi278ValidityFacts
    leaf4832LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4832CoverageChecked :
    coverageCheck (innerAD leaf4832Box) leaf4832InnerLog = true := by
  rfl'

private theorem leaf4832InnerLogValid :
    leaf4832InnerLog.Valid 8 (innerAD leaf4832Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4832CoverageChecked

private noncomputable def leaf4832InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4832InputLogOnePlusV_eq :
    leaf4832InputLogOnePlusV = outerEnclosure 24
      (leaf4832Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4832RoundedFacts : LeafRoundedFacts 8
    leaf4832Certificate.logOnePlusV leaf4832InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4832InputLogOnePlusV_eq }

private noncomputable def leaf4832Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi278InputQChi innerPair113Input
    leaf4832InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4832LowerChecked :
    lowerCheck 24 leaf4832Box leaf4832Inputs = true := by
  rfl'

private theorem leaf4832CoversExact : CoversExact 8
    leaf4832Box leaf4832Certificate leaf4832InnerLog leaf4832Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi278RoundedFacts
    innerPair113RoundedFacts leaf4832RoundedFacts (by rfl)

private theorem leaf4832FlatSound : Sound leaf4832Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4832CertificateValid
    leaf4832InnerLogValid leaf4832CoversExact leaf4832LowerChecked

private noncomputable def leaf4833Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4833Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810333184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2071891875/1073741824) }, upper := { exponent := 0, mantissa := (31919/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622640469/91620666368) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4833InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4833LocalValidity :
    LeafFacts leaf4833Box leaf4833Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4833Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810333184) }) = true
      norm_num [leaf4833Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4833CertificateValid :
    WideCertificateValid leaf4833Box leaf4833Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi277ValidityFacts
    leaf4833LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4833CoverageChecked :
    coverageCheck (innerAD leaf4833Box) leaf4833InnerLog = true := by
  rfl'

private theorem leaf4833InnerLogValid :
    leaf4833InnerLog.Valid 8 (innerAD leaf4833Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4833CoverageChecked

private noncomputable def leaf4833InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4833InputLogOnePlusV_eq :
    leaf4833InputLogOnePlusV = outerEnclosure 24
      (leaf4833Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4833RoundedFacts : LeafRoundedFacts 8
    leaf4833Certificate.logOnePlusV leaf4833InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4833InputLogOnePlusV_eq }

private noncomputable def leaf4833Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi277InputQChi innerPair304Input
    leaf4833InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4833LowerChecked :
    lowerCheck 24 leaf4833Box leaf4833Inputs = true := by
  rfl'

private theorem leaf4833CoversExact : CoversExact 8
    leaf4833Box leaf4833Certificate leaf4833InnerLog leaf4833Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi277RoundedFacts
    innerPair304RoundedFacts leaf4833RoundedFacts (by rfl)

private theorem leaf4833FlatSound : Sound leaf4833Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4833CertificateValid
    leaf4833InnerLogValid leaf4833CoversExact leaf4833LowerChecked

private noncomputable def leaf4834Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4834Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430966272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2076085921/1073741824) }, upper := { exponent := 0, mantissa := (1999/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867888127/274861932544) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4834InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4834LocalValidity :
    LeafFacts leaf4834Box leaf4834Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4834Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430966272) }) = true
      norm_num [leaf4834Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4834CertificateValid :
    WideCertificateValid leaf4834Box leaf4834Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi277ValidityFacts
    leaf4834LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4834CoverageChecked :
    coverageCheck (innerAD leaf4834Box) leaf4834InnerLog = true := by
  rfl'

private theorem leaf4834InnerLogValid :
    leaf4834InnerLog.Valid 8 (innerAD leaf4834Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4834CoverageChecked

private noncomputable def leaf4834InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4834InputLogOnePlusV_eq :
    leaf4834InputLogOnePlusV = outerEnclosure 24
      (leaf4834Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4834RoundedFacts : LeafRoundedFacts 8
    leaf4834Certificate.logOnePlusV leaf4834InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4834InputLogOnePlusV_eq }

private noncomputable def leaf4834Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi277InputQChi innerPair304Input
    leaf4834InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4834LowerChecked :
    lowerCheck 24 leaf4834Box leaf4834Inputs = true := by
  rfl'

private theorem leaf4834CoversExact : CoversExact 8
    leaf4834Box leaf4834Certificate leaf4834InnerLog leaf4834Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi277RoundedFacts
    innerPair304RoundedFacts leaf4834RoundedFacts (by rfl)

private theorem leaf4834FlatSound : Sound leaf4834Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4834CertificateValid
    leaf4834InnerLogValid leaf4834CoversExact leaf4834LowerChecked

private noncomputable def leaf4835Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4835Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430877184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2087488489/1073741824) }, upper := { exponent := 0, mantissa := (16079/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867799039/274861754368) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4835InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4835LocalValidity :
    LeafFacts leaf4835Box leaf4835Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4835Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430877184) }) = true
      norm_num [leaf4835Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4835CertificateValid :
    WideCertificateValid leaf4835Box leaf4835Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi278ValidityFacts
    leaf4835LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4835CoverageChecked :
    coverageCheck (innerAD leaf4835Box) leaf4835InnerLog = true := by
  rfl'

private theorem leaf4835InnerLogValid :
    leaf4835InnerLog.Valid 8 (innerAD leaf4835Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4835CoverageChecked

private noncomputable def leaf4835InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4835InputLogOnePlusV_eq :
    leaf4835InputLogOnePlusV = outerEnclosure 24
      (leaf4835Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4835RoundedFacts : LeafRoundedFacts 8
    leaf4835Certificate.logOnePlusV leaf4835InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4835InputLogOnePlusV_eq }

private noncomputable def leaf4835Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi278InputQChi innerPair113Input
    leaf4835InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4835LowerChecked :
    lowerCheck 24 leaf4835Box leaf4835Inputs = true := by
  rfl'

private theorem leaf4835CoversExact : CoversExact 8
    leaf4835Box leaf4835Certificate leaf4835InnerLog leaf4835Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi278RoundedFacts
    innerPair113RoundedFacts leaf4835RoundedFacts (by rfl)

private theorem leaf4835FlatSound : Sound leaf4835Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4835CertificateValid
    leaf4835InnerLogValid leaf4835CoversExact leaf4835LowerChecked

private noncomputable def leaf4836Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4836Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430843392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2091748067/1073741824) }, upper := { exponent := 0, mantissa := (1007/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867765247/274861686784) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4836InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4836LocalValidity :
    LeafFacts leaf4836Box leaf4836Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4836Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430843392) }) = true
      norm_num [leaf4836Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4836CertificateValid :
    WideCertificateValid leaf4836Box leaf4836Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi278ValidityFacts
    leaf4836LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4836CoverageChecked :
    coverageCheck (innerAD leaf4836Box) leaf4836InnerLog = true := by
  rfl'

private theorem leaf4836InnerLogValid :
    leaf4836InnerLog.Valid 8 (innerAD leaf4836Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4836CoverageChecked

private noncomputable def leaf4836InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4836InputLogOnePlusV_eq :
    leaf4836InputLogOnePlusV = outerEnclosure 24
      (leaf4836Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4836RoundedFacts : LeafRoundedFacts 8
    leaf4836Certificate.logOnePlusV leaf4836InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4836InputLogOnePlusV_eq }

private noncomputable def leaf4836Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi278InputQChi innerPair108Input
    leaf4836InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4836LowerChecked :
    lowerCheck 24 leaf4836Box leaf4836Inputs = true := by
  rfl'

private theorem leaf4836CoversExact : CoversExact 8
    leaf4836Box leaf4836Certificate leaf4836InnerLog leaf4836Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf4836RoundedFacts (by rfl)

private theorem leaf4836FlatSound : Sound leaf4836Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4836CertificateValid
    leaf4836InnerLogValid leaf4836CoversExact leaf4836LowerChecked

private noncomputable def leaf4837Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4837Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430823424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2094434883/1073741824) }, upper := { exponent := 0, mantissa := (32263/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867745279/274861646848) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4837InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4837LocalValidity :
    LeafFacts leaf4837Box leaf4837Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4837Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430823424) }) = true
      norm_num [leaf4837Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4837CertificateValid :
    WideCertificateValid leaf4837Box leaf4837Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi275ValidityFacts
    leaf4837LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4837CoverageChecked :
    coverageCheck (innerAD leaf4837Box) leaf4837InnerLog = true := by
  rfl'

private theorem leaf4837InnerLogValid :
    leaf4837InnerLog.Valid 8 (innerAD leaf4837Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4837CoverageChecked

private noncomputable def leaf4837InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4837InputLogOnePlusV_eq :
    leaf4837InputLogOnePlusV = outerEnclosure 24
      (leaf4837Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4837RoundedFacts : LeafRoundedFacts 8
    leaf4837Certificate.logOnePlusV leaf4837InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4837InputLogOnePlusV_eq }

private noncomputable def leaf4837Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4837InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4837LowerChecked :
    lowerCheck 24 leaf4837Box leaf4837Inputs = true := by
  rfl'

private theorem leaf4837CoversExact : CoversExact 8
    leaf4837Box leaf4837Certificate leaf4837InnerLog leaf4837Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4837RoundedFacts (by rfl)

private theorem leaf4837FlatSound : Sound leaf4837Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4837CertificateValid
    leaf4837InnerLogValid leaf4837CoversExact leaf4837LowerChecked

private noncomputable def leaf4838Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4838Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054017536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2098759993/1073741824) }, upper := { exponent := 0, mantissa := (16165/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108171355/6108035072) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4838InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4838LocalValidity :
    LeafFacts leaf4838Box leaf4838Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4838Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054017536) }) = true
      norm_num [leaf4838Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4838CertificateValid :
    WideCertificateValid leaf4838Box leaf4838Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi275ValidityFacts
    leaf4838LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4838CoverageChecked :
    coverageCheck (innerAD leaf4838Box) leaf4838InnerLog = true := by
  rfl'

private theorem leaf4838InnerLogValid :
    leaf4838InnerLog.Valid 8 (innerAD leaf4838Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4838CoverageChecked

private noncomputable def leaf4838InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4838InputLogOnePlusV_eq :
    leaf4838InputLogOnePlusV = outerEnclosure 24
      (leaf4838Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4838RoundedFacts : LeafRoundedFacts 8
    leaf4838Certificate.logOnePlusV leaf4838InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4838InputLogOnePlusV_eq }

private noncomputable def leaf4838Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4838InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4838LowerChecked :
    lowerCheck 24 leaf4838Box leaf4838Inputs = true := by
  rfl'

private theorem leaf4838CoversExact : CoversExact 8
    leaf4838Box leaf4838Certificate leaf4838InnerLog leaf4838Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4838RoundedFacts (by rfl)

private theorem leaf4838FlatSound : Sound leaf4838Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4838CertificateValid
    leaf4838InnerLogValid leaf4838CoversExact leaf4838LowerChecked

private noncomputable def leaf4839Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4839Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486140416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2109900433/1073741824) }, upper := { exponent := 0, mantissa := (8125/4096) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973524787/54972280832) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4839InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4839LocalValidity :
    LeafFacts leaf4839Box leaf4839Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4839Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486140416) }) = true
      norm_num [leaf4839Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4839CertificateValid :
    WideCertificateValid leaf4839Box leaf4839Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi276ValidityFacts
    leaf4839LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4839CoverageChecked :
    coverageCheck (innerAD leaf4839Box) leaf4839InnerLog = true := by
  rfl'

private theorem leaf4839InnerLogValid :
    leaf4839InnerLog.Valid 8 (innerAD leaf4839Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4839CoverageChecked

private noncomputable def leaf4839InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4839InputLogOnePlusV_eq :
    leaf4839InputLogOnePlusV = outerEnclosure 24
      (leaf4839Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4839RoundedFacts : LeafRoundedFacts 8
    leaf4839Certificate.logOnePlusV leaf4839InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4839InputLogOnePlusV_eq }

private noncomputable def leaf4839Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4839InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4839LowerChecked :
    lowerCheck 24 leaf4839Box leaf4839Inputs = true := by
  rfl'

private theorem leaf4839CoversExact : CoversExact 8
    leaf4839Box leaf4839Certificate leaf4839InnerLog leaf4839Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4839RoundedFacts (by rfl)

private theorem leaf4839FlatSound : Sound leaf4839Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4839CertificateValid
    leaf4839InnerLogValid leaf4839CoversExact leaf4839LowerChecked

private noncomputable def leaf4840Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4840Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430667264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2114291075/1073741824) }, upper := { exponent := 0, mantissa := (4071/2048) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867589119/274861334528) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4840InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4840LocalValidity :
    LeafFacts leaf4840Box leaf4840Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4840Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430667264) }) = true
      norm_num [leaf4840Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4840CertificateValid :
    WideCertificateValid leaf4840Box leaf4840Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi276ValidityFacts
    leaf4840LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4840CoverageChecked :
    coverageCheck (innerAD leaf4840Box) leaf4840InnerLog = true := by
  rfl'

private theorem leaf4840InnerLogValid :
    leaf4840InnerLog.Valid 8 (innerAD leaf4840Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4840CoverageChecked

private noncomputable def leaf4840InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4840InputLogOnePlusV_eq :
    leaf4840InputLogOnePlusV = outerEnclosure 24
      (leaf4840Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4840RoundedFacts : LeafRoundedFacts 8
    leaf4840Certificate.logOnePlusV leaf4840InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4840InputLogOnePlusV_eq }

private noncomputable def leaf4840Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4840InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4840LowerChecked :
    lowerCheck 24 leaf4840Box leaf4840Inputs = true := by
  rfl'

private theorem leaf4840CoversExact : CoversExact 8
    leaf4840Box leaf4840Certificate leaf4840InnerLog leaf4840Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4840RoundedFacts (by rfl)

private theorem leaf4840FlatSound : Sound leaf4840Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4840CertificateValid
    leaf4840InnerLogValid leaf4840CoversExact leaf4840LowerChecked

private noncomputable def leaf4841Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4841Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084162048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2103085103/1073741824) }, upper := { exponent := 0, mantissa := (32397/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168686863/16168324096) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4841InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4841LocalValidity :
    LeafFacts leaf4841Box leaf4841Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4841Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084162048) }) = true
      norm_num [leaf4841Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4841CertificateValid :
    WideCertificateValid leaf4841Box leaf4841Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi275ValidityFacts
    leaf4841LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4841CoverageChecked :
    coverageCheck (innerAD leaf4841Box) leaf4841InnerLog = true := by
  rfl'

private theorem leaf4841InnerLogValid :
    leaf4841InnerLog.Valid 8 (innerAD leaf4841Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4841CoverageChecked

private noncomputable def leaf4841InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4841InputLogOnePlusV_eq :
    leaf4841InputLogOnePlusV = outerEnclosure 24
      (leaf4841Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4841RoundedFacts : LeafRoundedFacts 8
    leaf4841Certificate.logOnePlusV leaf4841InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4841InputLogOnePlusV_eq }

private noncomputable def leaf4841Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4841InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4841LowerChecked :
    lowerCheck 24 leaf4841Box leaf4841Inputs = true := by
  rfl'

private theorem leaf4841CoversExact : CoversExact 8
    leaf4841Box leaf4841Certificate leaf4841InnerLog leaf4841Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4841RoundedFacts (by rfl)

private theorem leaf4841FlatSound : Sound leaf4841Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4841CertificateValid
    leaf4841InnerLogValid leaf4841CoversExact leaf4841LowerChecked

private noncomputable def leaf4842Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4842Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430720512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2107410213/1073741824) }, upper := { exponent := 0, mantissa := (2029/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867642367/274861441024) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4842InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4842LocalValidity :
    LeafFacts leaf4842Box leaf4842Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4842Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430720512) }) = true
      norm_num [leaf4842Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4842CertificateValid :
    WideCertificateValid leaf4842Box leaf4842Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi275ValidityFacts
    leaf4842LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4842CoverageChecked :
    coverageCheck (innerAD leaf4842Box) leaf4842InnerLog = true := by
  rfl'

private theorem leaf4842InnerLogValid :
    leaf4842InnerLog.Valid 8 (innerAD leaf4842Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4842CoverageChecked

private noncomputable def leaf4842InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4842InputLogOnePlusV_eq :
    leaf4842InputLogOnePlusV = outerEnclosure 24
      (leaf4842Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4842RoundedFacts : LeafRoundedFacts 8
    leaf4842Certificate.logOnePlusV leaf4842InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4842InputLogOnePlusV_eq }

private noncomputable def leaf4842Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4842InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4842LowerChecked :
    lowerCheck 24 leaf4842Box leaf4842Inputs = true := by
  rfl'

private theorem leaf4842CoversExact : CoversExact 8
    leaf4842Box leaf4842Certificate leaf4842InnerLog leaf4842Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4842RoundedFacts (by rfl)

private theorem leaf4842FlatSound : Sound leaf4842Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4842CertificateValid
    leaf4842InnerLogValid leaf4842CoversExact leaf4842LowerChecked

private noncomputable def leaf4843Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4843Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090023424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2118681717/1073741824) }, upper := { exponent := 0, mantissa := (8159/4096) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180279789/10180046848) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4843InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4843LocalValidity :
    LeafFacts leaf4843Box leaf4843Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4843Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090023424) }) = true
      norm_num [leaf4843Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4843CertificateValid :
    WideCertificateValid leaf4843Box leaf4843Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi276ValidityFacts
    leaf4843LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4843CoverageChecked :
    coverageCheck (innerAD leaf4843Box) leaf4843InnerLog = true := by
  rfl'

private theorem leaf4843InnerLogValid :
    leaf4843InnerLog.Valid 8 (innerAD leaf4843Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4843CoverageChecked

private noncomputable def leaf4843InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4843InputLogOnePlusV_eq :
    leaf4843InputLogOnePlusV = outerEnclosure 24
      (leaf4843Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4843RoundedFacts : LeafRoundedFacts 8
    leaf4843Certificate.logOnePlusV leaf4843InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4843InputLogOnePlusV_eq }

private noncomputable def leaf4843Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4843InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4843LowerChecked :
    lowerCheck 24 leaf4843Box leaf4843Inputs = true := by
  rfl'

private theorem leaf4843CoversExact : CoversExact 8
    leaf4843Box leaf4843Certificate leaf4843InnerLog leaf4843Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4843RoundedFacts (by rfl)

private theorem leaf4843FlatSound : Sound leaf4843Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4843CertificateValid
    leaf4843InnerLogValid leaf4843CoversExact leaf4843LowerChecked

private noncomputable def leaf4844Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4844Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715298816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2123072359/1073741824) }, upper := { exponent := 0, mantissa := (511/256) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432711167/137430597632) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4844InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4844LocalValidity :
    LeafFacts leaf4844Box leaf4844Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4844Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715298816) }) = true
      norm_num [leaf4844Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4844CertificateValid :
    WideCertificateValid leaf4844Box leaf4844Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi276ValidityFacts
    leaf4844LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4844CoverageChecked :
    coverageCheck (innerAD leaf4844Box) leaf4844InnerLog = true := by
  rfl'

private theorem leaf4844InnerLogValid :
    leaf4844InnerLog.Valid 8 (innerAD leaf4844Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4844CoverageChecked

private noncomputable def leaf4844InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4844InputLogOnePlusV_eq :
    leaf4844InputLogOnePlusV = outerEnclosure 24
      (leaf4844Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4844RoundedFacts : LeafRoundedFacts 8
    leaf4844Certificate.logOnePlusV leaf4844InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4844InputLogOnePlusV_eq }

private noncomputable def leaf4844Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4844InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4844LowerChecked :
    lowerCheck 24 leaf4844Box leaf4844Inputs = true := by
  rfl'

private theorem leaf4844CoversExact : CoversExact 8
    leaf4844Box leaf4844Certificate leaf4844InnerLog leaf4844Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4844RoundedFacts (by rfl)

private theorem leaf4844FlatSound : Sound leaf4844Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4844CertificateValid
    leaf4844InnerLogValid leaf4844CoversExact leaf4844LowerChecked

private noncomputable def leaf4845Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4845Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430722048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2107541287/1073741824) }, upper := { exponent := 0, mantissa := (32461/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867643903/274861444096) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4845InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4845LocalValidity :
    LeafFacts leaf4845Box leaf4845Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4845Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430722048) }) = true
      norm_num [leaf4845Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4845CertificateValid :
    WideCertificateValid leaf4845Box leaf4845Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi257ValidityFacts
    leaf4845LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4845CoverageChecked :
    coverageCheck (innerAD leaf4845Box) leaf4845InnerLog = true := by
  rfl'

private theorem leaf4845InnerLogValid :
    leaf4845InnerLog.Valid 8 (innerAD leaf4845Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4845CoverageChecked

private noncomputable def leaf4845InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4845InputLogOnePlusV_eq :
    leaf4845InputLogOnePlusV = outerEnclosure 24
      (leaf4845Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4845RoundedFacts : LeafRoundedFacts 8
    leaf4845Certificate.logOnePlusV leaf4845InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4845InputLogOnePlusV_eq }

private noncomputable def leaf4845Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4845InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4845LowerChecked :
    lowerCheck 24 leaf4845Box leaf4845Inputs = true := by
  rfl'

private theorem leaf4845CoversExact : CoversExact 8
    leaf4845Box leaf4845Certificate leaf4845InnerLog leaf4845Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4845RoundedFacts (by rfl)

private theorem leaf4845FlatSound : Sound leaf4845Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4845CertificateValid
    leaf4845InnerLogValid leaf4845CoversExact leaf4845LowerChecked

private noncomputable def leaf4846Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4846Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486137344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2111997461/1073741824) }, upper := { exponent := 0, mantissa := (16265/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973521715/54972274688) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4846InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4846LocalValidity :
    LeafFacts leaf4846Box leaf4846Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4846Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486137344) }) = true
      norm_num [leaf4846Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4846CertificateValid :
    WideCertificateValid leaf4846Box leaf4846Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi257ValidityFacts
    leaf4846LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4846CoverageChecked :
    coverageCheck (innerAD leaf4846Box) leaf4846InnerLog = true := by
  rfl'

private theorem leaf4846InnerLogValid :
    leaf4846InnerLog.Valid 8 (innerAD leaf4846Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4846CoverageChecked

private noncomputable def leaf4846InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4846InputLogOnePlusV_eq :
    leaf4846InputLogOnePlusV = outerEnclosure 24
      (leaf4846Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4846RoundedFacts : LeafRoundedFacts 8
    leaf4846Certificate.logOnePlusV leaf4846InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4846InputLogOnePlusV_eq }

private noncomputable def leaf4846Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4846InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4846LowerChecked :
    lowerCheck 24 leaf4846Box leaf4846Inputs = true := by
  rfl'

private theorem leaf4846CoversExact : CoversExact 8
    leaf4846Box leaf4846Certificate leaf4846InnerLog leaf4846Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4846RoundedFacts (by rfl)

private theorem leaf4846FlatSound : Sound leaf4846Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4846CertificateValid
    leaf4846InnerLogValid leaf4846CoversExact leaf4846LowerChecked

private noncomputable def leaf4847Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4847Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715301376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2122744709/1073741824) }, upper := { exponent := 0, mantissa := (16347/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432713727/137430602752) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4847InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4847LocalValidity :
    LeafFacts leaf4847Box leaf4847Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4847Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715301376) }) = true
      norm_num [leaf4847Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4847CertificateValid :
    WideCertificateValid leaf4847Box leaf4847Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi258ValidityFacts
    leaf4847LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4847CoverageChecked :
    coverageCheck (innerAD leaf4847Box) leaf4847InnerLog = true := by
  rfl'

private theorem leaf4847InnerLogValid :
    leaf4847InnerLog.Valid 8 (innerAD leaf4847Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4847CoverageChecked

private noncomputable def leaf4847InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4847InputLogOnePlusV_eq :
    leaf4847InputLogOnePlusV = outerEnclosure 24
      (leaf4847Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4847RoundedFacts : LeafRoundedFacts 8
    leaf4847Certificate.logOnePlusV leaf4847InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4847InputLogOnePlusV_eq }

private noncomputable def leaf4847Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4847InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4847LowerChecked :
    lowerCheck 24 leaf4847Box leaf4847Inputs = true := by
  rfl'

private theorem leaf4847CoversExact : CoversExact 8
    leaf4847Box leaf4847Certificate leaf4847InnerLog leaf4847Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4847RoundedFacts (by rfl)

private theorem leaf4847FlatSound : Sound leaf4847Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4847CertificateValid
    leaf4847InnerLogValid leaf4847CoversExact leaf4847LowerChecked

private noncomputable def leaf4848Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4848Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715283456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2127266415/1073741824) }, upper := { exponent := 0, mantissa := (8191/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432695807/137430566912) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4848InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4848LocalValidity :
    LeafFacts leaf4848Box leaf4848Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4848Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715283456) }) = true
      norm_num [leaf4848Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4848CertificateValid :
    WideCertificateValid leaf4848Box leaf4848Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi258ValidityFacts
    leaf4848LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4848CoverageChecked :
    coverageCheck (innerAD leaf4848Box) leaf4848InnerLog = true := by
  rfl'

private theorem leaf4848InnerLogValid :
    leaf4848InnerLog.Valid 8 (innerAD leaf4848Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4848CoverageChecked

private noncomputable def leaf4848InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4848InputLogOnePlusV_eq :
    leaf4848InputLogOnePlusV = outerEnclosure 24
      (leaf4848Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4848RoundedFacts : LeafRoundedFacts 8
    leaf4848Certificate.logOnePlusV leaf4848InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4848InputLogOnePlusV_eq }

private noncomputable def leaf4848Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4848InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4848LowerChecked :
    lowerCheck 24 leaf4848Box leaf4848Inputs = true := by
  rfl'

private theorem leaf4848CoversExact : CoversExact 8
    leaf4848Box leaf4848Certificate leaf4848InnerLog leaf4848Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4848RoundedFacts (by rfl)

private theorem leaf4848FlatSound : Sound leaf4848Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4848CertificateValid
    leaf4848InnerLogValid leaf4848CoversExact leaf4848LowerChecked

private noncomputable def leaf4849Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4849Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430651392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2116453635/1073741824) }, upper := { exponent := 0, mantissa := (32599/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867573247/274861302784) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4849InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4849LocalValidity :
    LeafFacts leaf4849Box leaf4849Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4849Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430651392) }) = true
      norm_num [leaf4849Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4849CertificateValid :
    WideCertificateValid leaf4849Box leaf4849Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi257ValidityFacts
    leaf4849LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4849CoverageChecked :
    coverageCheck (innerAD leaf4849Box) leaf4849InnerLog = true := by
  rfl'

private theorem leaf4849InnerLogValid :
    leaf4849InnerLog.Valid 8 (innerAD leaf4849Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4849CoverageChecked

private noncomputable def leaf4849InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4849InputLogOnePlusV_eq :
    leaf4849InputLogOnePlusV = outerEnclosure 24
      (leaf4849Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4849RoundedFacts : LeafRoundedFacts 8
    leaf4849Certificate.logOnePlusV leaf4849InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4849InputLogOnePlusV_eq }

private noncomputable def leaf4849Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4849InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4849LowerChecked :
    lowerCheck 24 leaf4849Box leaf4849Inputs = true := by
  rfl'

private theorem leaf4849CoversExact : CoversExact 8
    leaf4849Box leaf4849Certificate leaf4849InnerLog leaf4849Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4849RoundedFacts (by rfl)

private theorem leaf4849FlatSound : Sound leaf4849Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4849CertificateValid
    leaf4849InnerLogValid leaf4849CoversExact leaf4849LowerChecked

private noncomputable def leaf4850Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4850Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816472576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2120909809/1073741824) }, upper := { exponent := 0, mantissa := (8167/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633245769/19632945152) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4850InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4850LocalValidity :
    LeafFacts leaf4850Box leaf4850Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4850Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816472576) }) = true
      norm_num [leaf4850Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4850CertificateValid :
    WideCertificateValid leaf4850Box leaf4850Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi257ValidityFacts
    leaf4850LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4850CoverageChecked :
    coverageCheck (innerAD leaf4850Box) leaf4850InnerLog = true := by
  rfl'

private theorem leaf4850InnerLogValid :
    leaf4850InnerLog.Valid 8 (innerAD leaf4850Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4850CoverageChecked

private noncomputable def leaf4850InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4850InputLogOnePlusV_eq :
    leaf4850InputLogOnePlusV = outerEnclosure 24
      (leaf4850Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4850RoundedFacts : LeafRoundedFacts 8
    leaf4850Certificate.logOnePlusV leaf4850InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4850InputLogOnePlusV_eq }

private noncomputable def leaf4850Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4850InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4850LowerChecked :
    lowerCheck 24 leaf4850Box leaf4850Inputs = true := by
  rfl'

private theorem leaf4850CoversExact : CoversExact 8
    leaf4850Box leaf4850Certificate leaf4850InnerLog leaf4850Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4850RoundedFacts (by rfl)

private theorem leaf4850FlatSound : Sound leaf4850Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4850CertificateValid
    leaf4850InnerLogValid leaf4850CoversExact leaf4850LowerChecked

private noncomputable def leaf4851Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4851Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635029504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2131788121/1073741824) }, upper := { exponent := 1, mantissa := (16417/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270297543/15270059008) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4851InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4851LocalValidity :
    LeafFacts leaf4851Box leaf4851Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4851Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635029504) }) = true
      norm_num [leaf4851Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4851CertificateValid :
    WideCertificateValid leaf4851Box leaf4851Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi258ValidityFacts
    leaf4851LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4851CoverageChecked :
    coverageCheck (innerAD leaf4851Box) leaf4851InnerLog = true := by
  rfl'

private theorem leaf4851InnerLogValid :
    leaf4851InnerLog.Valid 8 (innerAD leaf4851Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4851CoverageChecked

private noncomputable def leaf4851InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4851InputLogOnePlusV_eq :
    leaf4851InputLogOnePlusV = outerEnclosure 24
      (leaf4851Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4851RoundedFacts : LeafRoundedFacts 8
    leaf4851Certificate.logOnePlusV leaf4851InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4851InputLogOnePlusV_eq }

private noncomputable def leaf4851Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi258InputQChi innerPair533Input
    leaf4851InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4851LowerChecked :
    lowerCheck 24 leaf4851Box leaf4851Inputs = true := by
  rfl'

private theorem leaf4851CoversExact : CoversExact 8
    leaf4851Box leaf4851Certificate leaf4851InnerLog leaf4851Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi258RoundedFacts
    innerPair533RoundedFacts leaf4851RoundedFacts (by rfl)

private theorem leaf4851FlatSound : Sound leaf4851Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4851CertificateValid
    leaf4851InnerLogValid leaf4851CoversExact leaf4851LowerChecked

private noncomputable def leaf4852Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4852Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715247616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2136309827/1073741824) }, upper := { exponent := 1, mantissa := (4113/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432659967/137430495232) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4852InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4852LocalValidity :
    LeafFacts leaf4852Box leaf4852Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4852Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715247616) }) = true
      norm_num [leaf4852Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4852CertificateValid :
    WideCertificateValid leaf4852Box leaf4852Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi258ValidityFacts
    leaf4852LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4852CoverageChecked :
    coverageCheck (innerAD leaf4852Box) leaf4852InnerLog = true := by
  rfl'

private theorem leaf4852InnerLogValid :
    leaf4852InnerLog.Valid 8 (innerAD leaf4852Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4852CoverageChecked

private noncomputable def leaf4852InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4852InputLogOnePlusV_eq :
    leaf4852InputLogOnePlusV = outerEnclosure 24
      (leaf4852Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4852RoundedFacts : LeafRoundedFacts 8
    leaf4852Certificate.logOnePlusV leaf4852InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4852InputLogOnePlusV_eq }

private noncomputable def leaf4852Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi258InputQChi innerPair533Input
    leaf4852InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4852LowerChecked :
    lowerCheck 24 leaf4852Box leaf4852Inputs = true := by
  rfl'

private theorem leaf4852CoversExact : CoversExact 8
    leaf4852Box leaf4852Certificate leaf4852InnerLog leaf4852Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi258RoundedFacts
    innerPair533RoundedFacts leaf4852RoundedFacts (by rfl)

private theorem leaf4852FlatSound : Sound leaf4852Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4852CertificateValid
    leaf4852InnerLogValid leaf4852CoversExact leaf4852LowerChecked

private noncomputable def leaf4853Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4853Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3272257731/3272154368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2137948131/1073741824) }, upper := { exponent := 1, mantissa := (32927/32768) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6544412099/6544308736) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4853InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4853LocalValidity :
    LeafFacts leaf4853Box leaf4853Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4853Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3272257731/3272154368) }) = true
      norm_num [leaf4853Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4853CertificateValid :
    WideCertificateValid leaf4853Box leaf4853Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi279ValidityFacts
    leaf4853LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4853CoverageChecked :
    coverageCheck (innerAD leaf4853Box) leaf4853InnerLog = true := by
  rfl'

private theorem leaf4853InnerLogValid :
    leaf4853InnerLog.Valid 8 (innerAD leaf4853Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4853CoverageChecked

private noncomputable def leaf4853InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4853InputLogOnePlusV_eq :
    leaf4853InputLogOnePlusV = outerEnclosure 24
      (leaf4853Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4853RoundedFacts : LeafRoundedFacts 8
    leaf4853Certificate.logOnePlusV leaf4853InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4853InputLogOnePlusV_eq }

private noncomputable def leaf4853Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi279InputQChi innerPair110Input
    leaf4853InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4853LowerChecked :
    lowerCheck 24 leaf4853Box leaf4853Inputs = true := by
  rfl'

private theorem leaf4853CoversExact : CoversExact 8
    leaf4853Box leaf4853Certificate leaf4853InnerLog leaf4853Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi279RoundedFacts
    innerPair110RoundedFacts leaf4853RoundedFacts (by rfl)

private theorem leaf4853FlatSound : Sound leaf4853Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4853CertificateValid
    leaf4853InnerLogValid leaf4853CoversExact leaf4853LowerChecked

private noncomputable def leaf4854Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4854Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715223552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2142535369/1073741824) }, upper := { exponent := 1, mantissa := (16499/16384) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432635903/137430447104) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4854InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4854LocalValidity :
    LeafFacts leaf4854Box leaf4854Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4854Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715223552) }) = true
      norm_num [leaf4854Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4854CertificateValid :
    WideCertificateValid leaf4854Box leaf4854Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi279ValidityFacts
    leaf4854LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4854CoverageChecked :
    coverageCheck (innerAD leaf4854Box) leaf4854InnerLog = true := by
  rfl'

private theorem leaf4854InnerLogValid :
    leaf4854InnerLog.Valid 8 (innerAD leaf4854Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4854CoverageChecked

private noncomputable def leaf4854InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4854InputLogOnePlusV_eq :
    leaf4854InputLogOnePlusV = outerEnclosure 24
      (leaf4854Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4854RoundedFacts : LeafRoundedFacts 8
    leaf4854Certificate.logOnePlusV leaf4854InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4854InputLogOnePlusV_eq }

private noncomputable def leaf4854Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi279InputQChi innerPair110Input
    leaf4854InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4854LowerChecked :
    lowerCheck 24 leaf4854Box leaf4854Inputs = true := by
  rfl'

private theorem leaf4854CoversExact : CoversExact 8
    leaf4854Box leaf4854Certificate leaf4854InnerLog leaf4854Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi279RoundedFacts
    innerPair110RoundedFacts leaf4854RoundedFacts (by rfl)

private theorem leaf4854FlatSound : Sound leaf4854Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4854CertificateValid
    leaf4854InnerLogValid leaf4854CoversExact leaf4854LowerChecked

private noncomputable def leaf4855Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4855Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715182080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2153151553/2147483648) }, upper := { exponent := 1, mantissa := (4145/4096) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432594431/137430364160) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf4855InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4855LocalValidity :
    LeafFacts leaf4855Box leaf4855Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4855Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715182080) }) = true
      norm_num [leaf4855Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4855CertificateValid :
    WideCertificateValid leaf4855Box leaf4855Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi280ValidityFacts
    leaf4855LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4855CoverageChecked :
    coverageCheck (innerAD leaf4855Box) leaf4855InnerLog = true := by
  rfl'

private theorem leaf4855InnerLogValid :
    leaf4855InnerLog.Valid 8 (innerAD leaf4855Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4855CoverageChecked

private noncomputable def leaf4855InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4855InputLogOnePlusV_eq :
    leaf4855InputLogOnePlusV = outerEnclosure 24
      (leaf4855Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4855RoundedFacts : LeafRoundedFacts 8
    leaf4855Certificate.logOnePlusV leaf4855InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4855InputLogOnePlusV_eq }

private noncomputable def leaf4855Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4855InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4855LowerChecked :
    lowerCheck 24 leaf4855Box leaf4855Inputs = true := by
  rfl'

private theorem leaf4855CoversExact : CoversExact 8
    leaf4855Box leaf4855Certificate leaf4855InnerLog leaf4855Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4855RoundedFacts (by rfl)

private theorem leaf4855FlatSound : Sound leaf4855Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4855CertificateValid
    leaf4855InnerLogValid leaf4855CoversExact leaf4855LowerChecked

private noncomputable def leaf4856Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4856Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715163648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2157804323/2147483648) }, upper := { exponent := 1, mantissa := (2077/2048) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432575999/137430327296) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf4856InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4856LocalValidity :
    LeafFacts leaf4856Box leaf4856Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4856Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715163648) }) = true
      norm_num [leaf4856Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4856CertificateValid :
    WideCertificateValid leaf4856Box leaf4856Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi280ValidityFacts
    leaf4856LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4856CoverageChecked :
    coverageCheck (innerAD leaf4856Box) leaf4856InnerLog = true := by
  rfl'

private theorem leaf4856InnerLogValid :
    leaf4856InnerLog.Valid 8 (innerAD leaf4856Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4856CoverageChecked

private noncomputable def leaf4856InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4856InputLogOnePlusV_eq :
    leaf4856InputLogOnePlusV = outerEnclosure 24
      (leaf4856Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4856RoundedFacts : LeafRoundedFacts 8
    leaf4856Certificate.logOnePlusV leaf4856InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4856InputLogOnePlusV_eq }

private noncomputable def leaf4856Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4856InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4856LowerChecked :
    lowerCheck 24 leaf4856Box leaf4856Inputs = true := by
  rfl'

private theorem leaf4856CoversExact : CoversExact 8
    leaf4856Box leaf4856Certificate leaf4856InnerLog leaf4856Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4856RoundedFacts (by rfl)

private theorem leaf4856FlatSound : Sound leaf4856Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4856CertificateValid
    leaf4856InnerLogValid leaf4856CoversExact leaf4856LowerChecked

private noncomputable def leaf4857Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4857Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1598079357/1598028032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2147122607/1073741824) }, upper := { exponent := 1, mantissa := (33069/32768) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3196107389/3196056064) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4857InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4857LocalValidity :
    LeafFacts leaf4857Box leaf4857Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4857Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1598079357/1598028032) }) = true
      norm_num [leaf4857Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4857CertificateValid :
    WideCertificateValid leaf4857Box leaf4857Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi279ValidityFacts
    leaf4857LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4857CoverageChecked :
    coverageCheck (innerAD leaf4857Box) leaf4857InnerLog = true := by
  rfl'

private theorem leaf4857InnerLogValid :
    leaf4857InnerLog.Valid 8 (innerAD leaf4857Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4857CoverageChecked

private noncomputable def leaf4857InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4857InputLogOnePlusV_eq :
    leaf4857InputLogOnePlusV = outerEnclosure 24
      (leaf4857Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4857RoundedFacts : LeafRoundedFacts 8
    leaf4857Certificate.logOnePlusV leaf4857InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4857InputLogOnePlusV_eq }

private noncomputable def leaf4857Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi279InputQChi innerPair110Input
    leaf4857InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4857LowerChecked :
    lowerCheck 24 leaf4857Box leaf4857Inputs = true := by
  rfl'

private theorem leaf4857CoversExact : CoversExact 8
    leaf4857Box leaf4857Certificate leaf4857InnerLog leaf4857Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi279RoundedFacts
    innerPair110RoundedFacts leaf4857RoundedFacts (by rfl)

private theorem leaf4857FlatSound : Sound leaf4857Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4857CertificateValid
    leaf4857InnerLogValid leaf4857CoversExact leaf4857LowerChecked

private noncomputable def leaf4858Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4858Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635020800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2151709845/2147483648) }, upper := { exponent := 1, mantissa := (8285/8192) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270288839/15270041600) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4858InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4858LocalValidity :
    LeafFacts leaf4858Box leaf4858Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4858Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635020800) }) = true
      norm_num [leaf4858Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4858CertificateValid :
    WideCertificateValid leaf4858Box leaf4858Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi279ValidityFacts
    leaf4858LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4858CoverageChecked :
    coverageCheck (innerAD leaf4858Box) leaf4858InnerLog = true := by
  rfl'

private theorem leaf4858InnerLogValid :
    leaf4858InnerLog.Valid 8 (innerAD leaf4858Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4858CoverageChecked

private noncomputable def leaf4858InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4858InputLogOnePlusV_eq :
    leaf4858InputLogOnePlusV = outerEnclosure 24
      (leaf4858Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4858RoundedFacts : LeafRoundedFacts 8
    leaf4858Certificate.logOnePlusV leaf4858InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4858InputLogOnePlusV_eq }

private noncomputable def leaf4858Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi279InputQChi innerPair116Input
    leaf4858InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4858LowerChecked :
    lowerCheck 24 leaf4858Box leaf4858Inputs = true := by
  rfl'

private theorem leaf4858CoversExact : CoversExact 8
    leaf4858Box leaf4858Certificate leaf4858InnerLog leaf4858Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf4858RoundedFacts (by rfl)

private theorem leaf4858FlatSound : Sound leaf4858Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4858CertificateValid
    leaf4858InnerLogValid leaf4858CoversExact leaf4858LowerChecked

private noncomputable def leaf4859Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4859Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715145216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2162457093/2147483648) }, upper := { exponent := 1, mantissa := (4163/4096) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432557567/137430290432) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf4859InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4859LocalValidity :
    LeafFacts leaf4859Box leaf4859Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4859Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715145216) }) = true
      norm_num [leaf4859Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4859CertificateValid :
    WideCertificateValid leaf4859Box leaf4859Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi280ValidityFacts
    leaf4859LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4859CoverageChecked :
    coverageCheck (innerAD leaf4859Box) leaf4859InnerLog = true := by
  rfl'

private theorem leaf4859InnerLogValid :
    leaf4859InnerLog.Valid 8 (innerAD leaf4859Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4859CoverageChecked

private noncomputable def leaf4859InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4859InputLogOnePlusV_eq :
    leaf4859InputLogOnePlusV = outerEnclosure 24
      (leaf4859Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4859RoundedFacts : LeafRoundedFacts 8
    leaf4859Certificate.logOnePlusV leaf4859InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4859InputLogOnePlusV_eq }

private noncomputable def leaf4859Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4859InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4859LowerChecked :
    lowerCheck 24 leaf4859Box leaf4859Inputs = true := by
  rfl'

private theorem leaf4859CoversExact : CoversExact 8
    leaf4859Box leaf4859Certificate leaf4859InnerLog leaf4859Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4859RoundedFacts (by rfl)

private theorem leaf4859FlatSound : Sound leaf4859Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4859CertificateValid
    leaf4859InnerLogValid leaf4859CoversExact leaf4859LowerChecked

private noncomputable def leaf4860Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4860Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715126784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2167109863/2147483648) }, upper := { exponent := 1, mantissa := (1043/1024) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432539135/137430253568) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf4860InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4860LocalValidity :
    LeafFacts leaf4860Box leaf4860Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4860Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715126784) }) = true
      norm_num [leaf4860Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4860CertificateValid :
    WideCertificateValid leaf4860Box leaf4860Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi280ValidityFacts
    leaf4860LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4860CoverageChecked :
    coverageCheck (innerAD leaf4860Box) leaf4860InnerLog = true := by
  rfl'

private theorem leaf4860InnerLogValid :
    leaf4860InnerLog.Valid 8 (innerAD leaf4860Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4860CoverageChecked

private noncomputable def leaf4860InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4860InputLogOnePlusV_eq :
    leaf4860InputLogOnePlusV = outerEnclosure 24
      (leaf4860Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4860RoundedFacts : LeafRoundedFacts 8
    leaf4860Certificate.logOnePlusV leaf4860InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4860InputLogOnePlusV_eq }

private noncomputable def leaf4860Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4860InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4860LowerChecked :
    lowerCheck 24 leaf4860Box leaf4860Inputs = true := by
  rfl'

private theorem leaf4860CoversExact : CoversExact 8
    leaf4860Box leaf4860Certificate leaf4860InnerLog leaf4860Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4860RoundedFacts (by rfl)

private theorem leaf4860FlatSound : Sound leaf4860Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4860CertificateValid
    leaf4860InnerLogValid leaf4860CoversExact leaf4860LowerChecked

private noncomputable def leaf4861Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4861Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715290368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2125365983/1073741824) }, upper := { exponent := 0, mantissa := (32737/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432702719/137430580736) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4861InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4861LocalValidity :
    LeafFacts leaf4861Box leaf4861Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4861Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715290368) }) = true
      norm_num [leaf4861Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4861CertificateValid :
    WideCertificateValid leaf4861Box leaf4861Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi257ValidityFacts
    leaf4861LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4861CoverageChecked :
    coverageCheck (innerAD leaf4861Box) leaf4861InnerLog = true := by
  rfl'

private theorem leaf4861InnerLogValid :
    leaf4861InnerLog.Valid 8 (innerAD leaf4861Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4861CoverageChecked

private noncomputable def leaf4861InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4861InputLogOnePlusV_eq :
    leaf4861InputLogOnePlusV = outerEnclosure 24
      (leaf4861Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4861RoundedFacts : LeafRoundedFacts 8
    leaf4861Certificate.logOnePlusV leaf4861InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4861InputLogOnePlusV_eq }

private noncomputable def leaf4861Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4861InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4861LowerChecked :
    lowerCheck 24 leaf4861Box leaf4861Inputs = true := by
  rfl'

private theorem leaf4861CoversExact : CoversExact 8
    leaf4861Box leaf4861Certificate leaf4861InnerLog leaf4861Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4861RoundedFacts (by rfl)

private theorem leaf4861FlatSound : Sound leaf4861Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4861CertificateValid
    leaf4861InnerLogValid leaf4861CoversExact leaf4861LowerChecked

private noncomputable def leaf4862Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4862Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715272704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2129822157/1073741824) }, upper := { exponent := 1, mantissa := (16403/16384) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432685055/137430545408) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4862InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4862LocalValidity :
    LeafFacts leaf4862Box leaf4862Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4862Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715272704) }) = true
      norm_num [leaf4862Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4862CertificateValid :
    WideCertificateValid leaf4862Box leaf4862Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi257ValidityFacts
    leaf4862LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4862CoverageChecked :
    coverageCheck (innerAD leaf4862Box) leaf4862InnerLog = true := by
  rfl'

private theorem leaf4862InnerLogValid :
    leaf4862InnerLog.Valid 8 (innerAD leaf4862Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4862CoverageChecked

private noncomputable def leaf4862InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4862InputLogOnePlusV_eq :
    leaf4862InputLogOnePlusV = outerEnclosure 24
      (leaf4862Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4862RoundedFacts : LeafRoundedFacts 8
    leaf4862Certificate.logOnePlusV leaf4862InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4862InputLogOnePlusV_eq }

private noncomputable def leaf4862Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi257InputQChi innerPair321Input
    leaf4862InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4862LowerChecked :
    lowerCheck 24 leaf4862Box leaf4862Inputs = true := by
  rfl'

private theorem leaf4862CoversExact : CoversExact 8
    leaf4862Box leaf4862Certificate leaf4862InnerLog leaf4862Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi257RoundedFacts
    innerPair321RoundedFacts leaf4862RoundedFacts (by rfl)

private theorem leaf4862FlatSound : Sound leaf4862Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4862CertificateValid
    leaf4862InnerLogValid leaf4862CoversExact leaf4862LowerChecked

private noncomputable def leaf4863Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4863Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715229696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2140831533/1073741824) }, upper := { exponent := 1, mantissa := (16487/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432642047/137430459392) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4863InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4863LocalValidity :
    LeafFacts leaf4863Box leaf4863Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4863Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715229696) }) = true
      norm_num [leaf4863Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4863CertificateValid :
    WideCertificateValid leaf4863Box leaf4863Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi258ValidityFacts
    leaf4863LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4863CoverageChecked :
    coverageCheck (innerAD leaf4863Box) leaf4863InnerLog = true := by
  rfl'

private theorem leaf4863InnerLogValid :
    leaf4863InnerLog.Valid 8 (innerAD leaf4863Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4863CoverageChecked

private noncomputable def leaf4863InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4863InputLogOnePlusV_eq :
    leaf4863InputLogOnePlusV = outerEnclosure 24
      (leaf4863Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4863RoundedFacts : LeafRoundedFacts 8
    leaf4863Certificate.logOnePlusV leaf4863InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4863InputLogOnePlusV_eq }

private noncomputable def leaf4863Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi258InputQChi innerPair533Input
    leaf4863InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4863LowerChecked :
    lowerCheck 24 leaf4863Box leaf4863Inputs = true := by
  rfl'

private theorem leaf4863CoversExact : CoversExact 8
    leaf4863Box leaf4863Certificate leaf4863InnerLog leaf4863Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi258RoundedFacts
    innerPair533RoundedFacts leaf4863RoundedFacts (by rfl)

private theorem leaf4863FlatSound : Sound leaf4863Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4863CertificateValid
    leaf4863InnerLogValid leaf4863CoversExact leaf4863LowerChecked

private noncomputable def leaf4864Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4864Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905070592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2145353239/1073741824) }, upper := { exponent := 1, mantissa := (8261/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810874709/45810141184) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4864InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf4864LocalValidity :
    LeafFacts leaf4864Box leaf4864Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4864Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905070592) }) = true
      norm_num [leaf4864Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4864CertificateValid :
    WideCertificateValid leaf4864Box leaf4864Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi258ValidityFacts
    leaf4864LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4864CoverageChecked :
    coverageCheck (innerAD leaf4864Box) leaf4864InnerLog = true := by
  rfl'

private theorem leaf4864InnerLogValid :
    leaf4864InnerLog.Valid 8 (innerAD leaf4864Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf4864CoverageChecked

private noncomputable def leaf4864InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4864InputLogOnePlusV_eq :
    leaf4864InputLogOnePlusV = outerEnclosure 24
      (leaf4864Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4864RoundedFacts : LeafRoundedFacts 8
    leaf4864Certificate.logOnePlusV leaf4864InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4864InputLogOnePlusV_eq }

private noncomputable def leaf4864Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi258InputQChi innerPair531Input
    leaf4864InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4864LowerChecked :
    lowerCheck 24 leaf4864Box leaf4864Inputs = true := by
  rfl'

private theorem leaf4864CoversExact : CoversExact 8
    leaf4864Box leaf4864Certificate leaf4864InnerLog leaf4864Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi258RoundedFacts
    innerPair531RoundedFacts leaf4864RoundedFacts (by rfl)

private theorem leaf4864FlatSound : Sound leaf4864Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4864CertificateValid
    leaf4864InnerLogValid leaf4864CoversExact leaf4864LowerChecked

private noncomputable def leaf4865Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4865Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715255040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2134278331/1073741824) }, upper := { exponent := 1, mantissa := (32875/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432667391/137430510080) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4865InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4865LocalValidity :
    LeafFacts leaf4865Box leaf4865Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4865Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715255040) }) = true
      norm_num [leaf4865Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4865CertificateValid :
    WideCertificateValid leaf4865Box leaf4865Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi257ValidityFacts
    leaf4865LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4865CoverageChecked :
    coverageCheck (innerAD leaf4865Box) leaf4865InnerLog = true := by
  rfl'

private theorem leaf4865InnerLogValid :
    leaf4865InnerLog.Valid 8 (innerAD leaf4865Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4865CoverageChecked

private noncomputable def leaf4865InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4865InputLogOnePlusV_eq :
    leaf4865InputLogOnePlusV = outerEnclosure 24
      (leaf4865Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4865RoundedFacts : LeafRoundedFacts 8
    leaf4865Certificate.logOnePlusV leaf4865InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4865InputLogOnePlusV_eq }

private noncomputable def leaf4865Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi257InputQChi innerPair533Input
    leaf4865InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4865LowerChecked :
    lowerCheck 24 leaf4865Box leaf4865Inputs = true := by
  rfl'

private theorem leaf4865CoversExact : CoversExact 8
    leaf4865Box leaf4865Certificate leaf4865InnerLog leaf4865Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi257RoundedFacts
    innerPair533RoundedFacts leaf4865RoundedFacts (by rfl)

private theorem leaf4865FlatSound : Sound leaf4865Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4865CertificateValid
    leaf4865InnerLogValid leaf4865CoversExact leaf4865LowerChecked

private noncomputable def leaf4866Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4866Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715237376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2138734505/1073741824) }, upper := { exponent := 1, mantissa := (2059/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432649727/137430474752) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4866InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf4866LocalValidity :
    LeafFacts leaf4866Box leaf4866Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4866Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715237376) }) = true
      norm_num [leaf4866Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4866CertificateValid :
    WideCertificateValid leaf4866Box leaf4866Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi257ValidityFacts
    leaf4866LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4866CoverageChecked :
    coverageCheck (innerAD leaf4866Box) leaf4866InnerLog = true := by
  rfl'

private theorem leaf4866InnerLogValid :
    leaf4866InnerLog.Valid 8 (innerAD leaf4866Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf4866CoverageChecked

private noncomputable def leaf4866InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4866InputLogOnePlusV_eq :
    leaf4866InputLogOnePlusV = outerEnclosure 24
      (leaf4866Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4866RoundedFacts : LeafRoundedFacts 8
    leaf4866Certificate.logOnePlusV leaf4866InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4866InputLogOnePlusV_eq }

private noncomputable def leaf4866Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi257InputQChi innerPair533Input
    leaf4866InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4866LowerChecked :
    lowerCheck 24 leaf4866Box leaf4866Inputs = true := by
  rfl'

private theorem leaf4866CoversExact : CoversExact 8
    leaf4866Box leaf4866Certificate leaf4866InnerLog leaf4866Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi257RoundedFacts
    innerPair533RoundedFacts leaf4866RoundedFacts (by rfl)

private theorem leaf4866FlatSound : Sound leaf4866Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4866CertificateValid
    leaf4866InnerLogValid leaf4866CoversExact leaf4866LowerChecked

private noncomputable def leaf4867Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4867Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715193856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2149874945/2147483648) }, upper := { exponent := 1, mantissa := (16557/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432606207/137430387712) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4867InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4867LocalValidity :
    LeafFacts leaf4867Box leaf4867Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4867Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715193856) }) = true
      norm_num [leaf4867Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4867CertificateValid :
    WideCertificateValid leaf4867Box leaf4867Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi258ValidityFacts
    leaf4867LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4867CoverageChecked :
    coverageCheck (innerAD leaf4867Box) leaf4867InnerLog = true := by
  rfl'

private theorem leaf4867InnerLogValid :
    leaf4867InnerLog.Valid 8 (innerAD leaf4867Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4867CoverageChecked

private noncomputable def leaf4867InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4867InputLogOnePlusV_eq :
    leaf4867InputLogOnePlusV = outerEnclosure 24
      (leaf4867Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4867RoundedFacts : LeafRoundedFacts 8
    leaf4867Certificate.logOnePlusV leaf4867InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4867InputLogOnePlusV_eq }

private noncomputable def leaf4867Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi258InputQChi innerPair116Input
    leaf4867InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4867LowerChecked :
    lowerCheck 24 leaf4867Box leaf4867Inputs = true := by
  rfl'

private theorem leaf4867CoversExact : CoversExact 8
    leaf4867Box leaf4867Certificate leaf4867InnerLog leaf4867Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf4867RoundedFacts (by rfl)

private theorem leaf4867FlatSound : Sound leaf4867Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4867CertificateValid
    leaf4867InnerLogValid leaf4867CoversExact leaf4867LowerChecked

private noncomputable def leaf4868Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4868Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715175936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2154396651/2147483648) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432588287/137430351872) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4868InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4868LocalValidity :
    LeafFacts leaf4868Box leaf4868Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4868Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715175936) }) = true
      norm_num [leaf4868Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4868CertificateValid :
    WideCertificateValid leaf4868Box leaf4868Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi258ValidityFacts
    leaf4868LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4868CoverageChecked :
    coverageCheck (innerAD leaf4868Box) leaf4868InnerLog = true := by
  rfl'

private theorem leaf4868InnerLogValid :
    leaf4868InnerLog.Valid 8 (innerAD leaf4868Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4868CoverageChecked

private noncomputable def leaf4868InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4868InputLogOnePlusV_eq :
    leaf4868InputLogOnePlusV = outerEnclosure 24
      (leaf4868Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4868RoundedFacts : LeafRoundedFacts 8
    leaf4868Certificate.logOnePlusV leaf4868InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4868InputLogOnePlusV_eq }

private noncomputable def leaf4868Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi258InputQChi innerPair116Input
    leaf4868InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4868LowerChecked :
    lowerCheck 24 leaf4868Box leaf4868Inputs = true := by
  rfl'

private theorem leaf4868CoversExact : CoversExact 8
    leaf4868Box leaf4868Certificate leaf4868InnerLog leaf4868Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf4868RoundedFacts (by rfl)

private theorem leaf4868FlatSound : Sound leaf4868Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4868CertificateValid
    leaf4868InnerLogValid leaf4868CoversExact leaf4868LowerChecked

private noncomputable def leaf4869Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4869Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715169024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2156297083/2147483648) }, upper := { exponent := 1, mantissa := (33211/32768) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432581375/137430338048) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4869InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4869LocalValidity :
    LeafFacts leaf4869Box leaf4869Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4869Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715169024) }) = true
      norm_num [leaf4869Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4869CertificateValid :
    WideCertificateValid leaf4869Box leaf4869Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi279ValidityFacts
    leaf4869LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4869CoverageChecked :
    coverageCheck (innerAD leaf4869Box) leaf4869InnerLog = true := by
  rfl'

private theorem leaf4869InnerLogValid :
    leaf4869InnerLog.Valid 8 (innerAD leaf4869Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4869CoverageChecked

private noncomputable def leaf4869InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4869InputLogOnePlusV_eq :
    leaf4869InputLogOnePlusV = outerEnclosure 24
      (leaf4869Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4869RoundedFacts : LeafRoundedFacts 8
    leaf4869Certificate.logOnePlusV leaf4869InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4869InputLogOnePlusV_eq }

private noncomputable def leaf4869Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi279InputQChi innerPair116Input
    leaf4869InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4869LowerChecked :
    lowerCheck 24 leaf4869Box leaf4869Inputs = true := by
  rfl'

private theorem leaf4869CoversExact : CoversExact 8
    leaf4869Box leaf4869Certificate leaf4869InnerLog leaf4869Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf4869RoundedFacts (by rfl)

private theorem leaf4869FlatSound : Sound leaf4869Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4869CertificateValid
    leaf4869InnerLogValid leaf4869CoversExact leaf4869LowerChecked

private noncomputable def leaf4870Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4870Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715150848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2160884321/2147483648) }, upper := { exponent := 1, mantissa := (16641/16384) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432563199/137430301696) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4870InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4870LocalValidity :
    LeafFacts leaf4870Box leaf4870Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4870Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715150848) }) = true
      norm_num [leaf4870Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4870CertificateValid :
    WideCertificateValid leaf4870Box leaf4870Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi279ValidityFacts
    leaf4870LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4870CoverageChecked :
    coverageCheck (innerAD leaf4870Box) leaf4870InnerLog = true := by
  rfl'

private theorem leaf4870InnerLogValid :
    leaf4870InnerLog.Valid 8 (innerAD leaf4870Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4870CoverageChecked

private noncomputable def leaf4870InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4870InputLogOnePlusV_eq :
    leaf4870InputLogOnePlusV = outerEnclosure 24
      (leaf4870Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4870RoundedFacts : LeafRoundedFacts 8
    leaf4870Certificate.logOnePlusV leaf4870InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4870InputLogOnePlusV_eq }

private noncomputable def leaf4870Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi279InputQChi innerPair116Input
    leaf4870InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4870LowerChecked :
    lowerCheck 24 leaf4870Box leaf4870Inputs = true := by
  rfl'

private theorem leaf4870CoversExact : CoversExact 8
    leaf4870Box leaf4870Certificate leaf4870InnerLog leaf4870Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf4870RoundedFacts (by rfl)

private theorem leaf4870FlatSound : Sound leaf4870Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4870CertificateValid
    leaf4870InnerLogValid leaf4870CoversExact leaf4870LowerChecked

private noncomputable def leaf4871Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4871Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715108352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2171762633/2147483648) }, upper := { exponent := 1, mantissa := (4181/4096) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432520703/137430216704) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf4871InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4871LocalValidity :
    LeafFacts leaf4871Box leaf4871Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4871Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715108352) }) = true
      norm_num [leaf4871Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4871CertificateValid :
    WideCertificateValid leaf4871Box leaf4871Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi280ValidityFacts
    leaf4871LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4871CoverageChecked :
    coverageCheck (innerAD leaf4871Box) leaf4871InnerLog = true := by
  rfl'

private theorem leaf4871InnerLogValid :
    leaf4871InnerLog.Valid 8 (innerAD leaf4871Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4871CoverageChecked

private noncomputable def leaf4871InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4871InputLogOnePlusV_eq :
    leaf4871InputLogOnePlusV = outerEnclosure 24
      (leaf4871Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4871RoundedFacts : LeafRoundedFacts 8
    leaf4871Certificate.logOnePlusV leaf4871InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4871InputLogOnePlusV_eq }

private noncomputable def leaf4871Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4871InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4871LowerChecked :
    lowerCheck 24 leaf4871Box leaf4871Inputs = true := by
  rfl'

private theorem leaf4871CoversExact : CoversExact 8
    leaf4871Box leaf4871Certificate leaf4871InnerLog leaf4871Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4871RoundedFacts (by rfl)

private theorem leaf4871FlatSound : Sound leaf4871Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4871CertificateValid
    leaf4871InnerLogValid leaf4871CoversExact leaf4871LowerChecked

private noncomputable def leaf4872Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4872Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715089920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2176415403/2147483648) }, upper := { exponent := 1, mantissa := (2095/2048) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432502271/137430179840) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf4872InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4872LocalValidity :
    LeafFacts leaf4872Box leaf4872Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4872Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715089920) }) = true
      norm_num [leaf4872Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4872CertificateValid :
    WideCertificateValid leaf4872Box leaf4872Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi280ValidityFacts
    leaf4872LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4872CoverageChecked :
    coverageCheck (innerAD leaf4872Box) leaf4872InnerLog = true := by
  rfl'

private theorem leaf4872InnerLogValid :
    leaf4872InnerLog.Valid 8 (innerAD leaf4872Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4872CoverageChecked

private noncomputable def leaf4872InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4872InputLogOnePlusV_eq :
    leaf4872InputLogOnePlusV = outerEnclosure 24
      (leaf4872Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4872RoundedFacts : LeafRoundedFacts 8
    leaf4872Certificate.logOnePlusV leaf4872InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4872InputLogOnePlusV_eq }

private noncomputable def leaf4872Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4872InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4872LowerChecked :
    lowerCheck 24 leaf4872Box leaf4872Inputs = true := by
  rfl'

private theorem leaf4872CoversExact : CoversExact 8
    leaf4872Box leaf4872Certificate leaf4872InnerLog leaf4872Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4872RoundedFacts (by rfl)

private theorem leaf4872FlatSound : Sound leaf4872Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4872CertificateValid
    leaf4872InnerLogValid leaf4872CoversExact leaf4872LowerChecked

private noncomputable def leaf4873Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4873Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905044224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2165471559/2147483648) }, upper := { exponent := 1, mantissa := (33353/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810848341/45810088448) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4873InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4873LocalValidity :
    LeafFacts leaf4873Box leaf4873Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4873Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905044224) }) = true
      norm_num [leaf4873Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4873CertificateValid :
    WideCertificateValid leaf4873Box leaf4873Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi279ValidityFacts
    leaf4873LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4873CoverageChecked :
    coverageCheck (innerAD leaf4873Box) leaf4873InnerLog = true := by
  rfl'

private theorem leaf4873InnerLogValid :
    leaf4873InnerLog.Valid 8 (innerAD leaf4873Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4873CoverageChecked

private noncomputable def leaf4873InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4873InputLogOnePlusV_eq :
    leaf4873InputLogOnePlusV = outerEnclosure 24
      (leaf4873Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4873RoundedFacts : LeafRoundedFacts 8
    leaf4873Certificate.logOnePlusV leaf4873InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4873InputLogOnePlusV_eq }

private noncomputable def leaf4873Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi279InputQChi innerPair116Input
    leaf4873InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4873LowerChecked :
    lowerCheck 24 leaf4873Box leaf4873Inputs = true := by
  rfl'

private theorem leaf4873CoversExact : CoversExact 8
    leaf4873Box leaf4873Certificate leaf4873InnerLog leaf4873Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf4873RoundedFacts (by rfl)

private theorem leaf4873FlatSound : Sound leaf4873Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4873CertificateValid
    leaf4873InnerLogValid leaf4873CoversExact leaf4873LowerChecked

private noncomputable def leaf4874Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4874Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816444928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2170058797/2147483648) }, upper := { exponent := 1, mantissa := (2089/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633218121/19632889856) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4874InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4874LocalValidity :
    LeafFacts leaf4874Box leaf4874Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4874Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816444928) }) = true
      norm_num [leaf4874Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4874CertificateValid :
    WideCertificateValid leaf4874Box leaf4874Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi279ValidityFacts
    leaf4874LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4874CoverageChecked :
    coverageCheck (innerAD leaf4874Box) leaf4874InnerLog = true := by
  rfl'

private theorem leaf4874InnerLogValid :
    leaf4874InnerLog.Valid 8 (innerAD leaf4874Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4874CoverageChecked

private noncomputable def leaf4874InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4874InputLogOnePlusV_eq :
    leaf4874InputLogOnePlusV = outerEnclosure 24
      (leaf4874Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4874RoundedFacts : LeafRoundedFacts 8
    leaf4874Certificate.logOnePlusV leaf4874InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4874InputLogOnePlusV_eq }

private noncomputable def leaf4874Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi279InputQChi innerPair116Input
    leaf4874InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4874LowerChecked :
    lowerCheck 24 leaf4874Box leaf4874Inputs = true := by
  rfl'

private theorem leaf4874CoversExact : CoversExact 8
    leaf4874Box leaf4874Certificate leaf4874InnerLog leaf4874Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf4874RoundedFacts (by rfl)

private theorem leaf4874FlatSound : Sound leaf4874Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4874CertificateValid
    leaf4874InnerLogValid leaf4874CoversExact leaf4874LowerChecked

private noncomputable def leaf4875Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4875Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816438784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2181068173/2147483648) }, upper := { exponent := 1, mantissa := (4199/4096) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633211977/19632877568) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf4875InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4875LocalValidity :
    LeafFacts leaf4875Box leaf4875Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4875Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816438784) }) = true
      norm_num [leaf4875Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4875CertificateValid :
    WideCertificateValid leaf4875Box leaf4875Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi280ValidityFacts
    leaf4875LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4875CoverageChecked :
    coverageCheck (innerAD leaf4875Box) leaf4875InnerLog = true := by
  rfl'

private theorem leaf4875InnerLogValid :
    leaf4875InnerLog.Valid 8 (innerAD leaf4875Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4875CoverageChecked

private noncomputable def leaf4875InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4875InputLogOnePlusV_eq :
    leaf4875InputLogOnePlusV = outerEnclosure 24
      (leaf4875Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4875RoundedFacts : LeafRoundedFacts 8
    leaf4875Certificate.logOnePlusV leaf4875InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4875InputLogOnePlusV_eq }

private noncomputable def leaf4875Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4875InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4875LowerChecked :
    lowerCheck 24 leaf4875Box leaf4875Inputs = true := by
  rfl'

private theorem leaf4875CoversExact : CoversExact 8
    leaf4875Box leaf4875Certificate leaf4875InnerLog leaf4875Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4875RoundedFacts (by rfl)

private theorem leaf4875FlatSound : Sound leaf4875Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4875CertificateValid
    leaf4875InnerLogValid leaf4875CoversExact leaf4875LowerChecked

private noncomputable def leaf4876Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4876Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715053056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2185720943/2147483648) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432465407/137430106112) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf4876InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4876LocalValidity :
    LeafFacts leaf4876Box leaf4876Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4876Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715053056) }) = true
      norm_num [leaf4876Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4876CertificateValid :
    WideCertificateValid leaf4876Box leaf4876Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi280ValidityFacts
    leaf4876LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4876CoverageChecked :
    coverageCheck (innerAD leaf4876Box) leaf4876InnerLog = true := by
  rfl'

private theorem leaf4876InnerLogValid :
    leaf4876InnerLog.Valid 8 (innerAD leaf4876Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4876CoverageChecked

private noncomputable def leaf4876InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4876InputLogOnePlusV_eq :
    leaf4876InputLogOnePlusV = outerEnclosure 24
      (leaf4876Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4876RoundedFacts : LeafRoundedFacts 8
    leaf4876Certificate.logOnePlusV leaf4876InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4876InputLogOnePlusV_eq }

private noncomputable def leaf4876Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4876InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4876LowerChecked :
    lowerCheck 24 leaf4876Box leaf4876Inputs = true := by
  rfl'

private theorem leaf4876CoversExact : CoversExact 8
    leaf4876Box leaf4876Certificate leaf4876InnerLog leaf4876Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4876RoundedFacts (by rfl)

private theorem leaf4876FlatSound : Sound leaf4876Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4876CertificateValid
    leaf4876InnerLogValid leaf4876CoversExact leaf4876LowerChecked

private noncomputable def component99Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node0_sound : Sound component99Node0Box :=
  sound_of_literal_split component99Node0Box leaf4813Box leaf4814Box
    .k (233/64) (by rfl) (by rfl)
    leaf4813FlatSound leaf4814FlatSound

private noncomputable def component99Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node1_sound : Sound component99Node1Box :=
  sound_of_literal_split component99Node1Box leaf4815Box leaf4816Box
    .k (233/64) (by rfl) (by rfl)
    leaf4815FlatSound leaf4816FlatSound

private noncomputable def component99Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node2_sound : Sound component99Node2Box :=
  sound_of_literal_split component99Node2Box component99Node0Box component99Node1Box
    .chi (65/256) (by rfl) (by rfl)
    component99Node0_sound component99Node1_sound

private noncomputable def component99Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node3_sound : Sound component99Node3Box :=
  sound_of_literal_split component99Node3Box leaf4817Box leaf4818Box
    .k (235/64) (by rfl) (by rfl)
    leaf4817FlatSound leaf4818FlatSound

private noncomputable def component99Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node4_sound : Sound component99Node4Box :=
  sound_of_literal_split component99Node4Box leaf4819Box leaf4820Box
    .k (235/64) (by rfl) (by rfl)
    leaf4819FlatSound leaf4820FlatSound

private noncomputable def component99Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node5_sound : Sound component99Node5Box :=
  sound_of_literal_split component99Node5Box component99Node3Box component99Node4Box
    .chi (65/256) (by rfl) (by rfl)
    component99Node3_sound component99Node4_sound

private noncomputable def component99Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node6_sound : Sound component99Node6Box :=
  sound_of_literal_split component99Node6Box component99Node2Box component99Node5Box
    .k (117/32) (by rfl) (by rfl)
    component99Node2_sound component99Node5_sound

private noncomputable def component99Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node7_sound : Sound component99Node7Box :=
  sound_of_literal_split component99Node7Box leaf4821Box leaf4822Box
    .k (233/64) (by rfl) (by rfl)
    leaf4821FlatSound leaf4822FlatSound

private noncomputable def component99Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node8_sound : Sound component99Node8Box :=
  sound_of_literal_split component99Node8Box leaf4823Box leaf4824Box
    .k (233/64) (by rfl) (by rfl)
    leaf4823FlatSound leaf4824FlatSound

private noncomputable def component99Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node9_sound : Sound component99Node9Box :=
  sound_of_literal_split component99Node9Box component99Node7Box component99Node8Box
    .chi (67/256) (by rfl) (by rfl)
    component99Node7_sound component99Node8_sound

private noncomputable def component99Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node10_sound : Sound component99Node10Box :=
  sound_of_literal_split component99Node10Box leaf4825Box leaf4826Box
    .k (235/64) (by rfl) (by rfl)
    leaf4825FlatSound leaf4826FlatSound

private noncomputable def component99Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node11_sound : Sound component99Node11Box :=
  sound_of_literal_split component99Node11Box leaf4827Box leaf4828Box
    .k (235/64) (by rfl) (by rfl)
    leaf4827FlatSound leaf4828FlatSound

private noncomputable def component99Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node12_sound : Sound component99Node12Box :=
  sound_of_literal_split component99Node12Box component99Node10Box component99Node11Box
    .chi (67/256) (by rfl) (by rfl)
    component99Node10_sound component99Node11_sound

private noncomputable def component99Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node13_sound : Sound component99Node13Box :=
  sound_of_literal_split component99Node13Box component99Node9Box component99Node12Box
    .k (117/32) (by rfl) (by rfl)
    component99Node9_sound component99Node12_sound

private noncomputable def component99Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node14_sound : Sound component99Node14Box :=
  sound_of_literal_split component99Node14Box component99Node6Box component99Node13Box
    .chi (33/128) (by rfl) (by rfl)
    component99Node6_sound component99Node13_sound

private noncomputable def component99Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node15_sound : Sound component99Node15Box :=
  sound_of_literal_split component99Node15Box leaf4829Box leaf4830Box
    .k (237/64) (by rfl) (by rfl)
    leaf4829FlatSound leaf4830FlatSound

private noncomputable def component99Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node16_sound : Sound component99Node16Box :=
  sound_of_literal_split component99Node16Box leaf4831Box leaf4832Box
    .k (237/64) (by rfl) (by rfl)
    leaf4831FlatSound leaf4832FlatSound

private noncomputable def component99Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node17_sound : Sound component99Node17Box :=
  sound_of_literal_split component99Node17Box component99Node15Box component99Node16Box
    .chi (65/256) (by rfl) (by rfl)
    component99Node15_sound component99Node16_sound

private noncomputable def component99Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node18_sound : Sound component99Node18Box :=
  sound_of_literal_split component99Node18Box leaf4833Box leaf4834Box
    .k (239/64) (by rfl) (by rfl)
    leaf4833FlatSound leaf4834FlatSound

private noncomputable def component99Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node19_sound : Sound component99Node19Box :=
  sound_of_literal_split component99Node19Box leaf4835Box leaf4836Box
    .k (239/64) (by rfl) (by rfl)
    leaf4835FlatSound leaf4836FlatSound

private noncomputable def component99Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node20_sound : Sound component99Node20Box :=
  sound_of_literal_split component99Node20Box component99Node18Box component99Node19Box
    .chi (65/256) (by rfl) (by rfl)
    component99Node18_sound component99Node19_sound

private noncomputable def component99Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node21_sound : Sound component99Node21Box :=
  sound_of_literal_split component99Node21Box component99Node17Box component99Node20Box
    .k (119/32) (by rfl) (by rfl)
    component99Node17_sound component99Node20_sound

private noncomputable def component99Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node22_sound : Sound component99Node22Box :=
  sound_of_literal_split component99Node22Box leaf4837Box leaf4838Box
    .k (237/64) (by rfl) (by rfl)
    leaf4837FlatSound leaf4838FlatSound

private noncomputable def component99Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node23_sound : Sound component99Node23Box :=
  sound_of_literal_split component99Node23Box leaf4839Box leaf4840Box
    .k (237/64) (by rfl) (by rfl)
    leaf4839FlatSound leaf4840FlatSound

private noncomputable def component99Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node24_sound : Sound component99Node24Box :=
  sound_of_literal_split component99Node24Box component99Node22Box component99Node23Box
    .chi (67/256) (by rfl) (by rfl)
    component99Node22_sound component99Node23_sound

private noncomputable def component99Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node25_sound : Sound component99Node25Box :=
  sound_of_literal_split component99Node25Box leaf4841Box leaf4842Box
    .k (239/64) (by rfl) (by rfl)
    leaf4841FlatSound leaf4842FlatSound

private noncomputable def component99Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node26_sound : Sound component99Node26Box :=
  sound_of_literal_split component99Node26Box leaf4843Box leaf4844Box
    .k (239/64) (by rfl) (by rfl)
    leaf4843FlatSound leaf4844FlatSound

private noncomputable def component99Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node27_sound : Sound component99Node27Box :=
  sound_of_literal_split component99Node27Box component99Node25Box component99Node26Box
    .chi (67/256) (by rfl) (by rfl)
    component99Node25_sound component99Node26_sound

private noncomputable def component99Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node28_sound : Sound component99Node28Box :=
  sound_of_literal_split component99Node28Box component99Node24Box component99Node27Box
    .k (119/32) (by rfl) (by rfl)
    component99Node24_sound component99Node27_sound

private noncomputable def component99Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node29_sound : Sound component99Node29Box :=
  sound_of_literal_split component99Node29Box component99Node21Box component99Node28Box
    .chi (33/128) (by rfl) (by rfl)
    component99Node21_sound component99Node28_sound

private noncomputable def component99Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component99Node30_sound : Sound component99Node30Box :=
  sound_of_literal_split component99Node30Box component99Node14Box component99Node29Box
    .k (59/16) (by rfl) (by rfl)
    component99Node14_sound component99Node29_sound

private noncomputable def component99Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node31_sound : Sound component99Node31Box :=
  sound_of_literal_split component99Node31Box leaf4845Box leaf4846Box
    .k (233/64) (by rfl) (by rfl)
    leaf4845FlatSound leaf4846FlatSound

private noncomputable def component99Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node32_sound : Sound component99Node32Box :=
  sound_of_literal_split component99Node32Box leaf4847Box leaf4848Box
    .k (233/64) (by rfl) (by rfl)
    leaf4847FlatSound leaf4848FlatSound

private noncomputable def component99Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node33_sound : Sound component99Node33Box :=
  sound_of_literal_split component99Node33Box component99Node31Box component99Node32Box
    .chi (69/256) (by rfl) (by rfl)
    component99Node31_sound component99Node32_sound

private noncomputable def component99Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node34_sound : Sound component99Node34Box :=
  sound_of_literal_split component99Node34Box leaf4849Box leaf4850Box
    .k (235/64) (by rfl) (by rfl)
    leaf4849FlatSound leaf4850FlatSound

private noncomputable def component99Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node35_sound : Sound component99Node35Box :=
  sound_of_literal_split component99Node35Box leaf4851Box leaf4852Box
    .k (235/64) (by rfl) (by rfl)
    leaf4851FlatSound leaf4852FlatSound

private noncomputable def component99Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node36_sound : Sound component99Node36Box :=
  sound_of_literal_split component99Node36Box component99Node34Box component99Node35Box
    .chi (69/256) (by rfl) (by rfl)
    component99Node34_sound component99Node35_sound

private noncomputable def component99Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node37_sound : Sound component99Node37Box :=
  sound_of_literal_split component99Node37Box component99Node33Box component99Node36Box
    .k (117/32) (by rfl) (by rfl)
    component99Node33_sound component99Node36_sound

private noncomputable def component99Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node38_sound : Sound component99Node38Box :=
  sound_of_literal_split component99Node38Box leaf4853Box leaf4854Box
    .k (233/64) (by rfl) (by rfl)
    leaf4853FlatSound leaf4854FlatSound

private noncomputable def component99Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node39_sound : Sound component99Node39Box :=
  sound_of_literal_split component99Node39Box leaf4855Box leaf4856Box
    .k (233/64) (by rfl) (by rfl)
    leaf4855FlatSound leaf4856FlatSound

private noncomputable def component99Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node40_sound : Sound component99Node40Box :=
  sound_of_literal_split component99Node40Box component99Node38Box component99Node39Box
    .chi (71/256) (by rfl) (by rfl)
    component99Node38_sound component99Node39_sound

private noncomputable def component99Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node41_sound : Sound component99Node41Box :=
  sound_of_literal_split component99Node41Box leaf4857Box leaf4858Box
    .k (235/64) (by rfl) (by rfl)
    leaf4857FlatSound leaf4858FlatSound

private noncomputable def component99Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node42_sound : Sound component99Node42Box :=
  sound_of_literal_split component99Node42Box leaf4859Box leaf4860Box
    .k (235/64) (by rfl) (by rfl)
    leaf4859FlatSound leaf4860FlatSound

private noncomputable def component99Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node43_sound : Sound component99Node43Box :=
  sound_of_literal_split component99Node43Box component99Node41Box component99Node42Box
    .chi (71/256) (by rfl) (by rfl)
    component99Node41_sound component99Node42_sound

private noncomputable def component99Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node44_sound : Sound component99Node44Box :=
  sound_of_literal_split component99Node44Box component99Node40Box component99Node43Box
    .k (117/32) (by rfl) (by rfl)
    component99Node40_sound component99Node43_sound

private noncomputable def component99Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node45_sound : Sound component99Node45Box :=
  sound_of_literal_split component99Node45Box component99Node37Box component99Node44Box
    .chi (35/128) (by rfl) (by rfl)
    component99Node37_sound component99Node44_sound

private noncomputable def component99Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node46_sound : Sound component99Node46Box :=
  sound_of_literal_split component99Node46Box leaf4861Box leaf4862Box
    .k (237/64) (by rfl) (by rfl)
    leaf4861FlatSound leaf4862FlatSound

private noncomputable def component99Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node47_sound : Sound component99Node47Box :=
  sound_of_literal_split component99Node47Box leaf4863Box leaf4864Box
    .k (237/64) (by rfl) (by rfl)
    leaf4863FlatSound leaf4864FlatSound

private noncomputable def component99Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node48_sound : Sound component99Node48Box :=
  sound_of_literal_split component99Node48Box component99Node46Box component99Node47Box
    .chi (69/256) (by rfl) (by rfl)
    component99Node46_sound component99Node47_sound

private noncomputable def component99Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node49_sound : Sound component99Node49Box :=
  sound_of_literal_split component99Node49Box leaf4865Box leaf4866Box
    .k (239/64) (by rfl) (by rfl)
    leaf4865FlatSound leaf4866FlatSound

private noncomputable def component99Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node50_sound : Sound component99Node50Box :=
  sound_of_literal_split component99Node50Box leaf4867Box leaf4868Box
    .k (239/64) (by rfl) (by rfl)
    leaf4867FlatSound leaf4868FlatSound

private noncomputable def component99Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node51_sound : Sound component99Node51Box :=
  sound_of_literal_split component99Node51Box component99Node49Box component99Node50Box
    .chi (69/256) (by rfl) (by rfl)
    component99Node49_sound component99Node50_sound

private noncomputable def component99Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component99Node52_sound : Sound component99Node52Box :=
  sound_of_literal_split component99Node52Box component99Node48Box component99Node51Box
    .k (119/32) (by rfl) (by rfl)
    component99Node48_sound component99Node51_sound

private noncomputable def component99Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node53_sound : Sound component99Node53Box :=
  sound_of_literal_split component99Node53Box leaf4869Box leaf4870Box
    .k (237/64) (by rfl) (by rfl)
    leaf4869FlatSound leaf4870FlatSound

private noncomputable def component99Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node54_sound : Sound component99Node54Box :=
  sound_of_literal_split component99Node54Box leaf4871Box leaf4872Box
    .k (237/64) (by rfl) (by rfl)
    leaf4871FlatSound leaf4872FlatSound

private noncomputable def component99Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node55_sound : Sound component99Node55Box :=
  sound_of_literal_split component99Node55Box component99Node53Box component99Node54Box
    .chi (71/256) (by rfl) (by rfl)
    component99Node53_sound component99Node54_sound

private noncomputable def component99Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component99Node56_sound : Sound component99Node56Box :=
  sound_of_literal_split component99Node56Box leaf4873Box leaf4874Box
    .k (239/64) (by rfl) (by rfl)
    leaf4873FlatSound leaf4874FlatSound

private noncomputable def component99Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node57_sound : Sound component99Node57Box :=
  sound_of_literal_split component99Node57Box leaf4875Box leaf4876Box
    .k (239/64) (by rfl) (by rfl)
    leaf4875FlatSound leaf4876FlatSound

private noncomputable def component99Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node58_sound : Sound component99Node58Box :=
  sound_of_literal_split component99Node58Box component99Node56Box component99Node57Box
    .chi (71/256) (by rfl) (by rfl)
    component99Node56_sound component99Node57_sound

private noncomputable def component99Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node59_sound : Sound component99Node59Box :=
  sound_of_literal_split component99Node59Box component99Node55Box component99Node58Box
    .k (119/32) (by rfl) (by rfl)
    component99Node55_sound component99Node58_sound

private noncomputable def component99Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node60_sound : Sound component99Node60Box :=
  sound_of_literal_split component99Node60Box component99Node52Box component99Node59Box
    .chi (35/128) (by rfl) (by rfl)
    component99Node52_sound component99Node59_sound

private noncomputable def component99Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component99Node61_sound : Sound component99Node61Box :=
  sound_of_literal_split component99Node61Box component99Node45Box component99Node60Box
    .k (59/16) (by rfl) (by rfl)
    component99Node45_sound component99Node60_sound

noncomputable def component99Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
theorem component99_sound : Sound component99Box :=
  sound_of_literal_split component99Box component99Node30Box component99Node61Box
    .chi (17/64) (by rfl) (by rfl)
    component99Node30_sound component99Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
