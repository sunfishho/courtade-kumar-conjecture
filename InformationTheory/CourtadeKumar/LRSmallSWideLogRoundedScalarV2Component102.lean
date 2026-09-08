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

private noncomputable def leaf4991Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4991Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430932992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2080279967/1073741824) }, upper := { exponent := 0, mantissa := (32049/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867854847/274861865984) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf4991InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf4991LocalValidity :
    LeafFacts leaf4991Box leaf4991Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4991Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430932992) }) = true
      norm_num [leaf4991Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4991CertificateValid :
    WideCertificateValid leaf4991Box leaf4991Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi277ValidityFacts
    leaf4991LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4991CoverageChecked :
    coverageCheck (innerAD leaf4991Box) leaf4991InnerLog = true := by
  rfl'

private theorem leaf4991InnerLogValid :
    leaf4991InnerLog.Valid 8 (innerAD leaf4991Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf4991CoverageChecked

private noncomputable def leaf4991InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4991InputLogOnePlusV_eq :
    leaf4991InputLogOnePlusV = outerEnclosure 24
      (leaf4991Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4991RoundedFacts : LeafRoundedFacts 8
    leaf4991Certificate.logOnePlusV leaf4991InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4991InputLogOnePlusV_eq }

private noncomputable def leaf4991Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi277InputQChi innerPair306Input
    leaf4991InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4991LowerChecked :
    lowerCheck 24 leaf4991Box leaf4991Inputs = true := by
  rfl'

private theorem leaf4991CoversExact : CoversExact 8
    leaf4991Box leaf4991Certificate leaf4991InnerLog leaf4991Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi277RoundedFacts
    innerPair306RoundedFacts leaf4991RoundedFacts (by rfl)

private theorem leaf4991FlatSound : Sound leaf4991Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4991CertificateValid
    leaf4991InnerLogValid leaf4991CoversExact leaf4991LowerChecked

private noncomputable def leaf4992Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4992Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270099968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2084474013/1073741824) }, upper := { exponent := 0, mantissa := (16057/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540869063/30540199936) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf4992InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4992LocalValidity :
    LeafFacts leaf4992Box leaf4992Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4992Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270099968) }) = true
      norm_num [leaf4992Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4992CertificateValid :
    WideCertificateValid leaf4992Box leaf4992Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi277ValidityFacts
    leaf4992LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4992CoverageChecked :
    coverageCheck (innerAD leaf4992Box) leaf4992InnerLog = true := by
  rfl'

private theorem leaf4992InnerLogValid :
    leaf4992InnerLog.Valid 8 (innerAD leaf4992Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4992CoverageChecked

private noncomputable def leaf4992InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4992InputLogOnePlusV_eq :
    leaf4992InputLogOnePlusV = outerEnclosure 24
      (leaf4992Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4992RoundedFacts : LeafRoundedFacts 8
    leaf4992Certificate.logOnePlusV leaf4992InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4992InputLogOnePlusV_eq }

private noncomputable def leaf4992Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi277InputQChi innerPair113Input
    leaf4992InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4992LowerChecked :
    lowerCheck 24 leaf4992Box leaf4992Inputs = true := by
  rfl'

private theorem leaf4992CoversExact : CoversExact 8
    leaf4992Box leaf4992Certificate leaf4992InnerLog leaf4992Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi277RoundedFacts
    innerPair113RoundedFacts leaf4992RoundedFacts (by rfl)

private theorem leaf4992FlatSound : Sound leaf4992Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4992CertificateValid
    leaf4992InnerLogValid leaf4992CoversExact leaf4992LowerChecked

private noncomputable def leaf4993Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4993Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486161920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2096007645/1073741824) }, upper := { exponent := 0, mantissa := (16145/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973546291/54972323840) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf4993InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4993LocalValidity :
    LeafFacts leaf4993Box leaf4993Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4993Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486161920) }) = true
      norm_num [leaf4993Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4993CertificateValid :
    WideCertificateValid leaf4993Box leaf4993Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi278ValidityFacts
    leaf4993LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4993CoverageChecked :
    coverageCheck (innerAD leaf4993Box) leaf4993InnerLog = true := by
  rfl'

private theorem leaf4993InnerLogValid :
    leaf4993InnerLog.Valid 8 (innerAD leaf4993Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4993CoverageChecked

private noncomputable def leaf4993InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4993InputLogOnePlusV_eq :
    leaf4993InputLogOnePlusV = outerEnclosure 24
      (leaf4993Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4993RoundedFacts : LeafRoundedFacts 8
    leaf4993Certificate.logOnePlusV leaf4993InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4993InputLogOnePlusV_eq }

private noncomputable def leaf4993Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi278InputQChi innerPair108Input
    leaf4993InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4993LowerChecked :
    lowerCheck 24 leaf4993Box leaf4993Inputs = true := by
  rfl'

private theorem leaf4993CoversExact : CoversExact 8
    leaf4993Box leaf4993Certificate leaf4993InnerLog leaf4993Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf4993RoundedFacts (by rfl)

private theorem leaf4993FlatSound : Sound leaf4993Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4993CertificateValid
    leaf4993InnerLogValid leaf4993CoversExact leaf4993LowerChecked

private noncomputable def leaf4994Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4994Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430775808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2100267223/1073741824) }, upper := { exponent := 0, mantissa := (8089/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867697663/274861551616) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf4994InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4994LocalValidity :
    LeafFacts leaf4994Box leaf4994Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4994Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430775808) }) = true
      norm_num [leaf4994Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4994CertificateValid :
    WideCertificateValid leaf4994Box leaf4994Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi278ValidityFacts
    leaf4994LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4994CoverageChecked :
    coverageCheck (innerAD leaf4994Box) leaf4994InnerLog = true := by
  rfl'

private theorem leaf4994InnerLogValid :
    leaf4994InnerLog.Valid 8 (innerAD leaf4994Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4994CoverageChecked

private noncomputable def leaf4994InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4994InputLogOnePlusV_eq :
    leaf4994InputLogOnePlusV = outerEnclosure 24
      (leaf4994Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4994RoundedFacts : LeafRoundedFacts 8
    leaf4994Certificate.logOnePlusV leaf4994InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4994InputLogOnePlusV_eq }

private noncomputable def leaf4994Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi278InputQChi innerPair108Input
    leaf4994InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4994LowerChecked :
    lowerCheck 24 leaf4994Box leaf4994Inputs = true := by
  rfl'

private theorem leaf4994CoversExact : CoversExact 8
    leaf4994Box leaf4994Certificate leaf4994InnerLog leaf4994Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf4994RoundedFacts (by rfl)

private theorem leaf4994FlatSound : Sound leaf4994Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4994CertificateValid
    leaf4994InnerLogValid leaf4994CoversExact leaf4994LowerChecked

private noncomputable def leaf4995Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4995Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430866432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2088668059/1073741824) }, upper := { exponent := 0, mantissa := (32179/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867788287/274861732864) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf4995InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4995LocalValidity :
    LeafFacts leaf4995Box leaf4995Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4995Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430866432) }) = true
      norm_num [leaf4995Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4995CertificateValid :
    WideCertificateValid leaf4995Box leaf4995Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi277ValidityFacts
    leaf4995LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4995CoverageChecked :
    coverageCheck (innerAD leaf4995Box) leaf4995InnerLog = true := by
  rfl'

private theorem leaf4995InnerLogValid :
    leaf4995InnerLog.Valid 8 (innerAD leaf4995Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4995CoverageChecked

private noncomputable def leaf4995InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4995InputLogOnePlusV_eq :
    leaf4995InputLogOnePlusV = outerEnclosure 24
      (leaf4995Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4995RoundedFacts : LeafRoundedFacts 8
    leaf4995Certificate.logOnePlusV leaf4995InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4995InputLogOnePlusV_eq }

private noncomputable def leaf4995Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi277InputQChi innerPair113Input
    leaf4995InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4995LowerChecked :
    lowerCheck 24 leaf4995Box leaf4995Inputs = true := by
  rfl'

private theorem leaf4995CoversExact : CoversExact 8
    leaf4995Box leaf4995Certificate leaf4995InnerLog leaf4995Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi277RoundedFacts
    innerPair113RoundedFacts leaf4995RoundedFacts (by rfl)

private theorem leaf4995FlatSound : Sound leaf4995Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4995CertificateValid
    leaf4995InnerLogValid leaf4995CoversExact leaf4995LowerChecked

private noncomputable def leaf4996Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4996Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084166656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2092862105/1073741824) }, upper := { exponent := 0, mantissa := (8061/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168691471/16168333312) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf4996InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4996LocalValidity :
    LeafFacts leaf4996Box leaf4996Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4996Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084166656) }) = true
      norm_num [leaf4996Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4996CertificateValid :
    WideCertificateValid leaf4996Box leaf4996Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi277ValidityFacts
    leaf4996LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4996CoverageChecked :
    coverageCheck (innerAD leaf4996Box) leaf4996InnerLog = true := by
  rfl'

private theorem leaf4996InnerLogValid :
    leaf4996InnerLog.Valid 8 (innerAD leaf4996Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4996CoverageChecked

private noncomputable def leaf4996InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4996InputLogOnePlusV_eq :
    leaf4996InputLogOnePlusV = outerEnclosure 24
      (leaf4996Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4996RoundedFacts : LeafRoundedFacts 8
    leaf4996Certificate.logOnePlusV leaf4996InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4996InputLogOnePlusV_eq }

private noncomputable def leaf4996Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi277InputQChi innerPair113Input
    leaf4996InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4996LowerChecked :
    lowerCheck 24 leaf4996Box leaf4996Inputs = true := by
  rfl'

private theorem leaf4996CoversExact : CoversExact 8
    leaf4996Box leaf4996Certificate leaf4996InnerLog leaf4996Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi277RoundedFacts
    innerPair113RoundedFacts leaf4996RoundedFacts (by rfl)

private theorem leaf4996FlatSound : Sound leaf4996Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4996CertificateValid
    leaf4996InnerLogValid leaf4996CoversExact leaf4996LowerChecked

private noncomputable def leaf4997Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4997Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430742016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2104526801/1073741824) }, upper := { exponent := 0, mantissa := (16211/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867663871/274861484032) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf4997InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4997LocalValidity :
    LeafFacts leaf4997Box leaf4997Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4997Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430742016) }) = true
      norm_num [leaf4997Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4997CertificateValid :
    WideCertificateValid leaf4997Box leaf4997Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi278ValidityFacts
    leaf4997LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4997CoverageChecked :
    coverageCheck (innerAD leaf4997Box) leaf4997InnerLog = true := by
  rfl'

private theorem leaf4997InnerLogValid :
    leaf4997InnerLog.Valid 8 (innerAD leaf4997Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4997CoverageChecked

private noncomputable def leaf4997InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4997InputLogOnePlusV_eq :
    leaf4997InputLogOnePlusV = outerEnclosure 24
      (leaf4997Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4997RoundedFacts : LeafRoundedFacts 8
    leaf4997Certificate.logOnePlusV leaf4997InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4997InputLogOnePlusV_eq }

private noncomputable def leaf4997Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi278InputQChi innerPair108Input
    leaf4997InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4997LowerChecked :
    lowerCheck 24 leaf4997Box leaf4997Inputs = true := by
  rfl'

private theorem leaf4997CoversExact : CoversExact 8
    leaf4997Box leaf4997Certificate leaf4997InnerLog leaf4997Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf4997RoundedFacts (by rfl)

private theorem leaf4997FlatSound : Sound leaf4997Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4997CertificateValid
    leaf4997InnerLogValid leaf4997CoversExact leaf4997LowerChecked

private noncomputable def leaf4998Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4998Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430708224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2108786379/1073741824) }, upper := { exponent := 0, mantissa := (4061/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867630079/274861416448) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf4998InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4998LocalValidity :
    LeafFacts leaf4998Box leaf4998Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4998Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430708224) }) = true
      norm_num [leaf4998Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4998CertificateValid :
    WideCertificateValid leaf4998Box leaf4998Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi278ValidityFacts
    leaf4998LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4998CoverageChecked :
    coverageCheck (innerAD leaf4998Box) leaf4998InnerLog = true := by
  rfl'

private theorem leaf4998InnerLogValid :
    leaf4998InnerLog.Valid 8 (innerAD leaf4998Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4998CoverageChecked

private noncomputable def leaf4998InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4998InputLogOnePlusV_eq :
    leaf4998InputLogOnePlusV = outerEnclosure 24
      (leaf4998Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4998RoundedFacts : LeafRoundedFacts 8
    leaf4998Certificate.logOnePlusV leaf4998InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4998InputLogOnePlusV_eq }

private noncomputable def leaf4998Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi278InputQChi innerPair108Input
    leaf4998InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4998LowerChecked :
    lowerCheck 24 leaf4998Box leaf4998Inputs = true := by
  rfl'

private theorem leaf4998CoversExact : CoversExact 8
    leaf4998Box leaf4998Certificate leaf4998InnerLog leaf4998Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf4998RoundedFacts (by rfl)

private theorem leaf4998FlatSound : Sound leaf4998Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4998CertificateValid
    leaf4998InnerLogValid leaf4998CoversExact leaf4998LowerChecked

private noncomputable def leaf4999Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4999Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810228736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2111735323/1073741824) }, upper := { exponent := 0, mantissa := (32531/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622536021/91620457472) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf4999InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4999LocalValidity :
    LeafFacts leaf4999Box leaf4999Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4999Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810228736) }) = true
      norm_num [leaf4999Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4999CertificateValid :
    WideCertificateValid leaf4999Box leaf4999Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi275ValidityFacts
    leaf4999LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4999CoverageChecked :
    coverageCheck (innerAD leaf4999Box) leaf4999InnerLog = true := by
  rfl'

private theorem leaf4999InnerLogValid :
    leaf4999InnerLog.Valid 8 (innerAD leaf4999Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4999CoverageChecked

private noncomputable def leaf4999InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4999InputLogOnePlusV_eq :
    leaf4999InputLogOnePlusV = outerEnclosure 24
      (leaf4999Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4999RoundedFacts : LeafRoundedFacts 8
    leaf4999Certificate.logOnePlusV leaf4999InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4999InputLogOnePlusV_eq }

private noncomputable def leaf4999Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi275InputQChi innerPair108Input
    leaf4999InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4999LowerChecked :
    lowerCheck 24 leaf4999Box leaf4999Inputs = true := by
  rfl'

private theorem leaf4999CoversExact : CoversExact 8
    leaf4999Box leaf4999Certificate leaf4999InnerLog leaf4999Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf4999RoundedFacts (by rfl)

private theorem leaf4999FlatSound : Sound leaf4999Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4999CertificateValid
    leaf4999InnerLogValid leaf4999CoversExact leaf4999LowerChecked

private noncomputable def leaf5000Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5000Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430651904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2116060433/1073741824) }, upper := { exponent := 0, mantissa := (16299/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867573759/274861303808) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5000InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5000LocalValidity :
    LeafFacts leaf5000Box leaf5000Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5000Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430651904) }) = true
      norm_num [leaf5000Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5000CertificateValid :
    WideCertificateValid leaf5000Box leaf5000Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi275ValidityFacts
    leaf5000LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5000CoverageChecked :
    coverageCheck (innerAD leaf5000Box) leaf5000InnerLog = true := by
  rfl'

private theorem leaf5000InnerLogValid :
    leaf5000InnerLog.Valid 8 (innerAD leaf5000Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5000CoverageChecked

private noncomputable def leaf5000InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5000InputLogOnePlusV_eq :
    leaf5000InputLogOnePlusV = outerEnclosure 24
      (leaf5000Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5000RoundedFacts : LeafRoundedFacts 8
    leaf5000Certificate.logOnePlusV leaf5000InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5000InputLogOnePlusV_eq }

private noncomputable def leaf5000Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi275InputQChi innerPair108Input
    leaf5000InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5000LowerChecked :
    lowerCheck 24 leaf5000Box leaf5000Inputs = true := by
  rfl'

private theorem leaf5000CoversExact : CoversExact 8
    leaf5000Box leaf5000Certificate leaf5000InnerLog leaf5000Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf5000RoundedFacts (by rfl)

private theorem leaf5000FlatSound : Sound leaf5000Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5000CertificateValid
    leaf5000InnerLogValid leaf5000CoversExact leaf5000LowerChecked

private noncomputable def leaf5001Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5001Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715281408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2127463001/1073741824) }, upper := { exponent := 1, mantissa := (8193/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432693759/137430562816) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5001InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf5001LocalValidity :
    LeafFacts leaf5001Box leaf5001Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5001Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715281408) }) = true
      norm_num [leaf5001Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5001CertificateValid :
    WideCertificateValid leaf5001Box leaf5001Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi276ValidityFacts
    leaf5001LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5001CoverageChecked :
    coverageCheck (innerAD leaf5001Box) leaf5001InnerLog = true := by
  rfl'

private theorem leaf5001InnerLogValid :
    leaf5001InnerLog.Valid 8 (innerAD leaf5001Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf5001CoverageChecked

private noncomputable def leaf5001InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5001InputLogOnePlusV_eq :
    leaf5001InputLogOnePlusV = outerEnclosure 24
      (leaf5001Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5001RoundedFacts : LeafRoundedFacts 8
    leaf5001Certificate.logOnePlusV leaf5001InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5001InputLogOnePlusV_eq }

private noncomputable def leaf5001Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi276InputQChi innerPair321Input
    leaf5001InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5001LowerChecked :
    lowerCheck 24 leaf5001Box leaf5001Inputs = true := by
  rfl'

private theorem leaf5001CoversExact : CoversExact 8
    leaf5001Box leaf5001Certificate leaf5001InnerLog leaf5001Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi276RoundedFacts
    innerPair321RoundedFacts leaf5001RoundedFacts (by rfl)

private theorem leaf5001FlatSound : Sound leaf5001Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5001CertificateValid
    leaf5001InnerLogValid leaf5001CoversExact leaf5001LowerChecked

private noncomputable def leaf5002Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5002Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905088000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2131853643/1073741824) }, upper := { exponent := 1, mantissa := (4105/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810892117/45810176000) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5002InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5002LocalValidity :
    LeafFacts leaf5002Box leaf5002Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5002Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905088000) }) = true
      norm_num [leaf5002Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5002CertificateValid :
    WideCertificateValid leaf5002Box leaf5002Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi276ValidityFacts
    leaf5002LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5002CoverageChecked :
    coverageCheck (innerAD leaf5002Box) leaf5002InnerLog = true := by
  rfl'

private theorem leaf5002InnerLogValid :
    leaf5002InnerLog.Valid 8 (innerAD leaf5002Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5002CoverageChecked

private noncomputable def leaf5002InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5002InputLogOnePlusV_eq :
    leaf5002InputLogOnePlusV = outerEnclosure 24
      (leaf5002Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5002RoundedFacts : LeafRoundedFacts 8
    leaf5002Certificate.logOnePlusV leaf5002InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5002InputLogOnePlusV_eq }

private noncomputable def leaf5002Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi276InputQChi innerPair533Input
    leaf5002InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5002LowerChecked :
    lowerCheck 24 leaf5002Box leaf5002Inputs = true := by
  rfl'

private theorem leaf5002CoversExact : CoversExact 8
    leaf5002Box leaf5002Certificate leaf5002InnerLog leaf5002Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi276RoundedFacts
    innerPair533RoundedFacts leaf5002RoundedFacts (by rfl)

private theorem leaf5002FlatSound : Sound leaf5002Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5002CertificateValid
    leaf5002InnerLogValid leaf5002CoversExact leaf5002LowerChecked

private noncomputable def leaf5003Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5003Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715308800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2120385543/1073741824) }, upper := { exponent := 0, mantissa := (32665/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432721151/137430617600) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5003InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5003LocalValidity :
    LeafFacts leaf5003Box leaf5003Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5003Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715308800) }) = true
      norm_num [leaf5003Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5003CertificateValid :
    WideCertificateValid leaf5003Box leaf5003Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi275ValidityFacts
    leaf5003LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5003CoverageChecked :
    coverageCheck (innerAD leaf5003Box) leaf5003InnerLog = true := by
  rfl'

private theorem leaf5003InnerLogValid :
    leaf5003InnerLog.Valid 8 (innerAD leaf5003Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5003CoverageChecked

private noncomputable def leaf5003InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5003InputLogOnePlusV_eq :
    leaf5003InputLogOnePlusV = outerEnclosure 24
      (leaf5003Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5003RoundedFacts : LeafRoundedFacts 8
    leaf5003Certificate.logOnePlusV leaf5003InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5003InputLogOnePlusV_eq }

private noncomputable def leaf5003Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi275InputQChi innerPair108Input
    leaf5003InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5003LowerChecked :
    lowerCheck 24 leaf5003Box leaf5003Inputs = true := by
  rfl'

private theorem leaf5003CoversExact : CoversExact 8
    leaf5003Box leaf5003Certificate leaf5003InnerLog leaf5003Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf5003RoundedFacts (by rfl)

private theorem leaf5003FlatSound : Sound leaf5003Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5003CertificateValid
    leaf5003InnerLogValid leaf5003CoversExact leaf5003LowerChecked

private noncomputable def leaf5004Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5004Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905097216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2124710653/1073741824) }, upper := { exponent := 0, mantissa := (8183/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810901333/45810194432) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5004InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5004LocalValidity :
    LeafFacts leaf5004Box leaf5004Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5004Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905097216) }) = true
      norm_num [leaf5004Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5004CertificateValid :
    WideCertificateValid leaf5004Box leaf5004Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi275ValidityFacts
    leaf5004LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5004CoverageChecked :
    coverageCheck (innerAD leaf5004Box) leaf5004InnerLog = true := by
  rfl'

private theorem leaf5004InnerLogValid :
    leaf5004InnerLog.Valid 8 (innerAD leaf5004Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5004CoverageChecked

private noncomputable def leaf5004InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5004InputLogOnePlusV_eq :
    leaf5004InputLogOnePlusV = outerEnclosure 24
      (leaf5004Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5004RoundedFacts : LeafRoundedFacts 8
    leaf5004Certificate.logOnePlusV leaf5004InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5004InputLogOnePlusV_eq }

private noncomputable def leaf5004Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi275InputQChi innerPair108Input
    leaf5004InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5004LowerChecked :
    lowerCheck 24 leaf5004Box leaf5004Inputs = true := by
  rfl'

private theorem leaf5004CoversExact : CoversExact 8
    leaf5004Box leaf5004Certificate leaf5004InnerLog leaf5004Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi275RoundedFacts
    innerPair108RoundedFacts leaf5004RoundedFacts (by rfl)

private theorem leaf5004FlatSound : Sound leaf5004Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5004CertificateValid
    leaf5004InnerLogValid leaf5004CoversExact leaf5004LowerChecked

private noncomputable def leaf5005Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5005Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715246592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2136244285/1073741824) }, upper := { exponent := 1, mantissa := (8227/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432658943/137430493184) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5005InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5005LocalValidity :
    LeafFacts leaf5005Box leaf5005Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5005Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715246592) }) = true
      norm_num [leaf5005Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5005CertificateValid :
    WideCertificateValid leaf5005Box leaf5005Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi276ValidityFacts
    leaf5005LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5005CoverageChecked :
    coverageCheck (innerAD leaf5005Box) leaf5005InnerLog = true := by
  rfl'

private theorem leaf5005InnerLogValid :
    leaf5005InnerLog.Valid 8 (innerAD leaf5005Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5005CoverageChecked

private noncomputable def leaf5005InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5005InputLogOnePlusV_eq :
    leaf5005InputLogOnePlusV = outerEnclosure 24
      (leaf5005Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5005RoundedFacts : LeafRoundedFacts 8
    leaf5005Certificate.logOnePlusV leaf5005InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5005InputLogOnePlusV_eq }

private noncomputable def leaf5005Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi276InputQChi innerPair533Input
    leaf5005InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5005LowerChecked :
    lowerCheck 24 leaf5005Box leaf5005Inputs = true := by
  rfl'

private theorem leaf5005CoversExact : CoversExact 8
    leaf5005Box leaf5005Certificate leaf5005InnerLog leaf5005Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi276RoundedFacts
    innerPair533RoundedFacts leaf5005RoundedFacts (by rfl)

private theorem leaf5005FlatSound : Sound leaf5005Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5005CertificateValid
    leaf5005InnerLogValid leaf5005CoversExact leaf5005LowerChecked

private noncomputable def leaf5006Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5006Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816461312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2140634927/1073741824) }, upper := { exponent := 1, mantissa := (2061/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633234505/19632922624) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5006InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5006LocalValidity :
    LeafFacts leaf5006Box leaf5006Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5006Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816461312) }) = true
      norm_num [leaf5006Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5006CertificateValid :
    WideCertificateValid leaf5006Box leaf5006Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi276ValidityFacts
    leaf5006LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5006CoverageChecked :
    coverageCheck (innerAD leaf5006Box) leaf5006InnerLog = true := by
  rfl'

private theorem leaf5006InnerLogValid :
    leaf5006InnerLog.Valid 8 (innerAD leaf5006Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5006CoverageChecked

private noncomputable def leaf5006InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5006InputLogOnePlusV_eq :
    leaf5006InputLogOnePlusV = outerEnclosure 24
      (leaf5006Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5006RoundedFacts : LeafRoundedFacts 8
    leaf5006Certificate.logOnePlusV leaf5006InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5006InputLogOnePlusV_eq }

private noncomputable def leaf5006Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi276InputQChi innerPair533Input
    leaf5006InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5006LowerChecked :
    lowerCheck 24 leaf5006Box leaf5006Inputs = true := by
  rfl'

private theorem leaf5006CoversExact : CoversExact 8
    leaf5006Box leaf5006Certificate leaf5006InnerLog leaf5006Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi276RoundedFacts
    innerPair533RoundedFacts leaf5006RoundedFacts (by rfl)

private theorem leaf5006FlatSound : Sound leaf5006Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5006CertificateValid
    leaf5006InnerLogValid leaf5006CoversExact leaf5006LowerChecked

private noncomputable def leaf5007Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5007Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810266624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2097056151/1073741824) }, upper := { exponent := 0, mantissa := (32309/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622573909/91620533248) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5007InnerLog : WideLogData :=
  innerPair114Data

set_option maxRecDepth 1000000 in
private theorem leaf5007LocalValidity :
    LeafFacts leaf5007Box leaf5007Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5007Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810266624) }) = true
      norm_num [leaf5007Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5007CertificateValid :
    WideCertificateValid leaf5007Box leaf5007Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi277ValidityFacts
    leaf5007LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5007CoverageChecked :
    coverageCheck (innerAD leaf5007Box) leaf5007InnerLog = true := by
  rfl'

private theorem leaf5007InnerLogValid :
    leaf5007InnerLog.Valid 8 (innerAD leaf5007Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint267PositiveFacts.valid leaf5007CoverageChecked

private noncomputable def leaf5007InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5007InputLogOnePlusV_eq :
    leaf5007InputLogOnePlusV = outerEnclosure 24
      (leaf5007Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5007RoundedFacts : LeafRoundedFacts 8
    leaf5007Certificate.logOnePlusV leaf5007InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5007InputLogOnePlusV_eq }

private noncomputable def leaf5007Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi277InputQChi innerPair114Input
    leaf5007InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5007LowerChecked :
    lowerCheck 24 leaf5007Box leaf5007Inputs = true := by
  rfl'

private theorem leaf5007CoversExact : CoversExact 8
    leaf5007Box leaf5007Certificate leaf5007InnerLog leaf5007Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi277RoundedFacts
    innerPair114RoundedFacts leaf5007RoundedFacts (by rfl)

private theorem leaf5007FlatSound : Sound leaf5007Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5007CertificateValid
    leaf5007InnerLogValid leaf5007CoversExact leaf5007LowerChecked

private noncomputable def leaf5008Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5008Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430766592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2101250197/1073741824) }, upper := { exponent := 0, mantissa := (16187/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867688447/274861533184) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5008InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf5008LocalValidity :
    LeafFacts leaf5008Box leaf5008Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5008Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430766592) }) = true
      norm_num [leaf5008Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5008CertificateValid :
    WideCertificateValid leaf5008Box leaf5008Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi277ValidityFacts
    leaf5008LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5008CoverageChecked :
    coverageCheck (innerAD leaf5008Box) leaf5008InnerLog = true := by
  rfl'

private theorem leaf5008InnerLogValid :
    leaf5008InnerLog.Valid 8 (innerAD leaf5008Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf5008CoverageChecked

private noncomputable def leaf5008InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5008InputLogOnePlusV_eq :
    leaf5008InputLogOnePlusV = outerEnclosure 24
      (leaf5008Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5008RoundedFacts : LeafRoundedFacts 8
    leaf5008Certificate.logOnePlusV leaf5008InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5008InputLogOnePlusV_eq }

private noncomputable def leaf5008Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi277InputQChi innerPair238Input
    leaf5008InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5008LowerChecked :
    lowerCheck 24 leaf5008Box leaf5008Inputs = true := by
  rfl'

private theorem leaf5008CoversExact : CoversExact 8
    leaf5008Box leaf5008Certificate leaf5008InnerLog leaf5008Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi277RoundedFacts
    innerPair238RoundedFacts leaf5008RoundedFacts (by rfl)

private theorem leaf5008FlatSound : Sound leaf5008Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5008CertificateValid
    leaf5008InnerLogValid leaf5008CoversExact leaf5008LowerChecked

private noncomputable def leaf5009Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5009Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430674432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2113045957/1073741824) }, upper := { exponent := 0, mantissa := (16277/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867596287/274861348864) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5009InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5009LocalValidity :
    LeafFacts leaf5009Box leaf5009Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5009Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430674432) }) = true
      norm_num [leaf5009Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5009CertificateValid :
    WideCertificateValid leaf5009Box leaf5009Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi278ValidityFacts
    leaf5009LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5009CoverageChecked :
    coverageCheck (innerAD leaf5009Box) leaf5009InnerLog = true := by
  rfl'

private theorem leaf5009InnerLogValid :
    leaf5009InnerLog.Valid 8 (innerAD leaf5009Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5009CoverageChecked

private noncomputable def leaf5009InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5009InputLogOnePlusV_eq :
    leaf5009InputLogOnePlusV = outerEnclosure 24
      (leaf5009Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5009RoundedFacts : LeafRoundedFacts 8
    leaf5009Certificate.logOnePlusV leaf5009InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5009InputLogOnePlusV_eq }

private noncomputable def leaf5009Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi278InputQChi innerPair108Input
    leaf5009InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5009LowerChecked :
    lowerCheck 24 leaf5009Box leaf5009Inputs = true := by
  rfl'

private theorem leaf5009CoversExact : CoversExact 8
    leaf5009Box leaf5009Certificate leaf5009InnerLog leaf5009Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf5009RoundedFacts (by rfl)

private theorem leaf5009FlatSound : Sound leaf5009Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5009CertificateValid
    leaf5009InnerLogValid leaf5009CoversExact leaf5009LowerChecked

private noncomputable def leaf5010Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5010Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486128128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2117305535/1073741824) }, upper := { exponent := 0, mantissa := (8155/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973512499/54972256256) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5010InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5010LocalValidity :
    LeafFacts leaf5010Box leaf5010Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5010Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486128128) }) = true
      norm_num [leaf5010Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5010CertificateValid :
    WideCertificateValid leaf5010Box leaf5010Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi278ValidityFacts
    leaf5010LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5010CoverageChecked :
    coverageCheck (innerAD leaf5010Box) leaf5010InnerLog = true := by
  rfl'

private theorem leaf5010InnerLogValid :
    leaf5010InnerLog.Valid 8 (innerAD leaf5010Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5010CoverageChecked

private noncomputable def leaf5010InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5010InputLogOnePlusV_eq :
    leaf5010InputLogOnePlusV = outerEnclosure 24
      (leaf5010Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5010RoundedFacts : LeafRoundedFacts 8
    leaf5010Certificate.logOnePlusV leaf5010InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5010InputLogOnePlusV_eq }

private noncomputable def leaf5010Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi278InputQChi innerPair108Input
    leaf5010InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5010LowerChecked :
    lowerCheck 24 leaf5010Box leaf5010Inputs = true := by
  rfl'

private theorem leaf5010CoversExact : CoversExact 8
    leaf5010Box leaf5010Certificate leaf5010InnerLog leaf5010Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf5010RoundedFacts (by rfl)

private theorem leaf5010FlatSound : Sound leaf5010Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5010CertificateValid
    leaf5010InnerLogValid leaf5010CoversExact leaf5010LowerChecked

private noncomputable def leaf5011Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5011Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430733312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2105444243/1073741824) }, upper := { exponent := 0, mantissa := (32439/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867655167/274861466624) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5011InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf5011LocalValidity :
    LeafFacts leaf5011Box leaf5011Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5011Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430733312) }) = true
      norm_num [leaf5011Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5011CertificateValid :
    WideCertificateValid leaf5011Box leaf5011Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi277ValidityFacts
    leaf5011LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5011CoverageChecked :
    coverageCheck (innerAD leaf5011Box) leaf5011InnerLog = true := by
  rfl'

private theorem leaf5011InnerLogValid :
    leaf5011InnerLog.Valid 8 (innerAD leaf5011Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf5011CoverageChecked

private noncomputable def leaf5011InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5011InputLogOnePlusV_eq :
    leaf5011InputLogOnePlusV = outerEnclosure 24
      (leaf5011Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5011RoundedFacts : LeafRoundedFacts 8
    leaf5011Certificate.logOnePlusV leaf5011InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5011InputLogOnePlusV_eq }

private noncomputable def leaf5011Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi277InputQChi innerPair238Input
    leaf5011InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5011LowerChecked :
    lowerCheck 24 leaf5011Box leaf5011Inputs = true := by
  rfl'

private theorem leaf5011CoversExact : CoversExact 8
    leaf5011Box leaf5011Certificate leaf5011InnerLog leaf5011Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi277RoundedFacts
    innerPair238RoundedFacts leaf5011RoundedFacts (by rfl)

private theorem leaf5011FlatSound : Sound leaf5011Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5011CertificateValid
    leaf5011InnerLogValid leaf5011CoversExact leaf5011LowerChecked

private noncomputable def leaf5012Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf5012Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810233344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2109638289/1073741824) }, upper := { exponent := 0, mantissa := (4063/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622540629/91620466688) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5012InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5012LocalValidity :
    LeafFacts leaf5012Box leaf5012Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5012Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810233344) }) = true
      norm_num [leaf5012Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5012CertificateValid :
    WideCertificateValid leaf5012Box leaf5012Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi277ValidityFacts
    leaf5012LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5012CoverageChecked :
    coverageCheck (innerAD leaf5012Box) leaf5012InnerLog = true := by
  rfl'

private theorem leaf5012InnerLogValid :
    leaf5012InnerLog.Valid 8 (innerAD leaf5012Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5012CoverageChecked

private noncomputable def leaf5012InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5012InputLogOnePlusV_eq :
    leaf5012InputLogOnePlusV = outerEnclosure 24
      (leaf5012Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5012RoundedFacts : LeafRoundedFacts 8
    leaf5012Certificate.logOnePlusV leaf5012InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5012InputLogOnePlusV_eq }

private noncomputable def leaf5012Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi277InputQChi innerPair108Input
    leaf5012InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5012LowerChecked :
    lowerCheck 24 leaf5012Box leaf5012Inputs = true := by
  rfl'

private theorem leaf5012CoversExact : CoversExact 8
    leaf5012Box leaf5012Certificate leaf5012InnerLog leaf5012Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi277RoundedFacts
    innerPair108RoundedFacts leaf5012RoundedFacts (by rfl)

private theorem leaf5012FlatSound : Sound leaf5012Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5012CertificateValid
    leaf5012InnerLogValid leaf5012CoversExact leaf5012LowerChecked

private noncomputable def leaf5013Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5013Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715303424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2121565113/1073741824) }, upper := { exponent := 0, mantissa := (16343/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432715775/137430606848) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5013InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5013LocalValidity :
    LeafFacts leaf5013Box leaf5013Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5013Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715303424) }) = true
      norm_num [leaf5013Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5013CertificateValid :
    WideCertificateValid leaf5013Box leaf5013Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi278ValidityFacts
    leaf5013LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5013CoverageChecked :
    coverageCheck (innerAD leaf5013Box) leaf5013InnerLog = true := by
  rfl'

private theorem leaf5013InnerLogValid :
    leaf5013InnerLog.Valid 8 (innerAD leaf5013Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5013CoverageChecked

private noncomputable def leaf5013InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5013InputLogOnePlusV_eq :
    leaf5013InputLogOnePlusV = outerEnclosure 24
      (leaf5013Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5013RoundedFacts : LeafRoundedFacts 8
    leaf5013Certificate.logOnePlusV leaf5013InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5013InputLogOnePlusV_eq }

private noncomputable def leaf5013Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi278InputQChi innerPair108Input
    leaf5013InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5013LowerChecked :
    lowerCheck 24 leaf5013Box leaf5013Inputs = true := by
  rfl'

private theorem leaf5013CoversExact : CoversExact 8
    leaf5013Box leaf5013Certificate leaf5013InnerLog leaf5013Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf5013RoundedFacts (by rfl)

private theorem leaf5013FlatSound : Sound leaf5013Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5013CertificateValid
    leaf5013InnerLogValid leaf5013CoversExact leaf5013LowerChecked

private noncomputable def leaf5014Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf5014Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816469504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2125824691/1073741824) }, upper := { exponent := 0, mantissa := (2047/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633242697/19632939008) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5014InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf5014LocalValidity :
    LeafFacts leaf5014Box leaf5014Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5014Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816469504) }) = true
      norm_num [leaf5014Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5014CertificateValid :
    WideCertificateValid leaf5014Box leaf5014Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi278ValidityFacts
    leaf5014LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5014CoverageChecked :
    coverageCheck (innerAD leaf5014Box) leaf5014InnerLog = true := by
  rfl'

private theorem leaf5014InnerLogValid :
    leaf5014InnerLog.Valid 8 (innerAD leaf5014Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf5014CoverageChecked

private noncomputable def leaf5014InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5014InputLogOnePlusV_eq :
    leaf5014InputLogOnePlusV = outerEnclosure 24
      (leaf5014Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5014RoundedFacts : LeafRoundedFacts 8
    leaf5014Certificate.logOnePlusV leaf5014InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5014InputLogOnePlusV_eq }

private noncomputable def leaf5014Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi278InputQChi innerPair108Input
    leaf5014InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5014LowerChecked :
    lowerCheck 24 leaf5014Box leaf5014Inputs = true := by
  rfl'

private theorem leaf5014CoversExact : CoversExact 8
    leaf5014Box leaf5014Certificate leaf5014InnerLog leaf5014Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi278RoundedFacts
    innerPair108RoundedFacts leaf5014RoundedFacts (by rfl)

private theorem leaf5014FlatSound : Sound leaf5014Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5014CertificateValid
    leaf5014InnerLogValid leaf5014CoversExact leaf5014LowerChecked

private noncomputable def leaf5015Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5015Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715274496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2129035763/1073741824) }, upper := { exponent := 1, mantissa := (32799/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432686847/137430548992) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5015InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf5015LocalValidity :
    LeafFacts leaf5015Box leaf5015Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5015Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715274496) }) = true
      norm_num [leaf5015Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5015CertificateValid :
    WideCertificateValid leaf5015Box leaf5015Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi275ValidityFacts
    leaf5015LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5015CoverageChecked :
    coverageCheck (innerAD leaf5015Box) leaf5015InnerLog = true := by
  rfl'

private theorem leaf5015InnerLogValid :
    leaf5015InnerLog.Valid 8 (innerAD leaf5015Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf5015CoverageChecked

private noncomputable def leaf5015InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5015InputLogOnePlusV_eq :
    leaf5015InputLogOnePlusV = outerEnclosure 24
      (leaf5015Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5015RoundedFacts : LeafRoundedFacts 8
    leaf5015Certificate.logOnePlusV leaf5015InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5015InputLogOnePlusV_eq }

private noncomputable def leaf5015Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi275InputQChi innerPair321Input
    leaf5015InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5015LowerChecked :
    lowerCheck 24 leaf5015Box leaf5015Inputs = true := by
  rfl'

private theorem leaf5015CoversExact : CoversExact 8
    leaf5015Box leaf5015Certificate leaf5015InnerLog leaf5015Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi275RoundedFacts
    innerPair321RoundedFacts leaf5015RoundedFacts (by rfl)

private theorem leaf5015FlatSound : Sound leaf5015Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5015CertificateValid
    leaf5015InnerLogValid leaf5015CoversExact leaf5015LowerChecked

private noncomputable def leaf5016Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5016Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715257344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2133360873/1073741824) }, upper := { exponent := 1, mantissa := (16433/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432669695/137430514688) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5016InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5016LocalValidity :
    LeafFacts leaf5016Box leaf5016Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5016Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715257344) }) = true
      norm_num [leaf5016Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5016CertificateValid :
    WideCertificateValid leaf5016Box leaf5016Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi275ValidityFacts
    leaf5016LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5016CoverageChecked :
    coverageCheck (innerAD leaf5016Box) leaf5016InnerLog = true := by
  rfl'

private theorem leaf5016InnerLogValid :
    leaf5016InnerLog.Valid 8 (innerAD leaf5016Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5016CoverageChecked

private noncomputable def leaf5016InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5016InputLogOnePlusV_eq :
    leaf5016InputLogOnePlusV = outerEnclosure 24
      (leaf5016Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5016RoundedFacts : LeafRoundedFacts 8
    leaf5016Certificate.logOnePlusV leaf5016InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5016InputLogOnePlusV_eq }

private noncomputable def leaf5016Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi275InputQChi innerPair533Input
    leaf5016InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5016LowerChecked :
    lowerCheck 24 leaf5016Box leaf5016Inputs = true := by
  rfl'

private theorem leaf5016CoversExact : CoversExact 8
    leaf5016Box leaf5016Certificate leaf5016InnerLog leaf5016Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi275RoundedFacts
    innerPair533RoundedFacts leaf5016RoundedFacts (by rfl)

private theorem leaf5016FlatSound : Sound leaf5016Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5016CertificateValid
    leaf5016InnerLogValid leaf5016CoversExact leaf5016LowerChecked

private noncomputable def leaf5017Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5017Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905070592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2145025569/1073741824) }, upper := { exponent := 1, mantissa := (8261/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810874709/45810141184) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5017InnerLog : WideLogData :=
  innerPair531Data

set_option maxRecDepth 1000000 in
private theorem leaf5017LocalValidity :
    LeafFacts leaf5017Box leaf5017Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5017Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905070592) }) = true
      norm_num [leaf5017Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5017CertificateValid :
    WideCertificateValid leaf5017Box leaf5017Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi276ValidityFacts
    leaf5017LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5017CoverageChecked :
    coverageCheck (innerAD leaf5017Box) leaf5017InnerLog = true := by
  rfl'

private theorem leaf5017InnerLogValid :
    leaf5017InnerLog.Valid 8 (innerAD leaf5017Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint82PositiveFacts.valid leaf5017CoverageChecked

private noncomputable def leaf5017InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5017InputLogOnePlusV_eq :
    leaf5017InputLogOnePlusV = outerEnclosure 24
      (leaf5017Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5017RoundedFacts : LeafRoundedFacts 8
    leaf5017Certificate.logOnePlusV leaf5017InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5017InputLogOnePlusV_eq }

private noncomputable def leaf5017Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi276InputQChi innerPair531Input
    leaf5017InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5017LowerChecked :
    lowerCheck 24 leaf5017Box leaf5017Inputs = true := by
  rfl'

private theorem leaf5017CoversExact : CoversExact 8
    leaf5017Box leaf5017Certificate leaf5017InnerLog leaf5017Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi276RoundedFacts
    innerPair531RoundedFacts leaf5017RoundedFacts (by rfl)

private theorem leaf5017FlatSound : Sound leaf5017Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5017CertificateValid
    leaf5017InnerLogValid leaf5017CoversExact leaf5017LowerChecked

private noncomputable def leaf5018Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5018Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1598079357/1598027776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2149416211/2147483648) }, upper := { exponent := 1, mantissa := (4139/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3196107133/3196055552) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5018InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5018LocalValidity :
    LeafFacts leaf5018Box leaf5018Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5018Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1598079357/1598027776) }) = true
      norm_num [leaf5018Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5018CertificateValid :
    WideCertificateValid leaf5018Box leaf5018Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi276ValidityFacts
    leaf5018LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5018CoverageChecked :
    coverageCheck (innerAD leaf5018Box) leaf5018InnerLog = true := by
  rfl'

private theorem leaf5018InnerLogValid :
    leaf5018InnerLog.Valid 8 (innerAD leaf5018Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5018CoverageChecked

private noncomputable def leaf5018InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5018InputLogOnePlusV_eq :
    leaf5018InputLogOnePlusV = outerEnclosure 24
      (leaf5018Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5018RoundedFacts : LeafRoundedFacts 8
    leaf5018Certificate.logOnePlusV leaf5018InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5018InputLogOnePlusV_eq }

private noncomputable def leaf5018Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi276InputQChi innerPair119Input
    leaf5018InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5018LowerChecked :
    lowerCheck 24 leaf5018Box leaf5018Inputs = true := by
  rfl'

private theorem leaf5018CoversExact : CoversExact 8
    leaf5018Box leaf5018Certificate leaf5018InnerLog leaf5018Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi276RoundedFacts
    innerPair119RoundedFacts leaf5018RoundedFacts (by rfl)

private theorem leaf5018FlatSound : Sound leaf5018Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5018CertificateValid
    leaf5018InnerLogValid leaf5018CoversExact leaf5018LowerChecked

private noncomputable def leaf5019Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5019Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635026688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2137685983/1073741824) }, upper := { exponent := 1, mantissa := (32933/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270294727/15270053376) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5019InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5019LocalValidity :
    LeafFacts leaf5019Box leaf5019Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5019Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635026688) }) = true
      norm_num [leaf5019Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5019CertificateValid :
    WideCertificateValid leaf5019Box leaf5019Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi275ValidityFacts
    leaf5019LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5019CoverageChecked :
    coverageCheck (innerAD leaf5019Box) leaf5019InnerLog = true := by
  rfl'

private theorem leaf5019InnerLogValid :
    leaf5019InnerLog.Valid 8 (innerAD leaf5019Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5019CoverageChecked

private noncomputable def leaf5019InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5019InputLogOnePlusV_eq :
    leaf5019InputLogOnePlusV = outerEnclosure 24
      (leaf5019Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5019RoundedFacts : LeafRoundedFacts 8
    leaf5019Certificate.logOnePlusV leaf5019InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5019InputLogOnePlusV_eq }

private noncomputable def leaf5019Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi275InputQChi innerPair533Input
    leaf5019InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5019LowerChecked :
    lowerCheck 24 leaf5019Box leaf5019Inputs = true := by
  rfl'

private theorem leaf5019CoversExact : CoversExact 8
    leaf5019Box leaf5019Certificate leaf5019InnerLog leaf5019Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi275RoundedFacts
    innerPair533RoundedFacts leaf5019RoundedFacts (by rfl)

private theorem leaf5019FlatSound : Sound leaf5019Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5019CertificateValid
    leaf5019InnerLogValid leaf5019CoversExact leaf5019LowerChecked

private noncomputable def leaf5020Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf5020Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715223040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2142011093/1073741824) }, upper := { exponent := 1, mantissa := (4125/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432635391/137430446080) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5020InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5020LocalValidity :
    LeafFacts leaf5020Box leaf5020Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5020Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715223040) }) = true
      norm_num [leaf5020Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5020CertificateValid :
    WideCertificateValid leaf5020Box leaf5020Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi275ValidityFacts
    leaf5020LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5020CoverageChecked :
    coverageCheck (innerAD leaf5020Box) leaf5020InnerLog = true := by
  rfl'

private theorem leaf5020InnerLogValid :
    leaf5020InnerLog.Valid 8 (innerAD leaf5020Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5020CoverageChecked

private noncomputable def leaf5020InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5020InputLogOnePlusV_eq :
    leaf5020InputLogOnePlusV = outerEnclosure 24
      (leaf5020Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5020RoundedFacts : LeafRoundedFacts 8
    leaf5020Certificate.logOnePlusV leaf5020InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5020InputLogOnePlusV_eq }

private noncomputable def leaf5020Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi275InputQChi innerPair533Input
    leaf5020InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5020LowerChecked :
    lowerCheck 24 leaf5020Box leaf5020Inputs = true := by
  rfl'

private theorem leaf5020CoversExact : CoversExact 8
    leaf5020Box leaf5020Certificate leaf5020InnerLog leaf5020Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi275RoundedFacts
    innerPair533RoundedFacts leaf5020RoundedFacts (by rfl)

private theorem leaf5020FlatSound : Sound leaf5020Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5020CertificateValid
    leaf5020InnerLogValid leaf5020CoversExact leaf5020LowerChecked

private noncomputable def leaf5021Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5021Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715176960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2153806853/2147483648) }, upper := { exponent := 1, mantissa := (8295/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432589311/137430353920) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5021InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5021LocalValidity :
    LeafFacts leaf5021Box leaf5021Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5021Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715176960) }) = true
      norm_num [leaf5021Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5021CertificateValid :
    WideCertificateValid leaf5021Box leaf5021Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi276ValidityFacts
    leaf5021LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5021CoverageChecked :
    coverageCheck (innerAD leaf5021Box) leaf5021InnerLog = true := by
  rfl'

private theorem leaf5021InnerLogValid :
    leaf5021InnerLog.Valid 8 (innerAD leaf5021Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5021CoverageChecked

private noncomputable def leaf5021InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5021InputLogOnePlusV_eq :
    leaf5021InputLogOnePlusV = outerEnclosure 24
      (leaf5021Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5021RoundedFacts : LeafRoundedFacts 8
    leaf5021Certificate.logOnePlusV leaf5021InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5021InputLogOnePlusV_eq }

private noncomputable def leaf5021Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi276InputQChi innerPair119Input
    leaf5021InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5021LowerChecked :
    lowerCheck 24 leaf5021Box leaf5021Inputs = true := by
  rfl'

private theorem leaf5021CoversExact : CoversExact 8
    leaf5021Box leaf5021Certificate leaf5021InnerLog leaf5021Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi276RoundedFacts
    innerPair119RoundedFacts leaf5021RoundedFacts (by rfl)

private theorem leaf5021FlatSound : Sound leaf5021Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5021CertificateValid
    leaf5021InnerLogValid leaf5021CoversExact leaf5021LowerChecked

private noncomputable def leaf5022Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf5022Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635017728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2158197495/2147483648) }, upper := { exponent := 1, mantissa := (1039/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270285767/15270035456) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5022InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5022LocalValidity :
    LeafFacts leaf5022Box leaf5022Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5022Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635017728) }) = true
      norm_num [leaf5022Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5022CertificateValid :
    WideCertificateValid leaf5022Box leaf5022Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi276ValidityFacts
    leaf5022LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5022CoverageChecked :
    coverageCheck (innerAD leaf5022Box) leaf5022InnerLog = true := by
  rfl'

private theorem leaf5022InnerLogValid :
    leaf5022InnerLog.Valid 8 (innerAD leaf5022Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5022CoverageChecked

private noncomputable def leaf5022InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5022InputLogOnePlusV_eq :
    leaf5022InputLogOnePlusV = outerEnclosure 24
      (leaf5022Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5022RoundedFacts : LeafRoundedFacts 8
    leaf5022Certificate.logOnePlusV leaf5022InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5022InputLogOnePlusV_eq }

private noncomputable def leaf5022Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi276InputQChi innerPair119Input
    leaf5022InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5022LowerChecked :
    lowerCheck 24 leaf5022Box leaf5022Inputs = true := by
  rfl'

private theorem leaf5022CoversExact : CoversExact 8
    leaf5022Box leaf5022Certificate leaf5022InnerLog leaf5022Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi276RoundedFacts
    innerPair119RoundedFacts leaf5022RoundedFacts (by rfl)

private theorem leaf5022FlatSound : Sound leaf5022Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5022CertificateValid
    leaf5022InnerLogValid leaf5022CoversExact leaf5022LowerChecked

private noncomputable def leaf5023Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5023Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715219712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2143190679/1073741824) }, upper := { exponent := 1, mantissa := (33013/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432632063/137430439424) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5023InnerLog : WideLogData :=
  innerPair533Data

set_option maxRecDepth 1000000 in
private theorem leaf5023LocalValidity :
    LeafFacts leaf5023Box leaf5023Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5023Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715219712) }) = true
      norm_num [leaf5023Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5023CertificateValid :
    WideCertificateValid leaf5023Box leaf5023Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi257ValidityFacts
    leaf5023LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5023CoverageChecked :
    coverageCheck (innerAD leaf5023Box) leaf5023InnerLog = true := by
  rfl'

private theorem leaf5023InnerLogValid :
    leaf5023InnerLog.Valid 8 (innerAD leaf5023Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint283PositiveFacts.valid leaf5023CoverageChecked

private noncomputable def leaf5023InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5023InputLogOnePlusV_eq :
    leaf5023InputLogOnePlusV = outerEnclosure 24
      (leaf5023Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5023RoundedFacts : LeafRoundedFacts 8
    leaf5023Certificate.logOnePlusV leaf5023InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5023InputLogOnePlusV_eq }

private noncomputable def leaf5023Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi257InputQChi innerPair533Input
    leaf5023InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5023LowerChecked :
    lowerCheck 24 leaf5023Box leaf5023Inputs = true := by
  rfl'

private theorem leaf5023CoversExact : CoversExact 8
    leaf5023Box leaf5023Certificate leaf5023InnerLog leaf5023Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi257RoundedFacts
    innerPair533RoundedFacts leaf5023RoundedFacts (by rfl)

private theorem leaf5023FlatSound : Sound leaf5023Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5023CertificateValid
    leaf5023InnerLogValid leaf5023CoversExact leaf5023LowerChecked

private noncomputable def leaf5024Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5024Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715202048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2147646853/2147483648) }, upper := { exponent := 1, mantissa := (16541/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432614399/137430404096) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5024InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5024LocalValidity :
    LeafFacts leaf5024Box leaf5024Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5024Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715202048) }) = true
      norm_num [leaf5024Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5024CertificateValid :
    WideCertificateValid leaf5024Box leaf5024Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi257ValidityFacts
    leaf5024LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5024CoverageChecked :
    coverageCheck (innerAD leaf5024Box) leaf5024InnerLog = true := by
  rfl'

private theorem leaf5024InnerLogValid :
    leaf5024InnerLog.Valid 8 (innerAD leaf5024Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5024CoverageChecked

private noncomputable def leaf5024InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5024InputLogOnePlusV_eq :
    leaf5024InputLogOnePlusV = outerEnclosure 24
      (leaf5024Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5024RoundedFacts : LeafRoundedFacts 8
    leaf5024Certificate.logOnePlusV leaf5024InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5024InputLogOnePlusV_eq }

private noncomputable def leaf5024Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi257InputQChi innerPair119Input
    leaf5024InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5024LowerChecked :
    lowerCheck 24 leaf5024Box leaf5024Inputs = true := by
  rfl'

private theorem leaf5024CoversExact : CoversExact 8
    leaf5024Box leaf5024Certificate leaf5024InnerLog leaf5024Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi257RoundedFacts
    innerPair119RoundedFacts leaf5024RoundedFacts (by rfl)

private theorem leaf5024FlatSound : Sound leaf5024Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5024CertificateValid
    leaf5024InnerLogValid leaf5024CoversExact leaf5024LowerChecked

private noncomputable def leaf5025Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5025Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905052672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2158918357/2147483648) }, upper := { exponent := 1, mantissa := (16627/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810856789/45810105344) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5025InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5025LocalValidity :
    LeafFacts leaf5025Box leaf5025Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5025Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905052672) }) = true
      norm_num [leaf5025Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5025CertificateValid :
    WideCertificateValid leaf5025Box leaf5025Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi258ValidityFacts
    leaf5025LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5025CoverageChecked :
    coverageCheck (innerAD leaf5025Box) leaf5025InnerLog = true := by
  rfl'

private theorem leaf5025InnerLogValid :
    leaf5025InnerLog.Valid 8 (innerAD leaf5025Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5025CoverageChecked

private noncomputable def leaf5025InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5025InputLogOnePlusV_eq :
    leaf5025InputLogOnePlusV = outerEnclosure 24
      (leaf5025Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5025RoundedFacts : LeafRoundedFacts 8
    leaf5025Certificate.logOnePlusV leaf5025InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5025InputLogOnePlusV_eq }

private noncomputable def leaf5025Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5025InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5025LowerChecked :
    lowerCheck 24 leaf5025Box leaf5025Inputs = true := by
  rfl'

private theorem leaf5025CoversExact : CoversExact 8
    leaf5025Box leaf5025Certificate leaf5025InnerLog leaf5025Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5025RoundedFacts (by rfl)

private theorem leaf5025FlatSound : Sound leaf5025Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5025CertificateValid
    leaf5025InnerLogValid leaf5025CoversExact leaf5025LowerChecked

private noncomputable def leaf5026Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5026Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715140096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2163440063/2147483648) }, upper := { exponent := 1, mantissa := (8331/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432552447/137430280192) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5026InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5026LocalValidity :
    LeafFacts leaf5026Box leaf5026Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5026Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715140096) }) = true
      norm_num [leaf5026Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5026CertificateValid :
    WideCertificateValid leaf5026Box leaf5026Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi258ValidityFacts
    leaf5026LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5026CoverageChecked :
    coverageCheck (innerAD leaf5026Box) leaf5026InnerLog = true := by
  rfl'

private theorem leaf5026InnerLogValid :
    leaf5026InnerLog.Valid 8 (innerAD leaf5026Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5026CoverageChecked

private noncomputable def leaf5026InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5026InputLogOnePlusV_eq :
    leaf5026InputLogOnePlusV = outerEnclosure 24
      (leaf5026Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5026RoundedFacts : LeafRoundedFacts 8
    leaf5026Certificate.logOnePlusV leaf5026InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5026InputLogOnePlusV_eq }

private noncomputable def leaf5026Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5026InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5026LowerChecked :
    lowerCheck 24 leaf5026Box leaf5026Inputs = true := by
  rfl'

private theorem leaf5026CoversExact : CoversExact 8
    leaf5026Box leaf5026Certificate leaf5026InnerLog leaf5026Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5026RoundedFacts (by rfl)

private theorem leaf5026FlatSound : Sound leaf5026Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5026CertificateValid
    leaf5026InnerLogValid leaf5026CoversExact leaf5026LowerChecked

private noncomputable def leaf5027Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5027Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816454912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2152103027/2147483648) }, upper := { exponent := 1, mantissa := (33151/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633228105/19632909824) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5027InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5027LocalValidity :
    LeafFacts leaf5027Box leaf5027Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5027Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816454912) }) = true
      norm_num [leaf5027Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5027CertificateValid :
    WideCertificateValid leaf5027Box leaf5027Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi257ValidityFacts
    leaf5027LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5027CoverageChecked :
    coverageCheck (innerAD leaf5027Box) leaf5027InnerLog = true := by
  rfl'

private theorem leaf5027InnerLogValid :
    leaf5027InnerLog.Valid 8 (innerAD leaf5027Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5027CoverageChecked

private noncomputable def leaf5027InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5027InputLogOnePlusV_eq :
    leaf5027InputLogOnePlusV = outerEnclosure 24
      (leaf5027Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5027RoundedFacts : LeafRoundedFacts 8
    leaf5027Certificate.logOnePlusV leaf5027InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5027InputLogOnePlusV_eq }

private noncomputable def leaf5027Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi257InputQChi innerPair119Input
    leaf5027InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5027LowerChecked :
    lowerCheck 24 leaf5027Box leaf5027Inputs = true := by
  rfl'

private theorem leaf5027CoversExact : CoversExact 8
    leaf5027Box leaf5027Certificate leaf5027InnerLog leaf5027Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi257RoundedFacts
    innerPair119RoundedFacts leaf5027RoundedFacts (by rfl)

private theorem leaf5027FlatSound : Sound leaf5027Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5027CertificateValid
    leaf5027InnerLogValid leaf5027CoversExact leaf5027LowerChecked

private noncomputable def leaf5028Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5028Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715166720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2156559201/2147483648) }, upper := { exponent := 1, mantissa := (8305/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432579071/137430333440) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5028InnerLog : WideLogData :=
  innerPair119Data

set_option maxRecDepth 1000000 in
private theorem leaf5028LocalValidity :
    LeafFacts leaf5028Box leaf5028Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5028Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715166720) }) = true
      norm_num [leaf5028Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5028CertificateValid :
    WideCertificateValid leaf5028Box leaf5028Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi257ValidityFacts
    leaf5028LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5028CoverageChecked :
    coverageCheck (innerAD leaf5028Box) leaf5028InnerLog = true := by
  rfl'

private theorem leaf5028InnerLogValid :
    leaf5028InnerLog.Valid 8 (innerAD leaf5028Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint82PositiveFacts.valid leaf5028CoverageChecked

private noncomputable def leaf5028InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5028InputLogOnePlusV_eq :
    leaf5028InputLogOnePlusV = outerEnclosure 24
      (leaf5028Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5028RoundedFacts : LeafRoundedFacts 8
    leaf5028Certificate.logOnePlusV leaf5028InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5028InputLogOnePlusV_eq }

private noncomputable def leaf5028Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi257InputQChi innerPair119Input
    leaf5028InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5028LowerChecked :
    lowerCheck 24 leaf5028Box leaf5028Inputs = true := by
  rfl'

private theorem leaf5028CoversExact : CoversExact 8
    leaf5028Box leaf5028Certificate leaf5028InnerLog leaf5028Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi257RoundedFacts
    innerPair119RoundedFacts leaf5028RoundedFacts (by rfl)

private theorem leaf5028FlatSound : Sound leaf5028Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5028CertificateValid
    leaf5028InnerLogValid leaf5028CoversExact leaf5028LowerChecked

private noncomputable def leaf5029Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5029Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715122176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2167961769/2147483648) }, upper := { exponent := 1, mantissa := (16697/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432534527/137430244352) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5029InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5029LocalValidity :
    LeafFacts leaf5029Box leaf5029Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5029Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715122176) }) = true
      norm_num [leaf5029Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5029CertificateValid :
    WideCertificateValid leaf5029Box leaf5029Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi258ValidityFacts
    leaf5029LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5029CoverageChecked :
    coverageCheck (innerAD leaf5029Box) leaf5029InnerLog = true := by
  rfl'

private theorem leaf5029InnerLogValid :
    leaf5029InnerLog.Valid 8 (innerAD leaf5029Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5029CoverageChecked

private noncomputable def leaf5029InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5029InputLogOnePlusV_eq :
    leaf5029InputLogOnePlusV = outerEnclosure 24
      (leaf5029Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5029RoundedFacts : LeafRoundedFacts 8
    leaf5029Certificate.logOnePlusV leaf5029InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5029InputLogOnePlusV_eq }

private noncomputable def leaf5029Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5029InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5029LowerChecked :
    lowerCheck 24 leaf5029Box leaf5029Inputs = true := by
  rfl'

private theorem leaf5029CoversExact : CoversExact 8
    leaf5029Box leaf5029Certificate leaf5029InnerLog leaf5029Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5029RoundedFacts (by rfl)

private theorem leaf5029FlatSound : Sound leaf5029Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5029CertificateValid
    leaf5029InnerLogValid leaf5029CoversExact leaf5029LowerChecked

private noncomputable def leaf5030Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5030Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635011584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2172483475/2147483648) }, upper := { exponent := 1, mantissa := (4183/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270279623/15270023168) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5030InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5030LocalValidity :
    LeafFacts leaf5030Box leaf5030Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5030Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635011584) }) = true
      norm_num [leaf5030Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5030CertificateValid :
    WideCertificateValid leaf5030Box leaf5030Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi258ValidityFacts
    leaf5030LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5030CoverageChecked :
    coverageCheck (innerAD leaf5030Box) leaf5030InnerLog = true := by
  rfl'

private theorem leaf5030InnerLogValid :
    leaf5030InnerLog.Valid 8 (innerAD leaf5030Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5030CoverageChecked

private noncomputable def leaf5030InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5030InputLogOnePlusV_eq :
    leaf5030InputLogOnePlusV = outerEnclosure 24
      (leaf5030Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5030RoundedFacts : LeafRoundedFacts 8
    leaf5030Certificate.logOnePlusV leaf5030InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5030InputLogOnePlusV_eq }

private noncomputable def leaf5030Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5030InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5030LowerChecked :
    lowerCheck 24 leaf5030Box leaf5030Inputs = true := by
  rfl'

private theorem leaf5030CoversExact : CoversExact 8
    leaf5030Box leaf5030Certificate leaf5030InnerLog leaf5030Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5030RoundedFacts (by rfl)

private theorem leaf5030FlatSound : Sound leaf5030Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5030CertificateValid
    leaf5030InnerLogValid leaf5030CoversExact leaf5030LowerChecked

private noncomputable def leaf5031Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5031Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715096320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2174646035/2147483648) }, upper := { exponent := 1, mantissa := (33495/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432508671/137430192640) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5031InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5031LocalValidity :
    LeafFacts leaf5031Box leaf5031Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5031Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715096320) }) = true
      norm_num [leaf5031Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5031CertificateValid :
    WideCertificateValid leaf5031Box leaf5031Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi279ValidityFacts
    leaf5031LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5031CoverageChecked :
    coverageCheck (innerAD leaf5031Box) leaf5031InnerLog = true := by
  rfl'

private theorem leaf5031InnerLogValid :
    leaf5031InnerLog.Valid 8 (innerAD leaf5031Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5031CoverageChecked

private noncomputable def leaf5031InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5031InputLogOnePlusV_eq :
    leaf5031InputLogOnePlusV = outerEnclosure 24
      (leaf5031Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5031RoundedFacts : LeafRoundedFacts 8
    leaf5031Certificate.logOnePlusV leaf5031InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5031InputLogOnePlusV_eq }

private noncomputable def leaf5031Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi279InputQChi innerPair116Input
    leaf5031InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5031LowerChecked :
    lowerCheck 24 leaf5031Box leaf5031Inputs = true := by
  rfl'

private theorem leaf5031CoversExact : CoversExact 8
    leaf5031Box leaf5031Certificate leaf5031InnerLog leaf5031Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf5031RoundedFacts (by rfl)

private theorem leaf5031FlatSound : Sound leaf5031Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5031CertificateValid
    leaf5031InnerLogValid leaf5031CoversExact leaf5031LowerChecked

private noncomputable def leaf5032Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5032Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (738896907/738871808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2179233273/2147483648) }, upper := { exponent := 1, mantissa := (16783/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1477768715/1477743616) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5032InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5032LocalValidity :
    LeafFacts leaf5032Box leaf5032Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5032Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (738896907/738871808) }) = true
      norm_num [leaf5032Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5032CertificateValid :
    WideCertificateValid leaf5032Box leaf5032Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi279ValidityFacts
    leaf5032LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5032CoverageChecked :
    coverageCheck (innerAD leaf5032Box) leaf5032InnerLog = true := by
  rfl'

private theorem leaf5032InnerLogValid :
    leaf5032InnerLog.Valid 8 (innerAD leaf5032Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5032CoverageChecked

private noncomputable def leaf5032InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5032InputLogOnePlusV_eq :
    leaf5032InputLogOnePlusV = outerEnclosure 24
      (leaf5032Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5032RoundedFacts : LeafRoundedFacts 8
    leaf5032Certificate.logOnePlusV leaf5032InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5032InputLogOnePlusV_eq }

private noncomputable def leaf5032Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi279InputQChi innerPair116Input
    leaf5032InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5032LowerChecked :
    lowerCheck 24 leaf5032Box leaf5032Inputs = true := by
  rfl'

private theorem leaf5032CoversExact : CoversExact 8
    leaf5032Box leaf5032Certificate leaf5032InnerLog leaf5032Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf5032RoundedFacts (by rfl)

private theorem leaf5032FlatSound : Sound leaf5032Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5032CertificateValid
    leaf5032InnerLogValid leaf5032CoversExact leaf5032LowerChecked

private noncomputable def leaf5033Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5033Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715034624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2190373713/2147483648) }, upper := { exponent := 1, mantissa := (4217/4096) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432446975/137430069248) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5033InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5033LocalValidity :
    LeafFacts leaf5033Box leaf5033Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5033Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715034624) }) = true
      norm_num [leaf5033Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5033CertificateValid :
    WideCertificateValid leaf5033Box leaf5033Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi280ValidityFacts
    leaf5033LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5033CoverageChecked :
    coverageCheck (innerAD leaf5033Box) leaf5033InnerLog = true := by
  rfl'

private theorem leaf5033InnerLogValid :
    leaf5033InnerLog.Valid 8 (innerAD leaf5033Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5033CoverageChecked

private noncomputable def leaf5033InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5033InputLogOnePlusV_eq :
    leaf5033InputLogOnePlusV = outerEnclosure 24
      (leaf5033Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5033RoundedFacts : LeafRoundedFacts 8
    leaf5033Certificate.logOnePlusV leaf5033InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5033InputLogOnePlusV_eq }

private noncomputable def leaf5033Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi280InputQChi innerPair116Input
    leaf5033InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5033LowerChecked :
    lowerCheck 24 leaf5033Box leaf5033Inputs = true := by
  rfl'

private theorem leaf5033CoversExact : CoversExact 8
    leaf5033Box leaf5033Certificate leaf5033InnerLog leaf5033Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf5033RoundedFacts (by rfl)

private theorem leaf5033FlatSound : Sound leaf5033Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5033CertificateValid
    leaf5033InnerLogValid leaf5033CoversExact leaf5033LowerChecked

private noncomputable def leaf5034Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5034Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715016192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2195026483/2147483648) }, upper := { exponent := 1, mantissa := (2113/2048) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432428543/137430032384) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5034InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf5034LocalValidity :
    LeafFacts leaf5034Box leaf5034Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5034Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715016192) }) = true
      norm_num [leaf5034Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5034CertificateValid :
    WideCertificateValid leaf5034Box leaf5034Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi280ValidityFacts
    leaf5034LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5034CoverageChecked :
    coverageCheck (innerAD leaf5034Box) leaf5034InnerLog = true := by
  rfl'

private theorem leaf5034InnerLogValid :
    leaf5034InnerLog.Valid 8 (innerAD leaf5034Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf5034CoverageChecked

private noncomputable def leaf5034InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5034InputLogOnePlusV_eq :
    leaf5034InputLogOnePlusV = outerEnclosure 24
      (leaf5034Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5034RoundedFacts : LeafRoundedFacts 8
    leaf5034Certificate.logOnePlusV leaf5034InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5034InputLogOnePlusV_eq }

private noncomputable def leaf5034Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi280InputQChi innerPair311Input
    leaf5034InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5034LowerChecked :
    lowerCheck 24 leaf5034Box leaf5034Inputs = true := by
  rfl'

private theorem leaf5034CoversExact : CoversExact 8
    leaf5034Box leaf5034Certificate leaf5034InnerLog leaf5034Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi280RoundedFacts
    innerPair311RoundedFacts leaf5034RoundedFacts (by rfl)

private theorem leaf5034FlatSound : Sound leaf5034Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5034CertificateValid
    leaf5034InnerLogValid leaf5034CoversExact leaf5034LowerChecked

private noncomputable def leaf5035Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5035Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715059968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2183820511/2147483648) }, upper := { exponent := 1, mantissa := (33637/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432472319/137430119936) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5035InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5035LocalValidity :
    LeafFacts leaf5035Box leaf5035Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5035Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715059968) }) = true
      norm_num [leaf5035Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5035CertificateValid :
    WideCertificateValid leaf5035Box leaf5035Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi279ValidityFacts
    leaf5035LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5035CoverageChecked :
    coverageCheck (innerAD leaf5035Box) leaf5035InnerLog = true := by
  rfl'

private theorem leaf5035InnerLogValid :
    leaf5035InnerLog.Valid 8 (innerAD leaf5035Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5035CoverageChecked

private noncomputable def leaf5035InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5035InputLogOnePlusV_eq :
    leaf5035InputLogOnePlusV = outerEnclosure 24
      (leaf5035Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5035RoundedFacts : LeafRoundedFacts 8
    leaf5035Certificate.logOnePlusV leaf5035InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5035InputLogOnePlusV_eq }

private noncomputable def leaf5035Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi279InputQChi innerPair116Input
    leaf5035InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5035LowerChecked :
    lowerCheck 24 leaf5035Box leaf5035Inputs = true := by
  rfl'

private theorem leaf5035CoversExact : CoversExact 8
    leaf5035Box leaf5035Certificate leaf5035InnerLog leaf5035Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf5035RoundedFacts (by rfl)

private theorem leaf5035FlatSound : Sound leaf5035Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5035CertificateValid
    leaf5035InnerLogValid leaf5035CoversExact leaf5035LowerChecked

private noncomputable def leaf5036Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5036Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715041792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2188407749/2147483648) }, upper := { exponent := 1, mantissa := (8427/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432454143/137430083584) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5036InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5036LocalValidity :
    LeafFacts leaf5036Box leaf5036Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5036Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715041792) }) = true
      norm_num [leaf5036Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5036CertificateValid :
    WideCertificateValid leaf5036Box leaf5036Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi279ValidityFacts
    leaf5036LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5036CoverageChecked :
    coverageCheck (innerAD leaf5036Box) leaf5036InnerLog = true := by
  rfl'

private theorem leaf5036InnerLogValid :
    leaf5036InnerLog.Valid 8 (innerAD leaf5036Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5036CoverageChecked

private noncomputable def leaf5036InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5036InputLogOnePlusV_eq :
    leaf5036InputLogOnePlusV = outerEnclosure 24
      (leaf5036Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5036RoundedFacts : LeafRoundedFacts 8
    leaf5036Certificate.logOnePlusV leaf5036InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5036InputLogOnePlusV_eq }

private noncomputable def leaf5036Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi279InputQChi innerPair116Input
    leaf5036InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5036LowerChecked :
    lowerCheck 24 leaf5036Box leaf5036Inputs = true := by
  rfl'

private theorem leaf5036CoversExact : CoversExact 8
    leaf5036Box leaf5036Certificate leaf5036InnerLog leaf5036Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf5036RoundedFacts (by rfl)

private theorem leaf5036FlatSound : Sound leaf5036Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5036CertificateValid
    leaf5036InnerLogValid leaf5036CoversExact leaf5036LowerChecked

private noncomputable def leaf5037Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5037Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714997760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2199679253/2147483648) }, upper := { exponent := 1, mantissa := (4235/4096) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432410111/137429995520) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5037InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5037LocalValidity :
    LeafFacts leaf5037Box leaf5037Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5037Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714997760) }) = true
      norm_num [leaf5037Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5037CertificateValid :
    WideCertificateValid leaf5037Box leaf5037Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi280ValidityFacts
    leaf5037LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5037CoverageChecked :
    coverageCheck (innerAD leaf5037Box) leaf5037InnerLog = true := by
  rfl'

private theorem leaf5037InnerLogValid :
    leaf5037InnerLog.Valid 8 (innerAD leaf5037Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5037CoverageChecked

private noncomputable def leaf5037InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf5037InputLogOnePlusV_eq :
    leaf5037InputLogOnePlusV = outerEnclosure 24
      (leaf5037Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5037RoundedFacts : LeafRoundedFacts 8
    leaf5037Certificate.logOnePlusV leaf5037InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5037InputLogOnePlusV_eq }

private noncomputable def leaf5037Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi280InputQChi innerPair327Input
    leaf5037InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5037LowerChecked :
    lowerCheck 24 leaf5037Box leaf5037Inputs = true := by
  rfl'

private theorem leaf5037CoversExact : CoversExact 8
    leaf5037Box leaf5037Certificate leaf5037InnerLog leaf5037Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi280RoundedFacts
    innerPair327RoundedFacts leaf5037RoundedFacts (by rfl)

private theorem leaf5037FlatSound : Sound leaf5037Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5037CertificateValid
    leaf5037InnerLogValid leaf5037CoversExact leaf5037LowerChecked

private noncomputable def leaf5038Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5038Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714979328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2204332023/2147483648) }, upper := { exponent := 1, mantissa := (1061/1024) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432391679/137429958656) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5038InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5038LocalValidity :
    LeafFacts leaf5038Box leaf5038Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5038Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714979328) }) = true
      norm_num [leaf5038Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5038CertificateValid :
    WideCertificateValid leaf5038Box leaf5038Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi280ValidityFacts
    leaf5038LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5038CoverageChecked :
    coverageCheck (innerAD leaf5038Box) leaf5038InnerLog = true := by
  rfl'

private theorem leaf5038InnerLogValid :
    leaf5038InnerLog.Valid 8 (innerAD leaf5038Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5038CoverageChecked

private noncomputable def leaf5038InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5038InputLogOnePlusV_eq :
    leaf5038InputLogOnePlusV = outerEnclosure 24
      (leaf5038Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5038RoundedFacts : LeafRoundedFacts 8
    leaf5038Certificate.logOnePlusV leaf5038InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5038InputLogOnePlusV_eq }

private noncomputable def leaf5038Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi280InputQChi innerPair327Input
    leaf5038InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5038LowerChecked :
    lowerCheck 24 leaf5038Box leaf5038Inputs = true := by
  rfl'

private theorem leaf5038CoversExact : CoversExact 8
    leaf5038Box leaf5038Certificate leaf5038InnerLog leaf5038Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi280RoundedFacts
    innerPair327RoundedFacts leaf5038RoundedFacts (by rfl)

private theorem leaf5038FlatSound : Sound leaf5038Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5038CertificateValid
    leaf5038InnerLogValid leaf5038CoversExact leaf5038LowerChecked

private noncomputable def leaf5039Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5039Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715149056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2161015375/2147483648) }, upper := { exponent := 1, mantissa := (33289/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432561407/137430298112) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5039InnerLog : WideLogData :=
  innerPair121Data

set_option maxRecDepth 1000000 in
private theorem leaf5039LocalValidity :
    LeafFacts leaf5039Box leaf5039Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5039Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715149056) }) = true
      norm_num [leaf5039Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5039CertificateValid :
    WideCertificateValid leaf5039Box leaf5039Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi257ValidityFacts
    leaf5039LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5039CoverageChecked :
    coverageCheck (innerAD leaf5039Box) leaf5039InnerLog = true := by
  rfl'

private theorem leaf5039InnerLogValid :
    leaf5039InnerLog.Valid 8 (innerAD leaf5039Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint87PositiveFacts.valid leaf5039CoverageChecked

private noncomputable def leaf5039InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5039InputLogOnePlusV_eq :
    leaf5039InputLogOnePlusV = outerEnclosure 24
      (leaf5039Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5039RoundedFacts : LeafRoundedFacts 8
    leaf5039Certificate.logOnePlusV leaf5039InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5039InputLogOnePlusV_eq }

private noncomputable def leaf5039Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi257InputQChi innerPair121Input
    leaf5039InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5039LowerChecked :
    lowerCheck 24 leaf5039Box leaf5039Inputs = true := by
  rfl'

private theorem leaf5039CoversExact : CoversExact 8
    leaf5039Box leaf5039Certificate leaf5039InnerLog leaf5039Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi257RoundedFacts
    innerPair121RoundedFacts leaf5039RoundedFacts (by rfl)

private theorem leaf5039FlatSound : Sound leaf5039Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5039CertificateValid
    leaf5039InnerLogValid leaf5039CoversExact leaf5039LowerChecked

private noncomputable def leaf5040Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5040Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715131392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2165471549/2147483648) }, upper := { exponent := 1, mantissa := (16679/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432543743/137430262784) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5040InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5040LocalValidity :
    LeafFacts leaf5040Box leaf5040Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5040Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715131392) }) = true
      norm_num [leaf5040Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5040CertificateValid :
    WideCertificateValid leaf5040Box leaf5040Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi257ValidityFacts
    leaf5040LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5040CoverageChecked :
    coverageCheck (innerAD leaf5040Box) leaf5040InnerLog = true := by
  rfl'

private theorem leaf5040InnerLogValid :
    leaf5040InnerLog.Valid 8 (innerAD leaf5040Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5040CoverageChecked

private noncomputable def leaf5040InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5040InputLogOnePlusV_eq :
    leaf5040InputLogOnePlusV = outerEnclosure 24
      (leaf5040Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5040RoundedFacts : LeafRoundedFacts 8
    leaf5040Certificate.logOnePlusV leaf5040InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5040InputLogOnePlusV_eq }

private noncomputable def leaf5040Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi257InputQChi innerPair116Input
    leaf5040InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5040LowerChecked :
    lowerCheck 24 leaf5040Box leaf5040Inputs = true := by
  rfl'

private theorem leaf5040CoversExact : CoversExact 8
    leaf5040Box leaf5040Certificate leaf5040InnerLog leaf5040Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi257RoundedFacts
    innerPair116RoundedFacts leaf5040RoundedFacts (by rfl)

private theorem leaf5040FlatSound : Sound leaf5040Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5040CertificateValid
    leaf5040InnerLogValid leaf5040CoversExact leaf5040LowerChecked

private noncomputable def leaf5041Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5041Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715086336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2177005181/2147483648) }, upper := { exponent := 1, mantissa := (16767/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432498687/137430172672) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5041InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5041LocalValidity :
    LeafFacts leaf5041Box leaf5041Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5041Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715086336) }) = true
      norm_num [leaf5041Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5041CertificateValid :
    WideCertificateValid leaf5041Box leaf5041Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi258ValidityFacts
    leaf5041LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5041CoverageChecked :
    coverageCheck (innerAD leaf5041Box) leaf5041InnerLog = true := by
  rfl'

private theorem leaf5041InnerLogValid :
    leaf5041InnerLog.Valid 8 (innerAD leaf5041Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5041CoverageChecked

private noncomputable def leaf5041InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5041InputLogOnePlusV_eq :
    leaf5041InputLogOnePlusV = outerEnclosure 24
      (leaf5041Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5041RoundedFacts : LeafRoundedFacts 8
    leaf5041Certificate.logOnePlusV leaf5041InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5041InputLogOnePlusV_eq }

private noncomputable def leaf5041Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5041InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5041LowerChecked :
    lowerCheck 24 leaf5041Box leaf5041Inputs = true := by
  rfl'

private theorem leaf5041CoversExact : CoversExact 8
    leaf5041Box leaf5041Certificate leaf5041InnerLog leaf5041Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5041RoundedFacts (by rfl)

private theorem leaf5041FlatSound : Sound leaf5041Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5041CertificateValid
    leaf5041InnerLogValid leaf5041CoversExact leaf5041LowerChecked

private noncomputable def leaf5042Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5042Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715068416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2181526887/2147483648) }, upper := { exponent := 1, mantissa := (8401/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432480767/137430136832) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5042InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5042LocalValidity :
    LeafFacts leaf5042Box leaf5042Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5042Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715068416) }) = true
      norm_num [leaf5042Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5042CertificateValid :
    WideCertificateValid leaf5042Box leaf5042Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi258ValidityFacts
    leaf5042LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5042CoverageChecked :
    coverageCheck (innerAD leaf5042Box) leaf5042InnerLog = true := by
  rfl'

private theorem leaf5042InnerLogValid :
    leaf5042InnerLog.Valid 8 (innerAD leaf5042Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5042CoverageChecked

private noncomputable def leaf5042InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5042InputLogOnePlusV_eq :
    leaf5042InputLogOnePlusV = outerEnclosure 24
      (leaf5042Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5042RoundedFacts : LeafRoundedFacts 8
    leaf5042Certificate.logOnePlusV leaf5042InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5042InputLogOnePlusV_eq }

private noncomputable def leaf5042Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5042InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5042LowerChecked :
    lowerCheck 24 leaf5042Box leaf5042Inputs = true := by
  rfl'

private theorem leaf5042CoversExact : CoversExact 8
    leaf5042Box leaf5042Certificate leaf5042InnerLog leaf5042Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5042RoundedFacts (by rfl)

private theorem leaf5042FlatSound : Sound leaf5042Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5042CertificateValid
    leaf5042InnerLogValid leaf5042CoversExact leaf5042LowerChecked

private noncomputable def leaf5043Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5043Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715113728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2169927723/2147483648) }, upper := { exponent := 1, mantissa := (33427/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432526079/137430227456) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5043InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5043LocalValidity :
    LeafFacts leaf5043Box leaf5043Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5043Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715113728) }) = true
      norm_num [leaf5043Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5043CertificateValid :
    WideCertificateValid leaf5043Box leaf5043Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi257ValidityFacts
    leaf5043LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5043CoverageChecked :
    coverageCheck (innerAD leaf5043Box) leaf5043InnerLog = true := by
  rfl'

private theorem leaf5043InnerLogValid :
    leaf5043InnerLog.Valid 8 (innerAD leaf5043Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5043CoverageChecked

private noncomputable def leaf5043InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5043InputLogOnePlusV_eq :
    leaf5043InputLogOnePlusV = outerEnclosure 24
      (leaf5043Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5043RoundedFacts : LeafRoundedFacts 8
    leaf5043Certificate.logOnePlusV leaf5043InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5043InputLogOnePlusV_eq }

private noncomputable def leaf5043Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi257InputQChi innerPair116Input
    leaf5043InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5043LowerChecked :
    lowerCheck 24 leaf5043Box leaf5043Inputs = true := by
  rfl'

private theorem leaf5043CoversExact : CoversExact 8
    leaf5043Box leaf5043Certificate leaf5043InnerLog leaf5043Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi257RoundedFacts
    innerPair116RoundedFacts leaf5043RoundedFacts (by rfl)

private theorem leaf5043FlatSound : Sound leaf5043Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5043CertificateValid
    leaf5043InnerLogValid leaf5043CoversExact leaf5043LowerChecked

private noncomputable def leaf5044Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf5044Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715096064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2174383897/2147483648) }, upper := { exponent := 1, mantissa := (4187/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432508415/137430192128) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5044InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5044LocalValidity :
    LeafFacts leaf5044Box leaf5044Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5044Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715096064) }) = true
      norm_num [leaf5044Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5044CertificateValid :
    WideCertificateValid leaf5044Box leaf5044Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi257ValidityFacts
    leaf5044LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5044CoverageChecked :
    coverageCheck (innerAD leaf5044Box) leaf5044InnerLog = true := by
  rfl'

private theorem leaf5044InnerLogValid :
    leaf5044InnerLog.Valid 8 (innerAD leaf5044Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5044CoverageChecked

private noncomputable def leaf5044InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5044InputLogOnePlusV_eq :
    leaf5044InputLogOnePlusV = outerEnclosure 24
      (leaf5044Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5044RoundedFacts : LeafRoundedFacts 8
    leaf5044Certificate.logOnePlusV leaf5044InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5044InputLogOnePlusV_eq }

private noncomputable def leaf5044Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi257InputQChi innerPair116Input
    leaf5044InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5044LowerChecked :
    lowerCheck 24 leaf5044Box leaf5044Inputs = true := by
  rfl'

private theorem leaf5044CoversExact : CoversExact 8
    leaf5044Box leaf5044Certificate leaf5044InnerLog leaf5044Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi257RoundedFacts
    innerPair116RoundedFacts leaf5044RoundedFacts (by rfl)

private theorem leaf5044FlatSound : Sound leaf5044Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5044CertificateValid
    leaf5044InnerLogValid leaf5044CoversExact leaf5044LowerChecked

private noncomputable def leaf5045Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5045Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905016832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2186048593/2147483648) }, upper := { exponent := 1, mantissa := (16837/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810820949/45810033664) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5045InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5045LocalValidity :
    LeafFacts leaf5045Box leaf5045Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5045Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905016832) }) = true
      norm_num [leaf5045Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5045CertificateValid :
    WideCertificateValid leaf5045Box leaf5045Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi258ValidityFacts
    leaf5045LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5045CoverageChecked :
    coverageCheck (innerAD leaf5045Box) leaf5045InnerLog = true := by
  rfl'

private theorem leaf5045InnerLogValid :
    leaf5045InnerLog.Valid 8 (innerAD leaf5045Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5045CoverageChecked

private noncomputable def leaf5045InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5045InputLogOnePlusV_eq :
    leaf5045InputLogOnePlusV = outerEnclosure 24
      (leaf5045Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5045RoundedFacts : LeafRoundedFacts 8
    leaf5045Certificate.logOnePlusV leaf5045InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5045InputLogOnePlusV_eq }

private noncomputable def leaf5045Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5045InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5045LowerChecked :
    lowerCheck 24 leaf5045Box leaf5045Inputs = true := by
  rfl'

private theorem leaf5045CoversExact : CoversExact 8
    leaf5045Box leaf5045Certificate leaf5045InnerLog leaf5045Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5045RoundedFacts (by rfl)

private theorem leaf5045FlatSound : Sound leaf5045Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5045CertificateValid
    leaf5045InnerLogValid leaf5045CoversExact leaf5045LowerChecked

private noncomputable def leaf5046Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf5046Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715032576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2190570299/2147483648) }, upper := { exponent := 1, mantissa := (2109/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432444927/137430065152) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5046InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5046LocalValidity :
    LeafFacts leaf5046Box leaf5046Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5046Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715032576) }) = true
      norm_num [leaf5046Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5046CertificateValid :
    WideCertificateValid leaf5046Box leaf5046Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi258ValidityFacts
    leaf5046LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5046CoverageChecked :
    coverageCheck (innerAD leaf5046Box) leaf5046InnerLog = true := by
  rfl'

private theorem leaf5046InnerLogValid :
    leaf5046InnerLog.Valid 8 (innerAD leaf5046Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5046CoverageChecked

private noncomputable def leaf5046InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5046InputLogOnePlusV_eq :
    leaf5046InputLogOnePlusV = outerEnclosure 24
      (leaf5046Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5046RoundedFacts : LeafRoundedFacts 8
    leaf5046Certificate.logOnePlusV leaf5046InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5046InputLogOnePlusV_eq }

private noncomputable def leaf5046Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi258InputQChi innerPair116Input
    leaf5046InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5046LowerChecked :
    lowerCheck 24 leaf5046Box leaf5046Inputs = true := by
  rfl'

private theorem leaf5046CoversExact : CoversExact 8
    leaf5046Box leaf5046Certificate leaf5046InnerLog leaf5046Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi258RoundedFacts
    innerPair116RoundedFacts leaf5046RoundedFacts (by rfl)

private theorem leaf5046FlatSound : Sound leaf5046Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5046CertificateValid
    leaf5046InnerLogValid leaf5046CoversExact leaf5046LowerChecked

private noncomputable def leaf5047Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5047Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7635002624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2192994987/2147483648) }, upper := { exponent := 1, mantissa := (33779/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270270663/15270005248) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5047InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf5047LocalValidity :
    LeafFacts leaf5047Box leaf5047Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5047Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7635002624) }) = true
      norm_num [leaf5047Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5047CertificateValid :
    WideCertificateValid leaf5047Box leaf5047Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi279ValidityFacts
    leaf5047LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5047CoverageChecked :
    coverageCheck (innerAD leaf5047Box) leaf5047InnerLog = true := by
  rfl'

private theorem leaf5047InnerLogValid :
    leaf5047InnerLog.Valid 8 (innerAD leaf5047Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf5047CoverageChecked

private noncomputable def leaf5047InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5047InputLogOnePlusV_eq :
    leaf5047InputLogOnePlusV = outerEnclosure 24
      (leaf5047Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5047RoundedFacts : LeafRoundedFacts 8
    leaf5047Certificate.logOnePlusV leaf5047InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5047InputLogOnePlusV_eq }

private noncomputable def leaf5047Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi279InputQChi innerPair116Input
    leaf5047InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5047LowerChecked :
    lowerCheck 24 leaf5047Box leaf5047Inputs = true := by
  rfl'

private theorem leaf5047CoversExact : CoversExact 8
    leaf5047Box leaf5047Certificate leaf5047InnerLog leaf5047Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi279RoundedFacts
    innerPair116RoundedFacts leaf5047RoundedFacts (by rfl)

private theorem leaf5047FlatSound : Sound leaf5047Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5047CertificateValid
    leaf5047InnerLogValid leaf5047CoversExact leaf5047LowerChecked

private noncomputable def leaf5048Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5048Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715005440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2197582225/2147483648) }, upper := { exponent := 1, mantissa := (16925/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432417791/137430010880) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5048InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf5048LocalValidity :
    LeafFacts leaf5048Box leaf5048Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5048Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715005440) }) = true
      norm_num [leaf5048Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5048CertificateValid :
    WideCertificateValid leaf5048Box leaf5048Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi279ValidityFacts
    leaf5048LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5048CoverageChecked :
    coverageCheck (innerAD leaf5048Box) leaf5048InnerLog = true := by
  rfl'

private theorem leaf5048InnerLogValid :
    leaf5048InnerLog.Valid 8 (innerAD leaf5048Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf5048CoverageChecked

private noncomputable def leaf5048InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5048InputLogOnePlusV_eq :
    leaf5048InputLogOnePlusV = outerEnclosure 24
      (leaf5048Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5048RoundedFacts : LeafRoundedFacts 8
    leaf5048Certificate.logOnePlusV leaf5048InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5048InputLogOnePlusV_eq }

private noncomputable def leaf5048Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi279InputQChi innerPair311Input
    leaf5048InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5048LowerChecked :
    lowerCheck 24 leaf5048Box leaf5048Inputs = true := by
  rfl'

private theorem leaf5048CoversExact : CoversExact 8
    leaf5048Box leaf5048Certificate leaf5048InnerLog leaf5048Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi279RoundedFacts
    innerPair311RoundedFacts leaf5048RoundedFacts (by rfl)

private theorem leaf5048FlatSound : Sound leaf5048Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5048CertificateValid
    leaf5048InnerLogValid leaf5048CoversExact leaf5048LowerChecked

private noncomputable def leaf5049Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5049Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714960896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2208984793/2147483648) }, upper := { exponent := 1, mantissa := (4253/4096) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432373247/137429921792) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5049InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5049LocalValidity :
    LeafFacts leaf5049Box leaf5049Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5049Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714960896) }) = true
      norm_num [leaf5049Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5049CertificateValid :
    WideCertificateValid leaf5049Box leaf5049Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi280ValidityFacts
    leaf5049LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5049CoverageChecked :
    coverageCheck (innerAD leaf5049Box) leaf5049InnerLog = true := by
  rfl'

private theorem leaf5049InnerLogValid :
    leaf5049InnerLog.Valid 8 (innerAD leaf5049Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5049CoverageChecked

private noncomputable def leaf5049InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5049InputLogOnePlusV_eq :
    leaf5049InputLogOnePlusV = outerEnclosure 24
      (leaf5049Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5049RoundedFacts : LeafRoundedFacts 8
    leaf5049Certificate.logOnePlusV leaf5049InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5049InputLogOnePlusV_eq }

private noncomputable def leaf5049Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi280InputQChi innerPair327Input
    leaf5049InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5049LowerChecked :
    lowerCheck 24 leaf5049Box leaf5049Inputs = true := by
  rfl'

private theorem leaf5049CoversExact : CoversExact 8
    leaf5049Box leaf5049Certificate leaf5049InnerLog leaf5049Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi280RoundedFacts
    innerPair327RoundedFacts leaf5049RoundedFacts (by rfl)

private theorem leaf5049FlatSound : Sound leaf5049Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5049CertificateValid
    leaf5049InnerLogValid leaf5049CoversExact leaf5049LowerChecked

private noncomputable def leaf5050Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5050Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816420352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2213637563/2147483648) }, upper := { exponent := 1, mantissa := (2131/2048) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633193545/19632840704) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5050InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf5050LocalValidity :
    LeafFacts leaf5050Box leaf5050Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5050Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816420352) }) = true
      norm_num [leaf5050Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5050CertificateValid :
    WideCertificateValid leaf5050Box leaf5050Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi280ValidityFacts
    leaf5050LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5050CoverageChecked :
    coverageCheck (innerAD leaf5050Box) leaf5050InnerLog = true := by
  rfl'

private theorem leaf5050InnerLogValid :
    leaf5050InnerLog.Valid 8 (innerAD leaf5050Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf5050CoverageChecked

private noncomputable def leaf5050InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5050InputLogOnePlusV_eq :
    leaf5050InputLogOnePlusV = outerEnclosure 24
      (leaf5050Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5050RoundedFacts : LeafRoundedFacts 8
    leaf5050Certificate.logOnePlusV leaf5050InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5050InputLogOnePlusV_eq }

private noncomputable def leaf5050Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi280InputQChi innerPair329Input
    leaf5050InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5050LowerChecked :
    lowerCheck 24 leaf5050Box leaf5050Inputs = true := by
  rfl'

private theorem leaf5050CoversExact : CoversExact 8
    leaf5050Box leaf5050Certificate leaf5050InnerLog leaf5050Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi280RoundedFacts
    innerPair329RoundedFacts leaf5050RoundedFacts (by rfl)

private theorem leaf5050FlatSound : Sound leaf5050Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5050CertificateValid
    leaf5050InnerLogValid leaf5050CoversExact leaf5050LowerChecked

private noncomputable def leaf5051Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5051Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816426752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2202169463/2147483648) }, upper := { exponent := 1, mantissa := (33921/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633199945/19632853504) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5051InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5051LocalValidity :
    LeafFacts leaf5051Box leaf5051Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5051Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816426752) }) = true
      norm_num [leaf5051Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5051CertificateValid :
    WideCertificateValid leaf5051Box leaf5051Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi279ValidityFacts
    leaf5051LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5051CoverageChecked :
    coverageCheck (innerAD leaf5051Box) leaf5051InnerLog = true := by
  rfl'

private theorem leaf5051InnerLogValid :
    leaf5051InnerLog.Valid 8 (innerAD leaf5051Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5051CoverageChecked

private noncomputable def leaf5051InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5051InputLogOnePlusV_eq :
    leaf5051InputLogOnePlusV = outerEnclosure 24
      (leaf5051Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5051RoundedFacts : LeafRoundedFacts 8
    leaf5051Certificate.logOnePlusV leaf5051InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5051InputLogOnePlusV_eq }

private noncomputable def leaf5051Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi279InputQChi innerPair327Input
    leaf5051InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5051LowerChecked :
    lowerCheck 24 leaf5051Box leaf5051Inputs = true := by
  rfl'

private theorem leaf5051CoversExact : CoversExact 8
    leaf5051Box leaf5051Certificate leaf5051InnerLog leaf5051Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi279RoundedFacts
    innerPair327RoundedFacts leaf5051RoundedFacts (by rfl)

private theorem leaf5051FlatSound : Sound leaf5051Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5051CertificateValid
    leaf5051InnerLogValid leaf5051CoversExact leaf5051LowerChecked

private noncomputable def leaf5052Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf5052Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904989696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2206756701/2147483648) }, upper := { exponent := 1, mantissa := (4249/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810793813/45809979392) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5052InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf5052LocalValidity :
    LeafFacts leaf5052Box leaf5052Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5052Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904989696) }) = true
      norm_num [leaf5052Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5052CertificateValid :
    WideCertificateValid leaf5052Box leaf5052Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi279ValidityFacts
    leaf5052LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5052CoverageChecked :
    coverageCheck (innerAD leaf5052Box) leaf5052InnerLog = true := by
  rfl'

private theorem leaf5052InnerLogValid :
    leaf5052InnerLog.Valid 8 (innerAD leaf5052Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf5052CoverageChecked

private noncomputable def leaf5052InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5052InputLogOnePlusV_eq :
    leaf5052InputLogOnePlusV = outerEnclosure 24
      (leaf5052Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5052RoundedFacts : LeafRoundedFacts 8
    leaf5052Certificate.logOnePlusV leaf5052InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5052InputLogOnePlusV_eq }

private noncomputable def leaf5052Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi279InputQChi innerPair327Input
    leaf5052InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5052LowerChecked :
    lowerCheck 24 leaf5052Box leaf5052Inputs = true := by
  rfl'

private theorem leaf5052CoversExact : CoversExact 8
    leaf5052Box leaf5052Certificate leaf5052InnerLog leaf5052Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi279RoundedFacts
    innerPair327RoundedFacts leaf5052RoundedFacts (by rfl)

private theorem leaf5052FlatSound : Sound leaf5052Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5052CertificateValid
    leaf5052InnerLogValid leaf5052CoversExact leaf5052LowerChecked

private noncomputable def leaf5053Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5053Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714924032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2218290333/2147483648) }, upper := { exponent := 1, mantissa := (4271/4096) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432336383/137429848064) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5053InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5053LocalValidity :
    LeafFacts leaf5053Box leaf5053Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5053Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714924032) }) = true
      norm_num [leaf5053Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5053CertificateValid :
    WideCertificateValid leaf5053Box leaf5053Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi280ValidityFacts
    leaf5053LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5053CoverageChecked :
    coverageCheck (innerAD leaf5053Box) leaf5053InnerLog = true := by
  rfl'

private theorem leaf5053InnerLogValid :
    leaf5053InnerLog.Valid 8 (innerAD leaf5053Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5053CoverageChecked

private noncomputable def leaf5053InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5053InputLogOnePlusV_eq :
    leaf5053InputLogOnePlusV = outerEnclosure 24
      (leaf5053Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5053RoundedFacts : LeafRoundedFacts 8
    leaf5053Certificate.logOnePlusV leaf5053InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5053InputLogOnePlusV_eq }

private noncomputable def leaf5053Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi280InputQChi innerPair248Input
    leaf5053InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5053LowerChecked :
    lowerCheck 24 leaf5053Box leaf5053Inputs = true := by
  rfl'

private theorem leaf5053CoversExact : CoversExact 8
    leaf5053Box leaf5053Certificate leaf5053InnerLog leaf5053Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi280RoundedFacts
    innerPair248RoundedFacts leaf5053RoundedFacts (by rfl)

private theorem leaf5053FlatSound : Sound leaf5053Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5053CertificateValid
    leaf5053InnerLogValid leaf5053CoversExact leaf5053LowerChecked

private noncomputable def leaf5054Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf5054Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (455082201/455065600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2222943103/2147483648) }, upper := { exponent := 1, mantissa := (535/512) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (910147801/910131200) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5054InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf5054LocalValidity :
    LeafFacts leaf5054Box leaf5054Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5054Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (455082201/455065600) }) = true
      norm_num [leaf5054Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5054CertificateValid :
    WideCertificateValid leaf5054Box leaf5054Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi280ValidityFacts
    leaf5054LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5054CoverageChecked :
    coverageCheck (innerAD leaf5054Box) leaf5054InnerLog = true := by
  rfl'

private theorem leaf5054InnerLogValid :
    leaf5054InnerLog.Valid 8 (innerAD leaf5054Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf5054CoverageChecked

private noncomputable def leaf5054InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5054InputLogOnePlusV_eq :
    leaf5054InputLogOnePlusV = outerEnclosure 24
      (leaf5054Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5054RoundedFacts : LeafRoundedFacts 8
    leaf5054Certificate.logOnePlusV leaf5054InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5054InputLogOnePlusV_eq }

private noncomputable def leaf5054Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi280InputQChi innerPair248Input
    leaf5054InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5054LowerChecked :
    lowerCheck 24 leaf5054Box leaf5054Inputs = true := by
  rfl'

private theorem leaf5054CoversExact : CoversExact 8
    leaf5054Box leaf5054Certificate leaf5054InnerLog leaf5054Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi280RoundedFacts
    innerPair248RoundedFacts leaf5054RoundedFacts (by rfl)

private theorem leaf5054FlatSound : Sound leaf5054Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5054CertificateValid
    leaf5054InnerLogValid leaf5054CoversExact leaf5054LowerChecked

private noncomputable def component102Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node0_sound : Sound component102Node0Box :=
  sound_of_literal_split component102Node0Box leaf4991Box leaf4992Box
    .k (241/64) (by rfl) (by rfl)
    leaf4991FlatSound leaf4992FlatSound

private noncomputable def component102Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node1_sound : Sound component102Node1Box :=
  sound_of_literal_split component102Node1Box leaf4993Box leaf4994Box
    .k (241/64) (by rfl) (by rfl)
    leaf4993FlatSound leaf4994FlatSound

private noncomputable def component102Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node2_sound : Sound component102Node2Box :=
  sound_of_literal_split component102Node2Box component102Node0Box component102Node1Box
    .chi (65/256) (by rfl) (by rfl)
    component102Node0_sound component102Node1_sound

private noncomputable def component102Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node3_sound : Sound component102Node3Box :=
  sound_of_literal_split component102Node3Box leaf4995Box leaf4996Box
    .k (243/64) (by rfl) (by rfl)
    leaf4995FlatSound leaf4996FlatSound

private noncomputable def component102Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node4_sound : Sound component102Node4Box :=
  sound_of_literal_split component102Node4Box leaf4997Box leaf4998Box
    .k (243/64) (by rfl) (by rfl)
    leaf4997FlatSound leaf4998FlatSound

private noncomputable def component102Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node5_sound : Sound component102Node5Box :=
  sound_of_literal_split component102Node5Box component102Node3Box component102Node4Box
    .chi (65/256) (by rfl) (by rfl)
    component102Node3_sound component102Node4_sound

private noncomputable def component102Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node6_sound : Sound component102Node6Box :=
  sound_of_literal_split component102Node6Box component102Node2Box component102Node5Box
    .k (121/32) (by rfl) (by rfl)
    component102Node2_sound component102Node5_sound

private noncomputable def component102Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node7_sound : Sound component102Node7Box :=
  sound_of_literal_split component102Node7Box leaf4999Box leaf5000Box
    .k (241/64) (by rfl) (by rfl)
    leaf4999FlatSound leaf5000FlatSound

private noncomputable def component102Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node8_sound : Sound component102Node8Box :=
  sound_of_literal_split component102Node8Box leaf5001Box leaf5002Box
    .k (241/64) (by rfl) (by rfl)
    leaf5001FlatSound leaf5002FlatSound

private noncomputable def component102Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node9_sound : Sound component102Node9Box :=
  sound_of_literal_split component102Node9Box component102Node7Box component102Node8Box
    .chi (67/256) (by rfl) (by rfl)
    component102Node7_sound component102Node8_sound

private noncomputable def component102Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node10_sound : Sound component102Node10Box :=
  sound_of_literal_split component102Node10Box leaf5003Box leaf5004Box
    .k (243/64) (by rfl) (by rfl)
    leaf5003FlatSound leaf5004FlatSound

private noncomputable def component102Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node11_sound : Sound component102Node11Box :=
  sound_of_literal_split component102Node11Box leaf5005Box leaf5006Box
    .k (243/64) (by rfl) (by rfl)
    leaf5005FlatSound leaf5006FlatSound

private noncomputable def component102Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node12_sound : Sound component102Node12Box :=
  sound_of_literal_split component102Node12Box component102Node10Box component102Node11Box
    .chi (67/256) (by rfl) (by rfl)
    component102Node10_sound component102Node11_sound

private noncomputable def component102Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node13_sound : Sound component102Node13Box :=
  sound_of_literal_split component102Node13Box component102Node9Box component102Node12Box
    .k (121/32) (by rfl) (by rfl)
    component102Node9_sound component102Node12_sound

private noncomputable def component102Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node14_sound : Sound component102Node14Box :=
  sound_of_literal_split component102Node14Box component102Node6Box component102Node13Box
    .chi (33/128) (by rfl) (by rfl)
    component102Node6_sound component102Node13_sound

private noncomputable def component102Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node15_sound : Sound component102Node15Box :=
  sound_of_literal_split component102Node15Box leaf5007Box leaf5008Box
    .k (245/64) (by rfl) (by rfl)
    leaf5007FlatSound leaf5008FlatSound

private noncomputable def component102Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node16_sound : Sound component102Node16Box :=
  sound_of_literal_split component102Node16Box leaf5009Box leaf5010Box
    .k (245/64) (by rfl) (by rfl)
    leaf5009FlatSound leaf5010FlatSound

private noncomputable def component102Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node17_sound : Sound component102Node17Box :=
  sound_of_literal_split component102Node17Box component102Node15Box component102Node16Box
    .chi (65/256) (by rfl) (by rfl)
    component102Node15_sound component102Node16_sound

private noncomputable def component102Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node18_sound : Sound component102Node18Box :=
  sound_of_literal_split component102Node18Box leaf5011Box leaf5012Box
    .k (247/64) (by rfl) (by rfl)
    leaf5011FlatSound leaf5012FlatSound

private noncomputable def component102Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node19_sound : Sound component102Node19Box :=
  sound_of_literal_split component102Node19Box leaf5013Box leaf5014Box
    .k (247/64) (by rfl) (by rfl)
    leaf5013FlatSound leaf5014FlatSound

private noncomputable def component102Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node20_sound : Sound component102Node20Box :=
  sound_of_literal_split component102Node20Box component102Node18Box component102Node19Box
    .chi (65/256) (by rfl) (by rfl)
    component102Node18_sound component102Node19_sound

private noncomputable def component102Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node21_sound : Sound component102Node21Box :=
  sound_of_literal_split component102Node21Box component102Node17Box component102Node20Box
    .k (123/32) (by rfl) (by rfl)
    component102Node17_sound component102Node20_sound

private noncomputable def component102Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node22_sound : Sound component102Node22Box :=
  sound_of_literal_split component102Node22Box leaf5015Box leaf5016Box
    .k (245/64) (by rfl) (by rfl)
    leaf5015FlatSound leaf5016FlatSound

private noncomputable def component102Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node23_sound : Sound component102Node23Box :=
  sound_of_literal_split component102Node23Box leaf5017Box leaf5018Box
    .k (245/64) (by rfl) (by rfl)
    leaf5017FlatSound leaf5018FlatSound

private noncomputable def component102Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node24_sound : Sound component102Node24Box :=
  sound_of_literal_split component102Node24Box component102Node22Box component102Node23Box
    .chi (67/256) (by rfl) (by rfl)
    component102Node22_sound component102Node23_sound

private noncomputable def component102Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node25_sound : Sound component102Node25Box :=
  sound_of_literal_split component102Node25Box leaf5019Box leaf5020Box
    .k (247/64) (by rfl) (by rfl)
    leaf5019FlatSound leaf5020FlatSound

private noncomputable def component102Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node26_sound : Sound component102Node26Box :=
  sound_of_literal_split component102Node26Box leaf5021Box leaf5022Box
    .k (247/64) (by rfl) (by rfl)
    leaf5021FlatSound leaf5022FlatSound

private noncomputable def component102Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node27_sound : Sound component102Node27Box :=
  sound_of_literal_split component102Node27Box component102Node25Box component102Node26Box
    .chi (67/256) (by rfl) (by rfl)
    component102Node25_sound component102Node26_sound

private noncomputable def component102Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node28_sound : Sound component102Node28Box :=
  sound_of_literal_split component102Node28Box component102Node24Box component102Node27Box
    .k (123/32) (by rfl) (by rfl)
    component102Node24_sound component102Node27_sound

private noncomputable def component102Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node29_sound : Sound component102Node29Box :=
  sound_of_literal_split component102Node29Box component102Node21Box component102Node28Box
    .chi (33/128) (by rfl) (by rfl)
    component102Node21_sound component102Node28_sound

private noncomputable def component102Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component102Node30_sound : Sound component102Node30Box :=
  sound_of_literal_split component102Node30Box component102Node14Box component102Node29Box
    .k (61/16) (by rfl) (by rfl)
    component102Node14_sound component102Node29_sound

private noncomputable def component102Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node31_sound : Sound component102Node31Box :=
  sound_of_literal_split component102Node31Box leaf5023Box leaf5024Box
    .k (241/64) (by rfl) (by rfl)
    leaf5023FlatSound leaf5024FlatSound

private noncomputable def component102Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node32_sound : Sound component102Node32Box :=
  sound_of_literal_split component102Node32Box leaf5025Box leaf5026Box
    .k (241/64) (by rfl) (by rfl)
    leaf5025FlatSound leaf5026FlatSound

private noncomputable def component102Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node33_sound : Sound component102Node33Box :=
  sound_of_literal_split component102Node33Box component102Node31Box component102Node32Box
    .chi (69/256) (by rfl) (by rfl)
    component102Node31_sound component102Node32_sound

private noncomputable def component102Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node34_sound : Sound component102Node34Box :=
  sound_of_literal_split component102Node34Box leaf5027Box leaf5028Box
    .k (243/64) (by rfl) (by rfl)
    leaf5027FlatSound leaf5028FlatSound

private noncomputable def component102Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node35_sound : Sound component102Node35Box :=
  sound_of_literal_split component102Node35Box leaf5029Box leaf5030Box
    .k (243/64) (by rfl) (by rfl)
    leaf5029FlatSound leaf5030FlatSound

private noncomputable def component102Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node36_sound : Sound component102Node36Box :=
  sound_of_literal_split component102Node36Box component102Node34Box component102Node35Box
    .chi (69/256) (by rfl) (by rfl)
    component102Node34_sound component102Node35_sound

private noncomputable def component102Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node37_sound : Sound component102Node37Box :=
  sound_of_literal_split component102Node37Box component102Node33Box component102Node36Box
    .k (121/32) (by rfl) (by rfl)
    component102Node33_sound component102Node36_sound

private noncomputable def component102Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node38_sound : Sound component102Node38Box :=
  sound_of_literal_split component102Node38Box leaf5031Box leaf5032Box
    .k (241/64) (by rfl) (by rfl)
    leaf5031FlatSound leaf5032FlatSound

private noncomputable def component102Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node39_sound : Sound component102Node39Box :=
  sound_of_literal_split component102Node39Box leaf5033Box leaf5034Box
    .k (241/64) (by rfl) (by rfl)
    leaf5033FlatSound leaf5034FlatSound

private noncomputable def component102Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node40_sound : Sound component102Node40Box :=
  sound_of_literal_split component102Node40Box component102Node38Box component102Node39Box
    .chi (71/256) (by rfl) (by rfl)
    component102Node38_sound component102Node39_sound

private noncomputable def component102Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node41_sound : Sound component102Node41Box :=
  sound_of_literal_split component102Node41Box leaf5035Box leaf5036Box
    .k (243/64) (by rfl) (by rfl)
    leaf5035FlatSound leaf5036FlatSound

private noncomputable def component102Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node42_sound : Sound component102Node42Box :=
  sound_of_literal_split component102Node42Box leaf5037Box leaf5038Box
    .k (243/64) (by rfl) (by rfl)
    leaf5037FlatSound leaf5038FlatSound

private noncomputable def component102Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node43_sound : Sound component102Node43Box :=
  sound_of_literal_split component102Node43Box component102Node41Box component102Node42Box
    .chi (71/256) (by rfl) (by rfl)
    component102Node41_sound component102Node42_sound

private noncomputable def component102Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node44_sound : Sound component102Node44Box :=
  sound_of_literal_split component102Node44Box component102Node40Box component102Node43Box
    .k (121/32) (by rfl) (by rfl)
    component102Node40_sound component102Node43_sound

private noncomputable def component102Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node45_sound : Sound component102Node45Box :=
  sound_of_literal_split component102Node45Box component102Node37Box component102Node44Box
    .chi (35/128) (by rfl) (by rfl)
    component102Node37_sound component102Node44_sound

private noncomputable def component102Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node46_sound : Sound component102Node46Box :=
  sound_of_literal_split component102Node46Box leaf5039Box leaf5040Box
    .k (245/64) (by rfl) (by rfl)
    leaf5039FlatSound leaf5040FlatSound

private noncomputable def component102Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node47_sound : Sound component102Node47Box :=
  sound_of_literal_split component102Node47Box leaf5041Box leaf5042Box
    .k (245/64) (by rfl) (by rfl)
    leaf5041FlatSound leaf5042FlatSound

private noncomputable def component102Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node48_sound : Sound component102Node48Box :=
  sound_of_literal_split component102Node48Box component102Node46Box component102Node47Box
    .chi (69/256) (by rfl) (by rfl)
    component102Node46_sound component102Node47_sound

private noncomputable def component102Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node49_sound : Sound component102Node49Box :=
  sound_of_literal_split component102Node49Box leaf5043Box leaf5044Box
    .k (247/64) (by rfl) (by rfl)
    leaf5043FlatSound leaf5044FlatSound

private noncomputable def component102Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node50_sound : Sound component102Node50Box :=
  sound_of_literal_split component102Node50Box leaf5045Box leaf5046Box
    .k (247/64) (by rfl) (by rfl)
    leaf5045FlatSound leaf5046FlatSound

private noncomputable def component102Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node51_sound : Sound component102Node51Box :=
  sound_of_literal_split component102Node51Box component102Node49Box component102Node50Box
    .chi (69/256) (by rfl) (by rfl)
    component102Node49_sound component102Node50_sound

private noncomputable def component102Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component102Node52_sound : Sound component102Node52Box :=
  sound_of_literal_split component102Node52Box component102Node48Box component102Node51Box
    .k (123/32) (by rfl) (by rfl)
    component102Node48_sound component102Node51_sound

private noncomputable def component102Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node53_sound : Sound component102Node53Box :=
  sound_of_literal_split component102Node53Box leaf5047Box leaf5048Box
    .k (245/64) (by rfl) (by rfl)
    leaf5047FlatSound leaf5048FlatSound

private noncomputable def component102Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node54_sound : Sound component102Node54Box :=
  sound_of_literal_split component102Node54Box leaf5049Box leaf5050Box
    .k (245/64) (by rfl) (by rfl)
    leaf5049FlatSound leaf5050FlatSound

private noncomputable def component102Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node55_sound : Sound component102Node55Box :=
  sound_of_literal_split component102Node55Box component102Node53Box component102Node54Box
    .chi (71/256) (by rfl) (by rfl)
    component102Node53_sound component102Node54_sound

private noncomputable def component102Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component102Node56_sound : Sound component102Node56Box :=
  sound_of_literal_split component102Node56Box leaf5051Box leaf5052Box
    .k (247/64) (by rfl) (by rfl)
    leaf5051FlatSound leaf5052FlatSound

private noncomputable def component102Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node57_sound : Sound component102Node57Box :=
  sound_of_literal_split component102Node57Box leaf5053Box leaf5054Box
    .k (247/64) (by rfl) (by rfl)
    leaf5053FlatSound leaf5054FlatSound

private noncomputable def component102Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node58_sound : Sound component102Node58Box :=
  sound_of_literal_split component102Node58Box component102Node56Box component102Node57Box
    .chi (71/256) (by rfl) (by rfl)
    component102Node56_sound component102Node57_sound

private noncomputable def component102Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node59_sound : Sound component102Node59Box :=
  sound_of_literal_split component102Node59Box component102Node55Box component102Node58Box
    .k (123/32) (by rfl) (by rfl)
    component102Node55_sound component102Node58_sound

private noncomputable def component102Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node60_sound : Sound component102Node60Box :=
  sound_of_literal_split component102Node60Box component102Node52Box component102Node59Box
    .chi (35/128) (by rfl) (by rfl)
    component102Node52_sound component102Node59_sound

private noncomputable def component102Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component102Node61_sound : Sound component102Node61Box :=
  sound_of_literal_split component102Node61Box component102Node45Box component102Node60Box
    .k (61/16) (by rfl) (by rfl)
    component102Node45_sound component102Node60_sound

noncomputable def component102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
theorem component102_sound : Sound component102Box :=
  sound_of_literal_split component102Box component102Node30Box component102Node61Box
    .chi (17/64) (by rfl) (by rfl)
    component102Node30_sound component102Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
