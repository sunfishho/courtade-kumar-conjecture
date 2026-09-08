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
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
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

private noncomputable def leaf3452Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3452Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431920128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1954458543/1073741824) }, upper := { exponent := 0, mantissa := (30121/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868841983/274863840256) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3452InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3452LocalValidity :
    LeafFacts leaf3452Box leaf3452Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3452Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431920128) }) = true
      norm_num [leaf3452Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3452CertificateValid :
    WideCertificateValid leaf3452Box leaf3452Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi201ValidityFacts
    leaf3452LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3452CoverageChecked :
    coverageCheck (innerAD leaf3452Box) leaf3452InnerLog = true := by
  rfl'

private theorem leaf3452InnerLogValid :
    leaf3452InnerLog.Valid 8 (innerAD leaf3452Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3452CoverageChecked

private noncomputable def leaf3452InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3452InputLogOnePlusV_eq :
    leaf3452InputLogOnePlusV = outerEnclosure 24
      (leaf3452Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3452RoundedFacts : LeafRoundedFacts 8
    leaf3452Certificate.logOnePlusV leaf3452InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3452InputLogOnePlusV_eq }

private noncomputable def leaf3452Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi201InputQChi innerPair94Input
    leaf3452InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3452LowerChecked :
    lowerCheck 24 leaf3452Box leaf3452Inputs = true := by
  rfl'

private theorem leaf3452CoversExact : CoversExact 8
    leaf3452Box leaf3452Certificate leaf3452InnerLog leaf3452Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi201RoundedFacts
    innerPair94RoundedFacts leaf3452RoundedFacts (by rfl)

private theorem leaf3452FlatSound : Sound leaf3452Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3452CertificateValid
    leaf3452InnerLogValid leaf3452CoversExact leaf3452LowerChecked

private noncomputable def leaf3453Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3453Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431890944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1958128333/1073741824) }, upper := { exponent := 0, mantissa := (15089/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868812799/274863781888) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3453InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3453LocalValidity :
    LeafFacts leaf3453Box leaf3453Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3453Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431890944) }) = true
      norm_num [leaf3453Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3453CertificateValid :
    WideCertificateValid leaf3453Box leaf3453Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi201ValidityFacts
    leaf3453LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3453CoverageChecked :
    coverageCheck (innerAD leaf3453Box) leaf3453InnerLog = true := by
  rfl'

private theorem leaf3453InnerLogValid :
    leaf3453InnerLog.Valid 8 (innerAD leaf3453Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3453CoverageChecked

private noncomputable def leaf3453InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3453InputLogOnePlusV_eq :
    leaf3453InputLogOnePlusV = outerEnclosure 24
      (leaf3453Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3453RoundedFacts : LeafRoundedFacts 8
    leaf3453Certificate.logOnePlusV leaf3453InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3453InputLogOnePlusV_eq }

private noncomputable def leaf3453Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi201InputQChi innerPair94Input
    leaf3453InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3453LowerChecked :
    lowerCheck 24 leaf3453Box leaf3453Inputs = true := by
  rfl'

private theorem leaf3453CoversExact : CoversExact 8
    leaf3453Box leaf3453Certificate leaf3453InnerLog leaf3453Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi201RoundedFacts
    innerPair94RoundedFacts leaf3453RoundedFacts (by rfl)

private theorem leaf3453FlatSound : Sound leaf3453Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3453CertificateValid
    leaf3453InnerLogValid leaf3453CoversExact leaf3453LowerChecked

private noncomputable def leaf3454Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3454Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810598912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1970186221/1073741824) }, upper := { exponent := 0, mantissa := (15181/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622906197/91621197824) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3454InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3454LocalValidity :
    LeafFacts leaf3454Box leaf3454Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3454Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810598912) }) = true
      norm_num [leaf3454Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3454CertificateValid :
    WideCertificateValid leaf3454Box leaf3454Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi202ValidityFacts
    leaf3454LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3454CoverageChecked :
    coverageCheck (innerAD leaf3454Box) leaf3454InnerLog = true := by
  rfl'

private theorem leaf3454InnerLogValid :
    leaf3454InnerLog.Valid 8 (innerAD leaf3454Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3454CoverageChecked

private noncomputable def leaf3454InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3454InputLogOnePlusV_eq :
    leaf3454InputLogOnePlusV = outerEnclosure 24
      (leaf3454Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3454RoundedFacts : LeafRoundedFacts 8
    leaf3454Certificate.logOnePlusV leaf3454InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3454InputLogOnePlusV_eq }

private noncomputable def leaf3454Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3454InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3454LowerChecked :
    lowerCheck 24 leaf3454Box leaf3454Inputs = true := by
  rfl'

private theorem leaf3454CoversExact : CoversExact 8
    leaf3454Box leaf3454Certificate leaf3454InnerLog leaf3454Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3454RoundedFacts (by rfl)

private theorem leaf3454FlatSound : Sound leaf3454Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3454CertificateValid
    leaf3454InnerLogValid leaf3454CoversExact leaf3454LowerChecked

private noncomputable def leaf3455Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3455Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486353408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1973921543/1073741824) }, upper := { exponent := 0, mantissa := (7605/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973737779/54972706816) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3455InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3455LocalValidity :
    LeafFacts leaf3455Box leaf3455Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3455Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486353408) }) = true
      norm_num [leaf3455Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3455CertificateValid :
    WideCertificateValid leaf3455Box leaf3455Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi202ValidityFacts
    leaf3455LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3455CoverageChecked :
    coverageCheck (innerAD leaf3455Box) leaf3455InnerLog = true := by
  rfl'

private theorem leaf3455InnerLogValid :
    leaf3455InnerLog.Valid 8 (innerAD leaf3455Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3455CoverageChecked

private noncomputable def leaf3455InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3455InputLogOnePlusV_eq :
    leaf3455InputLogOnePlusV = outerEnclosure 24
      (leaf3455Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3455RoundedFacts : LeafRoundedFacts 8
    leaf3455Certificate.logOnePlusV leaf3455InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3455InputLogOnePlusV_eq }

private noncomputable def leaf3455Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3455InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3455LowerChecked :
    lowerCheck 24 leaf3455Box leaf3455Inputs = true := by
  rfl'

private theorem leaf3455CoversExact : CoversExact 8
    leaf3455Box leaf3455Certificate leaf3455InnerLog leaf3455Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3455RoundedFacts (by rfl)

private theorem leaf3455FlatSound : Sound leaf3455Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3455CertificateValid
    leaf3455InnerLogValid leaf3455CoversExact leaf3455LowerChecked

private noncomputable def leaf3456Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3456Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486372352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1961798123/1073741824) }, upper := { exponent := 0, mantissa := (30235/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973756723/54972744704) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3456InnerLog : WideLogData :=
  innerPair99Data

set_option maxRecDepth 1000000 in
private theorem leaf3456LocalValidity :
    LeafFacts leaf3456Box leaf3456Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3456Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486372352) }) = true
      norm_num [leaf3456Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3456CertificateValid :
    WideCertificateValid leaf3456Box leaf3456Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi201ValidityFacts
    leaf3456LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3456CoverageChecked :
    coverageCheck (innerAD leaf3456Box) leaf3456InnerLog = true := by
  rfl'

private theorem leaf3456InnerLogValid :
    leaf3456InnerLog.Valid 8 (innerAD leaf3456Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint211PositiveFacts.valid leaf3456CoverageChecked

private noncomputable def leaf3456InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3456InputLogOnePlusV_eq :
    leaf3456InputLogOnePlusV = outerEnclosure 24
      (leaf3456Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3456RoundedFacts : LeafRoundedFacts 8
    leaf3456Certificate.logOnePlusV leaf3456InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3456InputLogOnePlusV_eq }

private noncomputable def leaf3456Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi201InputQChi innerPair99Input
    leaf3456InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3456LowerChecked :
    lowerCheck 24 leaf3456Box leaf3456Inputs = true := by
  rfl'

private theorem leaf3456CoversExact : CoversExact 8
    leaf3456Box leaf3456Certificate leaf3456InnerLog leaf3456Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi201RoundedFacts
    innerPair99RoundedFacts leaf3456RoundedFacts (by rfl)

private theorem leaf3456FlatSound : Sound leaf3456Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3456CertificateValid
    leaf3456InnerLogValid leaf3456CoversExact leaf3456LowerChecked

private noncomputable def leaf3457Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3457Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431832576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1965467913/1073741824) }, upper := { exponent := 0, mantissa := (7573/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868754431/274863665152) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3457InnerLog : WideLogData :=
  innerPair214Data

set_option maxRecDepth 1000000 in
private theorem leaf3457LocalValidity :
    LeafFacts leaf3457Box leaf3457Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3457Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431832576) }) = true
      norm_num [leaf3457Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3457CertificateValid :
    WideCertificateValid leaf3457Box leaf3457Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi201ValidityFacts
    leaf3457LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3457CoverageChecked :
    coverageCheck (innerAD leaf3457Box) leaf3457InnerLog = true := by
  rfl'

private theorem leaf3457InnerLogValid :
    leaf3457InnerLog.Valid 8 (innerAD leaf3457Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint211PositiveFacts.valid leaf3457CoverageChecked

private noncomputable def leaf3457InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3457InputLogOnePlusV_eq :
    leaf3457InputLogOnePlusV = outerEnclosure 24
      (leaf3457Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3457RoundedFacts : LeafRoundedFacts 8
    leaf3457Certificate.logOnePlusV leaf3457InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3457InputLogOnePlusV_eq }

private noncomputable def leaf3457Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi201InputQChi innerPair214Input
    leaf3457InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3457LowerChecked :
    lowerCheck 24 leaf3457Box leaf3457Inputs = true := by
  rfl'

private theorem leaf3457CoversExact : CoversExact 8
    leaf3457Box leaf3457Certificate leaf3457InnerLog leaf3457Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi201RoundedFacts
    innerPair214RoundedFacts leaf3457RoundedFacts (by rfl)

private theorem leaf3457FlatSound : Sound leaf3457Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3457CertificateValid
    leaf3457InnerLogValid leaf3457CoversExact leaf3457LowerChecked

private noncomputable def leaf3458Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3458Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431737344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1977656865/1073741824) }, upper := { exponent := 0, mantissa := (15239/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868659199/274863474688) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3458InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3458LocalValidity :
    LeafFacts leaf3458Box leaf3458Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3458Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431737344) }) = true
      norm_num [leaf3458Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3458CertificateValid :
    WideCertificateValid leaf3458Box leaf3458Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi202ValidityFacts
    leaf3458LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3458CoverageChecked :
    coverageCheck (innerAD leaf3458Box) leaf3458InnerLog = true := by
  rfl'

private theorem leaf3458InnerLogValid :
    leaf3458InnerLog.Valid 8 (innerAD leaf3458Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3458CoverageChecked

private noncomputable def leaf3458InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3458InputLogOnePlusV_eq :
    leaf3458InputLogOnePlusV = outerEnclosure 24
      (leaf3458Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3458RoundedFacts : LeafRoundedFacts 8
    leaf3458Certificate.logOnePlusV leaf3458InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3458InputLogOnePlusV_eq }

private noncomputable def leaf3458Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3458InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3458LowerChecked :
    lowerCheck 24 leaf3458Box leaf3458Inputs = true := by
  rfl'

private theorem leaf3458CoversExact : CoversExact 8
    leaf3458Box leaf3458Certificate leaf3458InnerLog leaf3458Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3458RoundedFacts (by rfl)

private theorem leaf3458FlatSound : Sound leaf3458Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3458CertificateValid
    leaf3458InnerLogValid leaf3458CoversExact leaf3458LowerChecked

private noncomputable def leaf3459Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3459Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810569216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1981392187/1073741824) }, upper := { exponent := 0, mantissa := (3817/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622876501/91621138432) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3459InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3459LocalValidity :
    LeafFacts leaf3459Box leaf3459Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3459Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810569216) }) = true
      norm_num [leaf3459Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3459CertificateValid :
    WideCertificateValid leaf3459Box leaf3459Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi202ValidityFacts
    leaf3459LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3459CoverageChecked :
    coverageCheck (innerAD leaf3459Box) leaf3459InnerLog = true := by
  rfl'

private theorem leaf3459InnerLogValid :
    leaf3459InnerLog.Valid 8 (innerAD leaf3459Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3459CoverageChecked

private noncomputable def leaf3459InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3459InputLogOnePlusV_eq :
    leaf3459InputLogOnePlusV = outerEnclosure 24
      (leaf3459Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3459RoundedFacts : LeafRoundedFacts 8
    leaf3459Certificate.logOnePlusV leaf3459InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3459InputLogOnePlusV_eq }

private noncomputable def leaf3459Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3459InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3459LowerChecked :
    lowerCheck 24 leaf3459Box leaf3459Inputs = true := by
  rfl'

private theorem leaf3459CoversExact : CoversExact 8
    leaf3459Box leaf3459Certificate leaf3459InnerLog leaf3459Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3459RoundedFacts (by rfl)

private theorem leaf3459FlatSound : Sound leaf3459Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3459CertificateValid
    leaf3459InnerLogValid leaf3459CoversExact leaf3459LowerChecked

private noncomputable def leaf3460Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3460Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431673344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1985913899/1073741824) }, upper := { exponent := 0, mantissa := (30603/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868595199/274863346688) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3460InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3460LocalValidity :
    LeafFacts leaf3460Box leaf3460Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3460Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431673344) }) = true
      norm_num [leaf3460Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3460CertificateValid :
    WideCertificateValid leaf3460Box leaf3460Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi199ValidityFacts
    leaf3460LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3460CoverageChecked :
    coverageCheck (innerAD leaf3460Box) leaf3460InnerLog = true := by
  rfl'

private theorem leaf3460InnerLogValid :
    leaf3460InnerLog.Valid 8 (innerAD leaf3460Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3460CoverageChecked

private noncomputable def leaf3460InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3460InputLogOnePlusV_eq :
    leaf3460InputLogOnePlusV = outerEnclosure 24
      (leaf3460Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3460RoundedFacts : LeafRoundedFacts 8
    leaf3460Certificate.logOnePlusV leaf3460InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3460InputLogOnePlusV_eq }

private noncomputable def leaf3460Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3460InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3460LowerChecked :
    lowerCheck 24 leaf3460Box leaf3460Inputs = true := by
  rfl'

private theorem leaf3460CoversExact : CoversExact 8
    leaf3460Box leaf3460Certificate leaf3460InnerLog leaf3460Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3460RoundedFacts (by rfl)

private theorem leaf3460FlatSound : Sound leaf3460Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3460CertificateValid
    leaf3460InnerLogValid leaf3460CoversExact leaf3460LowerChecked

private noncomputable def leaf3461Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3461Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810547712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1989714753/1073741824) }, upper := { exponent := 0, mantissa := (15331/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622854997/91621095424) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3461InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3461LocalValidity :
    LeafFacts leaf3461Box leaf3461Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3461Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810547712) }) = true
      norm_num [leaf3461Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3461CertificateValid :
    WideCertificateValid leaf3461Box leaf3461Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi199ValidityFacts
    leaf3461LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3461CoverageChecked :
    coverageCheck (innerAD leaf3461Box) leaf3461InnerLog = true := by
  rfl'

private theorem leaf3461InnerLogValid :
    leaf3461InnerLog.Valid 8 (innerAD leaf3461Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3461CoverageChecked

private noncomputable def leaf3461InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3461InputLogOnePlusV_eq :
    leaf3461InputLogOnePlusV = outerEnclosure 24
      (leaf3461Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3461RoundedFacts : LeafRoundedFacts 8
    leaf3461Certificate.logOnePlusV leaf3461InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3461InputLogOnePlusV_eq }

private noncomputable def leaf3461Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3461InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3461LowerChecked :
    lowerCheck 24 leaf3461Box leaf3461Inputs = true := by
  rfl'

private theorem leaf3461CoversExact : CoversExact 8
    leaf3461Box leaf3461Certificate leaf3461InnerLog leaf3461Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3461RoundedFacts (by rfl)

private theorem leaf3461FlatSound : Sound leaf3461Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3461CertificateValid
    leaf3461InnerLogValid leaf3461CoversExact leaf3461LowerChecked

private noncomputable def leaf3462Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3462Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431549952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2001641577/1073741824) }, upper := { exponent := 0, mantissa := (7711/4096) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868471807/274863099904) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3462InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3462LocalValidity :
    LeafFacts leaf3462Box leaf3462Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3462Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431549952) }) = true
      norm_num [leaf3462Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3462CertificateValid :
    WideCertificateValid leaf3462Box leaf3462Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi200ValidityFacts
    leaf3462LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3462CoverageChecked :
    coverageCheck (innerAD leaf3462Box) leaf3462InnerLog = true := by
  rfl'

private theorem leaf3462InnerLogValid :
    leaf3462InnerLog.Valid 8 (innerAD leaf3462Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3462CoverageChecked

private noncomputable def leaf3462InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3462InputLogOnePlusV_eq :
    leaf3462InputLogOnePlusV = outerEnclosure 24
      (leaf3462Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3462RoundedFacts : LeafRoundedFacts 8
    leaf3462Certificate.logOnePlusV leaf3462InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3462InputLogOnePlusV_eq }

private noncomputable def leaf3462Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi200InputQChi innerPair482Input
    leaf3462InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3462LowerChecked :
    lowerCheck 24 leaf3462Box leaf3462Inputs = true := by
  rfl'

private theorem leaf3462CoversExact : CoversExact 8
    leaf3462Box leaf3462Certificate leaf3462InnerLog leaf3462Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi200RoundedFacts
    innerPair482RoundedFacts leaf3462RoundedFacts (by rfl)

private theorem leaf3462FlatSound : Sound leaf3462Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3462CertificateValid
    leaf3462InnerLogValid leaf3462CoversExact leaf3462LowerChecked

private noncomputable def leaf3463Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3463Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431519232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2005507963/1073741824) }, upper := { exponent := 0, mantissa := (3863/2048) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868441087/274863038464) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3463InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3463LocalValidity :
    LeafFacts leaf3463Box leaf3463Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3463Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431519232) }) = true
      norm_num [leaf3463Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3463CertificateValid :
    WideCertificateValid leaf3463Box leaf3463Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi200ValidityFacts
    leaf3463LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3463CoverageChecked :
    coverageCheck (innerAD leaf3463Box) leaf3463InnerLog = true := by
  rfl'

private theorem leaf3463InnerLogValid :
    leaf3463InnerLog.Valid 8 (innerAD leaf3463Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3463CoverageChecked

private noncomputable def leaf3463InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3463InputLogOnePlusV_eq :
    leaf3463InputLogOnePlusV = outerEnclosure 24
      (leaf3463Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3463RoundedFacts : LeafRoundedFacts 8
    leaf3463Certificate.logOnePlusV leaf3463InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3463InputLogOnePlusV_eq }

private noncomputable def leaf3463Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi200InputQChi innerPair482Input
    leaf3463InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3463LowerChecked :
    lowerCheck 24 leaf3463Box leaf3463Inputs = true := by
  rfl'

private theorem leaf3463CoversExact : CoversExact 8
    leaf3463Box leaf3463Certificate leaf3463InnerLog leaf3463Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi200RoundedFacts
    innerPair482RoundedFacts leaf3463RoundedFacts (by rfl)

private theorem leaf3463FlatSound : Sound leaf3463Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3463CertificateValid
    leaf3463InnerLogValid leaf3463CoversExact leaf3463LowerChecked

private noncomputable def leaf3464Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3464Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431612928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1993515607/1073741824) }, upper := { exponent := 0, mantissa := (30721/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868534783/274863225856) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3464InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf3464LocalValidity :
    LeafFacts leaf3464Box leaf3464Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3464Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431612928) }) = true
      norm_num [leaf3464Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3464CertificateValid :
    WideCertificateValid leaf3464Box leaf3464Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi199ValidityFacts
    leaf3464LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3464CoverageChecked :
    coverageCheck (innerAD leaf3464Box) leaf3464InnerLog = true := by
  rfl'

private theorem leaf3464InnerLogValid :
    leaf3464InnerLog.Valid 8 (innerAD leaf3464Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf3464CoverageChecked

private noncomputable def leaf3464InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3464InputLogOnePlusV_eq :
    leaf3464InputLogOnePlusV = outerEnclosure 24
      (leaf3464Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3464RoundedFacts : LeafRoundedFacts 8
    leaf3464Certificate.logOnePlusV leaf3464InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3464InputLogOnePlusV_eq }

private noncomputable def leaf3464Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi199InputQChi innerPair199Input
    leaf3464InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3464LowerChecked :
    lowerCheck 24 leaf3464Box leaf3464Inputs = true := by
  rfl'

private theorem leaf3464CoversExact : CoversExact 8
    leaf3464Box leaf3464Certificate leaf3464InnerLog leaf3464Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi199RoundedFacts
    innerPair199RoundedFacts leaf3464RoundedFacts (by rfl)

private theorem leaf3464FlatSound : Sound leaf3464Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3464CertificateValid
    leaf3464InnerLogValid leaf3464CoversExact leaf3464LowerChecked

private noncomputable def leaf3465Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3465Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486316544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1997316461/1073741824) }, upper := { exponent := 0, mantissa := (7695/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973700915/54972633088) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3465InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3465LocalValidity :
    LeafFacts leaf3465Box leaf3465Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3465Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486316544) }) = true
      norm_num [leaf3465Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3465CertificateValid :
    WideCertificateValid leaf3465Box leaf3465Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi199ValidityFacts
    leaf3465LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3465CoverageChecked :
    coverageCheck (innerAD leaf3465Box) leaf3465InnerLog = true := by
  rfl'

private theorem leaf3465InnerLogValid :
    leaf3465InnerLog.Valid 8 (innerAD leaf3465Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3465CoverageChecked

private noncomputable def leaf3465InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3465InputLogOnePlusV_eq :
    leaf3465InputLogOnePlusV = outerEnclosure 24
      (leaf3465Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3465RoundedFacts : LeafRoundedFacts 8
    leaf3465Certificate.logOnePlusV leaf3465InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3465InputLogOnePlusV_eq }

private noncomputable def leaf3465Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi199InputQChi innerPair482Input
    leaf3465InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3465LowerChecked :
    lowerCheck 24 leaf3465Box leaf3465Inputs = true := by
  rfl'

private theorem leaf3465CoversExact : CoversExact 8
    leaf3465Box leaf3465Certificate leaf3465InnerLog leaf3465Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi199RoundedFacts
    innerPair482RoundedFacts leaf3465RoundedFacts (by rfl)

private theorem leaf3465FlatSound : Sound leaf3465Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3465CertificateValid
    leaf3465InnerLogValid leaf3465CoversExact leaf3465LowerChecked

private noncomputable def leaf3466Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3466Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431488512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2009374349/1073741824) }, upper := { exponent := 0, mantissa := (7741/4096) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868410367/274862977024) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3466InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3466LocalValidity :
    LeafFacts leaf3466Box leaf3466Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3466Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431488512) }) = true
      norm_num [leaf3466Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3466CertificateValid :
    WideCertificateValid leaf3466Box leaf3466Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi200ValidityFacts
    leaf3466LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3466CoverageChecked :
    coverageCheck (innerAD leaf3466Box) leaf3466InnerLog = true := by
  rfl'

private theorem leaf3466InnerLogValid :
    leaf3466InnerLog.Valid 8 (innerAD leaf3466Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3466CoverageChecked

private noncomputable def leaf3466InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3466InputLogOnePlusV_eq :
    leaf3466InputLogOnePlusV = outerEnclosure 24
      (leaf3466Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3466RoundedFacts : LeafRoundedFacts 8
    leaf3466Certificate.logOnePlusV leaf3466InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3466InputLogOnePlusV_eq }

private noncomputable def leaf3466Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi200InputQChi innerPair482Input
    leaf3466InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3466LowerChecked :
    lowerCheck 24 leaf3466Box leaf3466Inputs = true := by
  rfl'

private theorem leaf3466CoversExact : CoversExact 8
    leaf3466Box leaf3466Certificate leaf3466InnerLog leaf3466Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi200RoundedFacts
    innerPair482RoundedFacts leaf3466RoundedFacts (by rfl)

private theorem leaf3466FlatSound : Sound leaf3466Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3466CertificateValid
    leaf3466InnerLogValid leaf3466CoversExact leaf3466LowerChecked

private noncomputable def leaf3467Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3467Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431457792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2013240735/1073741824) }, upper := { exponent := 0, mantissa := (1939/1024) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868379647/274862915584) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3467InnerLog : WideLogData :=
  innerPair483Data

set_option maxRecDepth 1000000 in
private theorem leaf3467LocalValidity :
    LeafFacts leaf3467Box leaf3467Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3467Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431457792) }) = true
      norm_num [leaf3467Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3467CertificateValid :
    WideCertificateValid leaf3467Box leaf3467Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi200ValidityFacts
    leaf3467LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3467CoverageChecked :
    coverageCheck (innerAD leaf3467Box) leaf3467InnerLog = true := by
  rfl'

private theorem leaf3467InnerLogValid :
    leaf3467InnerLog.Valid 8 (innerAD leaf3467Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint70PositiveFacts.valid leaf3467CoverageChecked

private noncomputable def leaf3467InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3467InputLogOnePlusV_eq :
    leaf3467InputLogOnePlusV = outerEnclosure 24
      (leaf3467Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3467RoundedFacts : LeafRoundedFacts 8
    leaf3467Certificate.logOnePlusV leaf3467InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3467InputLogOnePlusV_eq }

private noncomputable def leaf3467Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi200InputQChi innerPair483Input
    leaf3467InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3467LowerChecked :
    lowerCheck 24 leaf3467Box leaf3467Inputs = true := by
  rfl'

private theorem leaf3467CoversExact : CoversExact 8
    leaf3467Box leaf3467Certificate leaf3467InnerLog leaf3467Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi200RoundedFacts
    innerPair483RoundedFacts leaf3467RoundedFacts (by rfl)

private theorem leaf3467FlatSound : Sound leaf3467Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3467CertificateValid
    leaf3467InnerLogValid leaf3467CoversExact leaf3467LowerChecked

private noncomputable def leaf3468Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3468Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431803392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1969137703/1073741824) }, upper := { exponent := 0, mantissa := (30349/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868725247/274863606784) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3468InnerLog : WideLogData :=
  innerPair214Data

set_option maxRecDepth 1000000 in
private theorem leaf3468LocalValidity :
    LeafFacts leaf3468Box leaf3468Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3468Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431803392) }) = true
      norm_num [leaf3468Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3468CertificateValid :
    WideCertificateValid leaf3468Box leaf3468Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi201ValidityFacts
    leaf3468LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3468CoverageChecked :
    coverageCheck (innerAD leaf3468Box) leaf3468InnerLog = true := by
  rfl'

private theorem leaf3468InnerLogValid :
    leaf3468InnerLog.Valid 8 (innerAD leaf3468Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint211PositiveFacts.valid leaf3468CoverageChecked

private noncomputable def leaf3468InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3468InputLogOnePlusV_eq :
    leaf3468InputLogOnePlusV = outerEnclosure 24
      (leaf3468Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3468RoundedFacts : LeafRoundedFacts 8
    leaf3468Certificate.logOnePlusV leaf3468InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3468InputLogOnePlusV_eq }

private noncomputable def leaf3468Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi201InputQChi innerPair214Input
    leaf3468InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3468LowerChecked :
    lowerCheck 24 leaf3468Box leaf3468Inputs = true := by
  rfl'

private theorem leaf3468CoversExact : CoversExact 8
    leaf3468Box leaf3468Certificate leaf3468InnerLog leaf3468Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi201RoundedFacts
    innerPair214RoundedFacts leaf3468RoundedFacts (by rfl)

private theorem leaf3468FlatSound : Sound leaf3468Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3468CertificateValid
    leaf3468InnerLogValid leaf3468CoversExact leaf3468LowerChecked

private noncomputable def leaf3469Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3469Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431774208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1972807493/1073741824) }, upper := { exponent := 0, mantissa := (15203/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868696063/274863548416) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3469InnerLog : WideLogData :=
  innerPair214Data

set_option maxRecDepth 1000000 in
private theorem leaf3469LocalValidity :
    LeafFacts leaf3469Box leaf3469Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3469Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431774208) }) = true
      norm_num [leaf3469Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3469CertificateValid :
    WideCertificateValid leaf3469Box leaf3469Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi201ValidityFacts
    leaf3469LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3469CoverageChecked :
    coverageCheck (innerAD leaf3469Box) leaf3469InnerLog = true := by
  rfl'

private theorem leaf3469InnerLogValid :
    leaf3469InnerLog.Valid 8 (innerAD leaf3469Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint211PositiveFacts.valid leaf3469CoverageChecked

private noncomputable def leaf3469InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3469InputLogOnePlusV_eq :
    leaf3469InputLogOnePlusV = outerEnclosure 24
      (leaf3469Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3469RoundedFacts : LeafRoundedFacts 8
    leaf3469Certificate.logOnePlusV leaf3469InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3469InputLogOnePlusV_eq }

private noncomputable def leaf3469Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi201InputQChi innerPair214Input
    leaf3469InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3469LowerChecked :
    lowerCheck 24 leaf3469Box leaf3469Inputs = true := by
  rfl'

private theorem leaf3469CoversExact : CoversExact 8
    leaf3469Box leaf3469Certificate leaf3469InnerLog leaf3469Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi201RoundedFacts
    innerPair214RoundedFacts leaf3469RoundedFacts (by rfl)

private theorem leaf3469FlatSound : Sound leaf3469Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3469CertificateValid
    leaf3469InnerLogValid leaf3469CoversExact leaf3469LowerChecked

private noncomputable def leaf3470Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3470Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431677952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1985127509/1073741824) }, upper := { exponent := 0, mantissa := (15297/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868599807/274863355904) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3470InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3470LocalValidity :
    LeafFacts leaf3470Box leaf3470Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3470Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431677952) }) = true
      norm_num [leaf3470Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3470CertificateValid :
    WideCertificateValid leaf3470Box leaf3470Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi202ValidityFacts
    leaf3470LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3470CoverageChecked :
    coverageCheck (innerAD leaf3470Box) leaf3470InnerLog = true := by
  rfl'

private theorem leaf3470InnerLogValid :
    leaf3470InnerLog.Valid 8 (innerAD leaf3470Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3470CoverageChecked

private noncomputable def leaf3470InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3470InputLogOnePlusV_eq :
    leaf3470InputLogOnePlusV = outerEnclosure 24
      (leaf3470Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3470RoundedFacts : LeafRoundedFacts 8
    leaf3470Certificate.logOnePlusV leaf3470InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3470InputLogOnePlusV_eq }

private noncomputable def leaf3470Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3470InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3470LowerChecked :
    lowerCheck 24 leaf3470Box leaf3470Inputs = true := by
  rfl'

private theorem leaf3470CoversExact : CoversExact 8
    leaf3470Box leaf3470Certificate leaf3470InnerLog leaf3470Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3470RoundedFacts (by rfl)

private theorem leaf3470FlatSound : Sound leaf3470Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3470CertificateValid
    leaf3470InnerLogValid leaf3470CoversExact leaf3470LowerChecked

private noncomputable def leaf3471Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3471Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431648256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1988862831/1073741824) }, upper := { exponent := 0, mantissa := (7663/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868570111/274863296512) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3471InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3471LocalValidity :
    LeafFacts leaf3471Box leaf3471Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3471Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431648256) }) = true
      norm_num [leaf3471Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3471CertificateValid :
    WideCertificateValid leaf3471Box leaf3471Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi202ValidityFacts
    leaf3471LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3471CoverageChecked :
    coverageCheck (innerAD leaf3471Box) leaf3471InnerLog = true := by
  rfl'

private theorem leaf3471InnerLogValid :
    leaf3471InnerLog.Valid 8 (innerAD leaf3471Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3471CoverageChecked

private noncomputable def leaf3471InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3471InputLogOnePlusV_eq :
    leaf3471InputLogOnePlusV = outerEnclosure 24
      (leaf3471Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3471RoundedFacts : LeafRoundedFacts 8
    leaf3471Certificate.logOnePlusV leaf3471InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3471InputLogOnePlusV_eq }

private noncomputable def leaf3471Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3471InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3471LowerChecked :
    lowerCheck 24 leaf3471Box leaf3471Inputs = true := by
  rfl'

private theorem leaf3471CoversExact : CoversExact 8
    leaf3471Box leaf3471Certificate leaf3471InnerLog leaf3471Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3471RoundedFacts (by rfl)

private theorem leaf3471FlatSound : Sound leaf3471Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3471CertificateValid
    leaf3471InnerLogValid leaf3471CoversExact leaf3471LowerChecked

private noncomputable def leaf3472Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3472Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431745024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1976477283/1073741824) }, upper := { exponent := 0, mantissa := (30463/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868666879/274863490048) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3472InnerLog : WideLogData :=
  innerPair214Data

set_option maxRecDepth 1000000 in
private theorem leaf3472LocalValidity :
    LeafFacts leaf3472Box leaf3472Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3472Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431745024) }) = true
      norm_num [leaf3472Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3472CertificateValid :
    WideCertificateValid leaf3472Box leaf3472Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi201ValidityFacts
    leaf3472LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3472CoverageChecked :
    coverageCheck (innerAD leaf3472Box) leaf3472InnerLog = true := by
  rfl'

private theorem leaf3472InnerLogValid :
    leaf3472InnerLog.Valid 8 (innerAD leaf3472Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint211PositiveFacts.valid leaf3472CoverageChecked

private noncomputable def leaf3472InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3472InputLogOnePlusV_eq :
    leaf3472InputLogOnePlusV = outerEnclosure 24
      (leaf3472Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3472RoundedFacts : LeafRoundedFacts 8
    leaf3472Certificate.logOnePlusV leaf3472InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3472InputLogOnePlusV_eq }

private noncomputable def leaf3472Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi201InputQChi innerPair214Input
    leaf3472InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3472LowerChecked :
    lowerCheck 24 leaf3472Box leaf3472Inputs = true := by
  rfl'

private theorem leaf3472CoversExact : CoversExact 8
    leaf3472Box leaf3472Certificate leaf3472InnerLog leaf3472Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi201RoundedFacts
    innerPair214RoundedFacts leaf3472RoundedFacts (by rfl)

private theorem leaf3472FlatSound : Sound leaf3472Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3472CertificateValid
    leaf3472InnerLogValid leaf3472CoversExact leaf3472LowerChecked

private noncomputable def leaf3473Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3473Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486343168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1980147073/1073741824) }, upper := { exponent := 0, mantissa := (3815/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973727539/54972686336) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3473InnerLog : WideLogData :=
  innerPair202Data

set_option maxRecDepth 1000000 in
private theorem leaf3473LocalValidity :
    LeafFacts leaf3473Box leaf3473Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3473Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486343168) }) = true
      norm_num [leaf3473Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3473CertificateValid :
    WideCertificateValid leaf3473Box leaf3473Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi201ValidityFacts
    leaf3473LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3473CoverageChecked :
    coverageCheck (innerAD leaf3473Box) leaf3473InnerLog = true := by
  rfl'

private theorem leaf3473InnerLogValid :
    leaf3473InnerLog.Valid 8 (innerAD leaf3473Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint241PositiveFacts.valid leaf3473CoverageChecked

private noncomputable def leaf3473InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3473InputLogOnePlusV_eq :
    leaf3473InputLogOnePlusV = outerEnclosure 24
      (leaf3473Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3473RoundedFacts : LeafRoundedFacts 8
    leaf3473Certificate.logOnePlusV leaf3473InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3473InputLogOnePlusV_eq }

private noncomputable def leaf3473Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi201InputQChi innerPair202Input
    leaf3473InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3473LowerChecked :
    lowerCheck 24 leaf3473Box leaf3473Inputs = true := by
  rfl'

private theorem leaf3473CoversExact : CoversExact 8
    leaf3473Box leaf3473Certificate leaf3473InnerLog leaf3473Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi201RoundedFacts
    innerPair202RoundedFacts leaf3473RoundedFacts (by rfl)

private theorem leaf3473FlatSound : Sound leaf3473Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3473CertificateValid
    leaf3473InnerLogValid leaf3473CoversExact leaf3473LowerChecked

private noncomputable def leaf3474Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3474Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054035968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1992598153/1073741824) }, upper := { exponent := 0, mantissa := (15355/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108189787/6108071936) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3474InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3474LocalValidity :
    LeafFacts leaf3474Box leaf3474Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3474Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054035968) }) = true
      norm_num [leaf3474Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3474CertificateValid :
    WideCertificateValid leaf3474Box leaf3474Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi202ValidityFacts
    leaf3474LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3474CoverageChecked :
    coverageCheck (innerAD leaf3474Box) leaf3474InnerLog = true := by
  rfl'

private theorem leaf3474InnerLogValid :
    leaf3474InnerLog.Valid 8 (innerAD leaf3474Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3474CoverageChecked

private noncomputable def leaf3474InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3474InputLogOnePlusV_eq :
    leaf3474InputLogOnePlusV = outerEnclosure 24
      (leaf3474Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3474RoundedFacts : LeafRoundedFacts 8
    leaf3474Certificate.logOnePlusV leaf3474InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3474InputLogOnePlusV_eq }

private noncomputable def leaf3474Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3474InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3474LowerChecked :
    lowerCheck 24 leaf3474Box leaf3474Inputs = true := by
  rfl'

private theorem leaf3474CoversExact : CoversExact 8
    leaf3474Box leaf3474Certificate leaf3474InnerLog leaf3474Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3474RoundedFacts (by rfl)

private theorem leaf3474FlatSound : Sound leaf3474Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3474CertificateValid
    leaf3474InnerLogValid leaf3474CoversExact leaf3474LowerChecked

private noncomputable def leaf3475Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3475Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431588864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1996333475/1073741824) }, upper := { exponent := 0, mantissa := (1923/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868510719/274863177728) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3475InnerLog : WideLogData :=
  innerPair510Data

set_option maxRecDepth 1000000 in
private theorem leaf3475LocalValidity :
    LeafFacts leaf3475Box leaf3475Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3475Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431588864) }) = true
      norm_num [leaf3475Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3475CertificateValid :
    WideCertificateValid leaf3475Box leaf3475Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi202ValidityFacts
    leaf3475LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3475CoverageChecked :
    coverageCheck (innerAD leaf3475Box) leaf3475InnerLog = true := by
  rfl'

private theorem leaf3475InnerLogValid :
    leaf3475InnerLog.Valid 8 (innerAD leaf3475Box) :=
  wideLogDataValid_of_cachedCheck endpoint238PositiveFacts
    endpoint242PositiveFacts.valid leaf3475CoverageChecked

private noncomputable def leaf3475InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3475InputLogOnePlusV_eq :
    leaf3475InputLogOnePlusV = outerEnclosure 24
      (leaf3475Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3475RoundedFacts : LeafRoundedFacts 8
    leaf3475Certificate.logOnePlusV leaf3475InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3475InputLogOnePlusV_eq }

private noncomputable def leaf3475Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi202InputQChi innerPair510Input
    leaf3475InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3475LowerChecked :
    lowerCheck 24 leaf3475Box leaf3475Inputs = true := by
  rfl'

private theorem leaf3475CoversExact : CoversExact 8
    leaf3475Box leaf3475Certificate leaf3475InnerLog leaf3475Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi202RoundedFacts
    innerPair510RoundedFacts leaf3475RoundedFacts (by rfl)

private theorem leaf3475FlatSound : Sound leaf3475Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3475CertificateValid
    leaf3475InnerLogValid leaf3475CoversExact leaf3475LowerChecked

private noncomputable def leaf3476Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3476Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810517504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2001117315/1073741824) }, upper := { exponent := 0, mantissa := (30839/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622824789/91621035008) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3476InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3476LocalValidity :
    LeafFacts leaf3476Box leaf3476Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3476Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810517504) }) = true
      norm_num [leaf3476Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3476CertificateValid :
    WideCertificateValid leaf3476Box leaf3476Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi199ValidityFacts
    leaf3476LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3476CoverageChecked :
    coverageCheck (innerAD leaf3476Box) leaf3476InnerLog = true := by
  rfl'

private theorem leaf3476InnerLogValid :
    leaf3476InnerLog.Valid 8 (innerAD leaf3476Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3476CoverageChecked

private noncomputable def leaf3476InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3476InputLogOnePlusV_eq :
    leaf3476InputLogOnePlusV = outerEnclosure 24
      (leaf3476Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3476RoundedFacts : LeafRoundedFacts 8
    leaf3476Certificate.logOnePlusV leaf3476InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3476InputLogOnePlusV_eq }

private noncomputable def leaf3476Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi199InputQChi innerPair482Input
    leaf3476InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3476LowerChecked :
    lowerCheck 24 leaf3476Box leaf3476Inputs = true := by
  rfl'

private theorem leaf3476CoversExact : CoversExact 8
    leaf3476Box leaf3476Certificate leaf3476InnerLog leaf3476Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi199RoundedFacts
    innerPair482RoundedFacts leaf3476RoundedFacts (by rfl)

private theorem leaf3476FlatSound : Sound leaf3476Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3476CertificateValid
    leaf3476InnerLogValid leaf3476CoversExact leaf3476LowerChecked

private noncomputable def leaf3477Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3477Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431522304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2004918169/1073741824) }, upper := { exponent := 0, mantissa := (15449/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868444159/274863044608) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3477InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3477LocalValidity :
    LeafFacts leaf3477Box leaf3477Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3477Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431522304) }) = true
      norm_num [leaf3477Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3477CertificateValid :
    WideCertificateValid leaf3477Box leaf3477Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi199ValidityFacts
    leaf3477LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3477CoverageChecked :
    coverageCheck (innerAD leaf3477Box) leaf3477InnerLog = true := by
  rfl'

private theorem leaf3477InnerLogValid :
    leaf3477InnerLog.Valid 8 (innerAD leaf3477Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3477CoverageChecked

private noncomputable def leaf3477InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3477InputLogOnePlusV_eq :
    leaf3477InputLogOnePlusV = outerEnclosure 24
      (leaf3477Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3477RoundedFacts : LeafRoundedFacts 8
    leaf3477Certificate.logOnePlusV leaf3477InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3477InputLogOnePlusV_eq }

private noncomputable def leaf3477Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi199InputQChi innerPair482Input
    leaf3477InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3477LowerChecked :
    lowerCheck 24 leaf3477Box leaf3477Inputs = true := by
  rfl'

private theorem leaf3477CoversExact : CoversExact 8
    leaf3477Box leaf3477Certificate leaf3477InnerLog leaf3477Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi199RoundedFacts
    innerPair482RoundedFacts leaf3477RoundedFacts (by rfl)

private theorem leaf3477FlatSound : Sound leaf3477Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3477CertificateValid
    leaf3477InnerLogValid leaf3477CoversExact leaf3477LowerChecked

private noncomputable def leaf3478Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3478Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431427072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2017107121/1073741824) }, upper := { exponent := 0, mantissa := (7771/4096) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868348927/274862854144) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3478InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3478LocalValidity :
    LeafFacts leaf3478Box leaf3478Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3478Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431427072) }) = true
      norm_num [leaf3478Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3478CertificateValid :
    WideCertificateValid leaf3478Box leaf3478Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi200ValidityFacts
    leaf3478LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3478CoverageChecked :
    coverageCheck (innerAD leaf3478Box) leaf3478InnerLog = true := by
  rfl'

private theorem leaf3478InnerLogValid :
    leaf3478InnerLog.Valid 8 (innerAD leaf3478Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3478CoverageChecked

private noncomputable def leaf3478InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3478InputLogOnePlusV_eq :
    leaf3478InputLogOnePlusV = outerEnclosure 24
      (leaf3478Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3478RoundedFacts : LeafRoundedFacts 8
    leaf3478Certificate.logOnePlusV leaf3478InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3478InputLogOnePlusV_eq }

private noncomputable def leaf3478Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi200InputQChi innerPair103Input
    leaf3478InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3478LowerChecked :
    lowerCheck 24 leaf3478Box leaf3478Inputs = true := by
  rfl'

private theorem leaf3478CoversExact : CoversExact 8
    leaf3478Box leaf3478Certificate leaf3478InnerLog leaf3478Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi200RoundedFacts
    innerPair103RoundedFacts leaf3478RoundedFacts (by rfl)

private theorem leaf3478FlatSound : Sound leaf3478Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3478CertificateValid
    leaf3478InnerLogValid leaf3478CoversExact leaf3478LowerChecked

private noncomputable def leaf3479Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3479Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431396352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2020973507/1073741824) }, upper := { exponent := 0, mantissa := (3893/2048) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868318207/274862792704) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3479InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3479LocalValidity :
    LeafFacts leaf3479Box leaf3479Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3479Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431396352) }) = true
      norm_num [leaf3479Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3479CertificateValid :
    WideCertificateValid leaf3479Box leaf3479Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi200ValidityFacts
    leaf3479LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3479CoverageChecked :
    coverageCheck (innerAD leaf3479Box) leaf3479InnerLog = true := by
  rfl'

private theorem leaf3479InnerLogValid :
    leaf3479InnerLog.Valid 8 (innerAD leaf3479Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3479CoverageChecked

private noncomputable def leaf3479InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3479InputLogOnePlusV_eq :
    leaf3479InputLogOnePlusV = outerEnclosure 24
      (leaf3479Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3479RoundedFacts : LeafRoundedFacts 8
    leaf3479Certificate.logOnePlusV leaf3479InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3479InputLogOnePlusV_eq }

private noncomputable def leaf3479Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi200InputQChi innerPair103Input
    leaf3479InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3479LowerChecked :
    lowerCheck 24 leaf3479Box leaf3479Inputs = true := by
  rfl'

private theorem leaf3479CoversExact : CoversExact 8
    leaf3479Box leaf3479Certificate leaf3479InnerLog leaf3479Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi200RoundedFacts
    innerPair103RoundedFacts leaf3479RoundedFacts (by rfl)

private theorem leaf3479FlatSound : Sound leaf3479Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3479CertificateValid
    leaf3479InnerLogValid leaf3479CoversExact leaf3479LowerChecked

private noncomputable def leaf3480Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3480Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431492096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2008719023/1073741824) }, upper := { exponent := 0, mantissa := (30957/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868413951/274862984192) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3480InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3480LocalValidity :
    LeafFacts leaf3480Box leaf3480Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3480Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431492096) }) = true
      norm_num [leaf3480Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3480CertificateValid :
    WideCertificateValid leaf3480Box leaf3480Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi199ValidityFacts
    leaf3480LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3480CoverageChecked :
    coverageCheck (innerAD leaf3480Box) leaf3480InnerLog = true := by
  rfl'

private theorem leaf3480InnerLogValid :
    leaf3480InnerLog.Valid 8 (innerAD leaf3480Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3480CoverageChecked

private noncomputable def leaf3480InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3480InputLogOnePlusV_eq :
    leaf3480InputLogOnePlusV = outerEnclosure 24
      (leaf3480Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3480RoundedFacts : LeafRoundedFacts 8
    leaf3480Certificate.logOnePlusV leaf3480InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3480InputLogOnePlusV_eq }

private noncomputable def leaf3480Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi199InputQChi innerPair482Input
    leaf3480InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3480LowerChecked :
    lowerCheck 24 leaf3480Box leaf3480Inputs = true := by
  rfl'

private theorem leaf3480CoversExact : CoversExact 8
    leaf3480Box leaf3480Certificate leaf3480InnerLog leaf3480Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi199RoundedFacts
    innerPair482RoundedFacts leaf3480RoundedFacts (by rfl)

private theorem leaf3480FlatSound : Sound leaf3480Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3480CertificateValid
    leaf3480InnerLogValid leaf3480CoversExact leaf3480LowerChecked

private noncomputable def leaf3481Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3481Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090054144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2012519877/1073741824) }, upper := { exponent := 0, mantissa := (3877/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180310509/10180108288) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3481InnerLog : WideLogData :=
  innerPair514Data

set_option maxRecDepth 1000000 in
private theorem leaf3481LocalValidity :
    LeafFacts leaf3481Box leaf3481Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3481Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090054144) }) = true
      norm_num [leaf3481Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3481CertificateValid :
    WideCertificateValid leaf3481Box leaf3481Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi199ValidityFacts
    leaf3481LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3481CoverageChecked :
    coverageCheck (innerAD leaf3481Box) leaf3481InnerLog = true := by
  rfl'

private theorem leaf3481InnerLogValid :
    leaf3481InnerLog.Valid 8 (innerAD leaf3481Box) :=
  wideLogDataValid_of_cachedCheck endpoint243PositiveFacts
    endpoint244PositiveFacts.valid leaf3481CoverageChecked

private noncomputable def leaf3481InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3481InputLogOnePlusV_eq :
    leaf3481InputLogOnePlusV = outerEnclosure 24
      (leaf3481Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3481RoundedFacts : LeafRoundedFacts 8
    leaf3481Certificate.logOnePlusV leaf3481InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3481InputLogOnePlusV_eq }

private noncomputable def leaf3481Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi199InputQChi innerPair514Input
    leaf3481InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3481LowerChecked :
    lowerCheck 24 leaf3481Box leaf3481Inputs = true := by
  rfl'

private theorem leaf3481CoversExact : CoversExact 8
    leaf3481Box leaf3481Certificate leaf3481InnerLog leaf3481Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi199RoundedFacts
    innerPair514RoundedFacts leaf3481RoundedFacts (by rfl)

private theorem leaf3481FlatSound : Sound leaf3481Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3481CertificateValid
    leaf3481InnerLogValid leaf3481CoversExact leaf3481LowerChecked

private noncomputable def leaf3482Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3482Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431365632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2024839893/1073741824) }, upper := { exponent := 0, mantissa := (7801/4096) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868287487/274862731264) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3482InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3482LocalValidity :
    LeafFacts leaf3482Box leaf3482Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3482Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431365632) }) = true
      norm_num [leaf3482Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3482CertificateValid :
    WideCertificateValid leaf3482Box leaf3482Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi200ValidityFacts
    leaf3482LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3482CoverageChecked :
    coverageCheck (innerAD leaf3482Box) leaf3482InnerLog = true := by
  rfl'

private theorem leaf3482InnerLogValid :
    leaf3482InnerLog.Valid 8 (innerAD leaf3482Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3482CoverageChecked

private noncomputable def leaf3482InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3482InputLogOnePlusV_eq :
    leaf3482InputLogOnePlusV = outerEnclosure 24
      (leaf3482Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3482RoundedFacts : LeafRoundedFacts 8
    leaf3482Certificate.logOnePlusV leaf3482InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3482InputLogOnePlusV_eq }

private noncomputable def leaf3482Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi200InputQChi innerPair103Input
    leaf3482InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3482LowerChecked :
    lowerCheck 24 leaf3482Box leaf3482Inputs = true := by
  rfl'

private theorem leaf3482CoversExact : CoversExact 8
    leaf3482Box leaf3482Certificate leaf3482InnerLog leaf3482Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi200RoundedFacts
    innerPair103RoundedFacts leaf3482RoundedFacts (by rfl)

private theorem leaf3482FlatSound : Sound leaf3482Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3482CertificateValid
    leaf3482InnerLogValid leaf3482CoversExact leaf3482LowerChecked

private noncomputable def leaf3483Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3483Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431334912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2028706279/1073741824) }, upper := { exponent := 0, mantissa := (977/512) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868256767/274862669824) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3483InnerLog : WideLogData :=
  innerPair515Data

set_option maxRecDepth 1000000 in
private theorem leaf3483LocalValidity :
    LeafFacts leaf3483Box leaf3483Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3483Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431334912) }) = true
      norm_num [leaf3483Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3483CertificateValid :
    WideCertificateValid leaf3483Box leaf3483Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi200ValidityFacts
    leaf3483LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3483CoverageChecked :
    coverageCheck (innerAD leaf3483Box) leaf3483InnerLog = true := by
  rfl'

private theorem leaf3483InnerLogValid :
    leaf3483InnerLog.Valid 8 (innerAD leaf3483Box) :=
  wideLogDataValid_of_cachedCheck endpoint245PositiveFacts
    endpoint246PositiveFacts.valid leaf3483CoverageChecked

private noncomputable def leaf3483InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3483InputLogOnePlusV_eq :
    leaf3483InputLogOnePlusV = outerEnclosure 24
      (leaf3483Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3483RoundedFacts : LeafRoundedFacts 8
    leaf3483Certificate.logOnePlusV leaf3483InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3483InputLogOnePlusV_eq }

private noncomputable def leaf3483Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi200InputQChi innerPair515Input
    leaf3483InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3483LowerChecked :
    lowerCheck 24 leaf3483Box leaf3483Inputs = true := by
  rfl'

private theorem leaf3483CoversExact : CoversExact 8
    leaf3483Box leaf3483Certificate leaf3483InnerLog leaf3483Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi200RoundedFacts
    innerPair515RoundedFacts leaf3483RoundedFacts (by rfl)

private theorem leaf3483FlatSound : Sound leaf3483Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3483CertificateValid
    leaf3483InnerLogValid leaf3483CoversExact leaf3483LowerChecked

private noncomputable def leaf3484Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3484Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162095104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2017369255/1073741824) }, upper := { exponent := 0, mantissa := (31085/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324556561/18324190208) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3484InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3484LocalValidity :
    LeafFacts leaf3484Box leaf3484Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3484Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162095104) }) = true
      norm_num [leaf3484Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3484CertificateValid :
    WideCertificateValid leaf3484Box leaf3484Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi191ValidityFacts
    leaf3484LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3484CoverageChecked :
    coverageCheck (innerAD leaf3484Box) leaf3484InnerLog = true := by
  rfl'

private theorem leaf3484InnerLogValid :
    leaf3484InnerLog.Valid 8 (innerAD leaf3484Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3484CoverageChecked

private noncomputable def leaf3484InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3484InputLogOnePlusV_eq :
    leaf3484InputLogOnePlusV = outerEnclosure 24
      (leaf3484Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3484RoundedFacts : LeafRoundedFacts 8
    leaf3484Certificate.logOnePlusV leaf3484InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3484InputLogOnePlusV_eq }

private noncomputable def leaf3484Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi191InputQChi innerPair103Input
    leaf3484InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3484LowerChecked :
    lowerCheck 24 leaf3484Box leaf3484Inputs = true := by
  rfl'

private theorem leaf3484CoversExact : CoversExact 8
    leaf3484Box leaf3484Certificate leaf3484InnerLog leaf3484Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi191RoundedFacts
    innerPair103RoundedFacts leaf3484RoundedFacts (by rfl)

private theorem leaf3484FlatSound : Sound leaf3484Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3484CertificateValid
    leaf3484InnerLogValid leaf3484CoversExact leaf3484LowerChecked

private noncomputable def leaf3485Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3485Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431395328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2021301173/1073741824) }, upper := { exponent := 0, mantissa := (15573/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868317183/274862790656) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3485InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3485LocalValidity :
    LeafFacts leaf3485Box leaf3485Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3485Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431395328) }) = true
      norm_num [leaf3485Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3485CertificateValid :
    WideCertificateValid leaf3485Box leaf3485Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi191ValidityFacts
    leaf3485LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3485CoverageChecked :
    coverageCheck (innerAD leaf3485Box) leaf3485InnerLog = true := by
  rfl'

private theorem leaf3485InnerLogValid :
    leaf3485InnerLog.Valid 8 (innerAD leaf3485Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3485CoverageChecked

private noncomputable def leaf3485InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3485InputLogOnePlusV_eq :
    leaf3485InputLogOnePlusV = outerEnclosure 24
      (leaf3485Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3485RoundedFacts : LeafRoundedFacts 8
    leaf3485Certificate.logOnePlusV leaf3485InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3485InputLogOnePlusV_eq }

private noncomputable def leaf3485Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi191InputQChi innerPair103Input
    leaf3485InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3485LowerChecked :
    lowerCheck 24 leaf3485Box leaf3485Inputs = true := by
  rfl'

private theorem leaf3485CoversExact : CoversExact 8
    leaf3485Box leaf3485Certificate leaf3485InnerLog leaf3485Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi191RoundedFacts
    innerPair103RoundedFacts leaf3485RoundedFacts (by rfl)

private theorem leaf3485FlatSound : Sound leaf3485Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3485CertificateValid
    leaf3485InnerLogValid leaf3485CoversExact leaf3485LowerChecked

private noncomputable def leaf3486Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3486Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084194304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2033096933/1073741824) }, upper := { exponent := 0, mantissa := (15663/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168719119/16168388608) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3486InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3486LocalValidity :
    LeafFacts leaf3486Box leaf3486Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3486Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084194304) }) = true
      norm_num [leaf3486Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3486CertificateValid :
    WideCertificateValid leaf3486Box leaf3486Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi192ValidityFacts
    leaf3486LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3486CoverageChecked :
    coverageCheck (innerAD leaf3486Box) leaf3486InnerLog = true := by
  rfl'

private theorem leaf3486InnerLogValid :
    leaf3486InnerLog.Valid 8 (innerAD leaf3486Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3486CoverageChecked

private noncomputable def leaf3486InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3486InputLogOnePlusV_eq :
    leaf3486InputLogOnePlusV = outerEnclosure 24
      (leaf3486Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3486RoundedFacts : LeafRoundedFacts 8
    leaf3486Certificate.logOnePlusV leaf3486InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3486InputLogOnePlusV_eq }

private noncomputable def leaf3486Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi192InputQChi innerPair100Input
    leaf3486InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3486LowerChecked :
    lowerCheck 24 leaf3486Box leaf3486Inputs = true := by
  rfl'

private theorem leaf3486CoversExact : CoversExact 8
    leaf3486Box leaf3486Certificate leaf3486InnerLog leaf3486Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi192RoundedFacts
    innerPair100RoundedFacts leaf3486RoundedFacts (by rfl)

private theorem leaf3486FlatSound : Sound leaf3486Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3486CertificateValid
    leaf3486InnerLogValid leaf3486CoversExact leaf3486LowerChecked

private noncomputable def leaf3487Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3487Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810423808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2037094383/1073741824) }, upper := { exponent := 0, mantissa := (7847/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622731093/91620847616) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3487InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3487LocalValidity :
    LeafFacts leaf3487Box leaf3487Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3487Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810423808) }) = true
      norm_num [leaf3487Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3487CertificateValid :
    WideCertificateValid leaf3487Box leaf3487Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi192ValidityFacts
    leaf3487LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3487CoverageChecked :
    coverageCheck (innerAD leaf3487Box) leaf3487InnerLog = true := by
  rfl'

private theorem leaf3487InnerLogValid :
    leaf3487InnerLog.Valid 8 (innerAD leaf3487Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3487CoverageChecked

private noncomputable def leaf3487InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3487InputLogOnePlusV_eq :
    leaf3487InputLogOnePlusV = outerEnclosure 24
      (leaf3487Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3487RoundedFacts : LeafRoundedFacts 8
    leaf3487Certificate.logOnePlusV leaf3487InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3487InputLogOnePlusV_eq }

private noncomputable def leaf3487Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi192InputQChi innerPair100Input
    leaf3487InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3487LowerChecked :
    lowerCheck 24 leaf3487Box leaf3487Inputs = true := by
  rfl'

private theorem leaf3487CoversExact : CoversExact 8
    leaf3487Box leaf3487Certificate leaf3487InnerLog leaf3487Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi192RoundedFacts
    innerPair100RoundedFacts leaf3487RoundedFacts (by rfl)

private theorem leaf3487FlatSound : Sound leaf3487Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3487CertificateValid
    leaf3487InnerLogValid leaf3487CoversExact leaf3487LowerChecked

private noncomputable def leaf3488Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3488Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084197888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2025233091/1073741824) }, upper := { exponent := 0, mantissa := (31207/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168722703/16168395776) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3488InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3488LocalValidity :
    LeafFacts leaf3488Box leaf3488Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3488Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084197888) }) = true
      norm_num [leaf3488Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3488CertificateValid :
    WideCertificateValid leaf3488Box leaf3488Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi191ValidityFacts
    leaf3488LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3488CoverageChecked :
    coverageCheck (innerAD leaf3488Box) leaf3488InnerLog = true := by
  rfl'

private theorem leaf3488InnerLogValid :
    leaf3488InnerLog.Valid 8 (innerAD leaf3488Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3488CoverageChecked

private noncomputable def leaf3488InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3488InputLogOnePlusV_eq :
    leaf3488InputLogOnePlusV = outerEnclosure 24
      (leaf3488Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3488RoundedFacts : LeafRoundedFacts 8
    leaf3488Certificate.logOnePlusV leaf3488InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3488InputLogOnePlusV_eq }

private noncomputable def leaf3488Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi191InputQChi innerPair103Input
    leaf3488InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3488LowerChecked :
    lowerCheck 24 leaf3488Box leaf3488Inputs = true := by
  rfl'

private theorem leaf3488CoversExact : CoversExact 8
    leaf3488Box leaf3488Certificate leaf3488InnerLog leaf3488Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi191RoundedFacts
    innerPair103RoundedFacts leaf3488RoundedFacts (by rfl)

private theorem leaf3488FlatSound : Sound leaf3488Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3488CertificateValid
    leaf3488InnerLogValid leaf3488CoversExact leaf3488LowerChecked

private noncomputable def leaf3489Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3489Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270148096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2029165009/1073741824) }, upper := { exponent := 0, mantissa := (7817/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540917191/30540296192) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3489InnerLog : WideLogData :=
  innerPair106Data

set_option maxRecDepth 1000000 in
private theorem leaf3489LocalValidity :
    LeafFacts leaf3489Box leaf3489Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3489Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270148096) }) = true
      norm_num [leaf3489Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3489CertificateValid :
    WideCertificateValid leaf3489Box leaf3489Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi191ValidityFacts
    leaf3489LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3489CoverageChecked :
    coverageCheck (innerAD leaf3489Box) leaf3489InnerLog = true := by
  rfl'

private theorem leaf3489InnerLogValid :
    leaf3489InnerLog.Valid 8 (innerAD leaf3489Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint81PositiveFacts.valid leaf3489CoverageChecked

private noncomputable def leaf3489InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3489InputLogOnePlusV_eq :
    leaf3489InputLogOnePlusV = outerEnclosure 24
      (leaf3489Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3489RoundedFacts : LeafRoundedFacts 8
    leaf3489Certificate.logOnePlusV leaf3489InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3489InputLogOnePlusV_eq }

private noncomputable def leaf3489Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi191InputQChi innerPair106Input
    leaf3489InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3489LowerChecked :
    lowerCheck 24 leaf3489Box leaf3489Inputs = true := by
  rfl'

private theorem leaf3489CoversExact : CoversExact 8
    leaf3489Box leaf3489Certificate leaf3489InnerLog leaf3489Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi191RoundedFacts
    innerPair106RoundedFacts leaf3489RoundedFacts (by rfl)

private theorem leaf3489FlatSound : Sound leaf3489Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3489CertificateValid
    leaf3489InnerLogValid leaf3489CoversExact leaf3489LowerChecked

private noncomputable def leaf3490Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3490Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486247936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2041091833/1073741824) }, upper := { exponent := 0, mantissa := (15725/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973632307/54972495872) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3490InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3490LocalValidity :
    LeafFacts leaf3490Box leaf3490Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3490Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486247936) }) = true
      norm_num [leaf3490Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3490CertificateValid :
    WideCertificateValid leaf3490Box leaf3490Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi192ValidityFacts
    leaf3490LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3490CoverageChecked :
    coverageCheck (innerAD leaf3490Box) leaf3490InnerLog = true := by
  rfl'

private theorem leaf3490InnerLogValid :
    leaf3490InnerLog.Valid 8 (innerAD leaf3490Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3490CoverageChecked

private noncomputable def leaf3490InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3490InputLogOnePlusV_eq :
    leaf3490InputLogOnePlusV = outerEnclosure 24
      (leaf3490Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3490RoundedFacts : LeafRoundedFacts 8
    leaf3490Certificate.logOnePlusV leaf3490InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3490InputLogOnePlusV_eq }

private noncomputable def leaf3490Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi192InputQChi innerPair100Input
    leaf3490InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3490LowerChecked :
    lowerCheck 24 leaf3490Box leaf3490Inputs = true := by
  rfl'

private theorem leaf3490CoversExact : CoversExact 8
    leaf3490Box leaf3490Certificate leaf3490InnerLog leaf3490Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi192RoundedFacts
    innerPair100RoundedFacts leaf3490RoundedFacts (by rfl)

private theorem leaf3490FlatSound : Sound leaf3490Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3490CertificateValid
    leaf3490InnerLogValid leaf3490CoversExact leaf3490LowerChecked

private noncomputable def leaf3491Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3491Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431207936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2045089283/1073741824) }, upper := { exponent := 0, mantissa := (3939/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868129791/274862415872) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3491InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3491LocalValidity :
    LeafFacts leaf3491Box leaf3491Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3491Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431207936) }) = true
      norm_num [leaf3491Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3491CertificateValid :
    WideCertificateValid leaf3491Box leaf3491Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi192ValidityFacts
    leaf3491LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3491CoverageChecked :
    coverageCheck (innerAD leaf3491Box) leaf3491InnerLog = true := by
  rfl'

private theorem leaf3491InnerLogValid :
    leaf3491InnerLog.Valid 8 (innerAD leaf3491Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3491CoverageChecked

private noncomputable def leaf3491InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3491InputLogOnePlusV_eq :
    leaf3491InputLogOnePlusV = outerEnclosure 24
      (leaf3491Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3491RoundedFacts : LeafRoundedFacts 8
    leaf3491Certificate.logOnePlusV leaf3491InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3491InputLogOnePlusV_eq }

private noncomputable def leaf3491Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi192InputQChi innerPair100Input
    leaf3491InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3491LowerChecked :
    lowerCheck 24 leaf3491Box leaf3491Inputs = true := by
  rfl'

private theorem leaf3491CoversExact : CoversExact 8
    leaf3491Box leaf3491Certificate leaf3491InnerLog leaf3491Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi192RoundedFacts
    innerPair100RoundedFacts leaf3491RoundedFacts (by rfl)

private theorem leaf3491FlatSound : Sound leaf3491Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3491CertificateValid
    leaf3491InnerLogValid leaf3491CoversExact leaf3491LowerChecked

private noncomputable def leaf3492Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3492Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431179776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2048824611/1073741824) }, upper := { exponent := 0, mantissa := (31567/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868101631/274862359552) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3492InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3492LocalValidity :
    LeafFacts leaf3492Box leaf3492Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3492Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431179776) }) = true
      norm_num [leaf3492Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3492CertificateValid :
    WideCertificateValid leaf3492Box leaf3492Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi189ValidityFacts
    leaf3492LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3492CoverageChecked :
    coverageCheck (innerAD leaf3492Box) leaf3492InnerLog = true := by
  rfl'

private theorem leaf3492InnerLogValid :
    leaf3492InnerLog.Valid 8 (innerAD leaf3492Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3492CoverageChecked

private noncomputable def leaf3492InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3492InputLogOnePlusV_eq :
    leaf3492InputLogOnePlusV = outerEnclosure 24
      (leaf3492Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3492RoundedFacts : LeafRoundedFacts 8
    leaf3492Certificate.logOnePlusV leaf3492InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3492InputLogOnePlusV_eq }

private noncomputable def leaf3492Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3492InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3492LowerChecked :
    lowerCheck 24 leaf3492Box leaf3492Inputs = true := by
  rfl'

private theorem leaf3492CoversExact : CoversExact 8
    leaf3492Box leaf3492Certificate leaf3492InnerLog leaf3492Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3492RoundedFacts (by rfl)

private theorem leaf3492FlatSound : Sound leaf3492Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3492CertificateValid
    leaf3492InnerLogValid leaf3492CoversExact leaf3492LowerChecked

private noncomputable def leaf3493Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3493Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486229504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2052887593/1073741824) }, upper := { exponent := 0, mantissa := (15815/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973613875/54972459008) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3493InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3493LocalValidity :
    LeafFacts leaf3493Box leaf3493Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3493Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486229504) }) = true
      norm_num [leaf3493Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3493CertificateValid :
    WideCertificateValid leaf3493Box leaf3493Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi189ValidityFacts
    leaf3493LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3493CoverageChecked :
    coverageCheck (innerAD leaf3493Box) leaf3493InnerLog = true := by
  rfl'

private theorem leaf3493InnerLogValid :
    leaf3493InnerLog.Valid 8 (innerAD leaf3493Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3493CoverageChecked

private noncomputable def leaf3493InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3493InputLogOnePlusV_eq :
    leaf3493InputLogOnePlusV = outerEnclosure 24
      (leaf3493Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3493RoundedFacts : LeafRoundedFacts 8
    leaf3493Certificate.logOnePlusV leaf3493InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3493InputLogOnePlusV_eq }

private noncomputable def leaf3493Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3493InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3493LowerChecked :
    lowerCheck 24 leaf3493Box leaf3493Inputs = true := by
  rfl'

private theorem leaf3493CoversExact : CoversExact 8
    leaf3493Box leaf3493Certificate leaf3493InnerLog leaf3493Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3493RoundedFacts (by rfl)

private theorem leaf3493FlatSound : Sound leaf3493Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3493CertificateValid
    leaf3493InnerLogValid leaf3493CoversExact leaf3493LowerChecked

private noncomputable def leaf3494Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3494Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742433/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270117376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2064552289/1073741824) }, upper := { exponent := 0, mantissa := (497/256) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540886471/30540234752) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3494InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3494LocalValidity :
    LeafFacts leaf3494Box leaf3494Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3494Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270117376) }) = true
      norm_num [leaf3494Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3494CertificateValid :
    WideCertificateValid leaf3494Box leaf3494Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi190ValidityFacts
    leaf3494LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3494CoverageChecked :
    coverageCheck (innerAD leaf3494Box) leaf3494InnerLog = true := by
  rfl'

private theorem leaf3494InnerLogValid :
    leaf3494InnerLog.Valid 8 (innerAD leaf3494Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3494CoverageChecked

private noncomputable def leaf3494InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3494InputLogOnePlusV_eq :
    leaf3494InputLogOnePlusV = outerEnclosure 24
      (leaf3494Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3494RoundedFacts : LeafRoundedFacts 8
    leaf3494Certificate.logOnePlusV leaf3494InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3494InputLogOnePlusV_eq }

private noncomputable def leaf3494Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi190InputQChi innerPair304Input
    leaf3494InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3494LowerChecked :
    lowerCheck 24 leaf3494Box leaf3494Inputs = true := by
  rfl'

private theorem leaf3494CoversExact : CoversExact 8
    leaf3494Box leaf3494Certificate leaf3494InnerLog leaf3494Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi190RoundedFacts
    innerPair304RoundedFacts leaf3494RoundedFacts (by rfl)

private theorem leaf3494FlatSound : Sound leaf3494Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3494CertificateValid
    leaf3494InnerLogValid leaf3494CoversExact leaf3494LowerChecked

private noncomputable def leaf3495Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3495Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431023616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2068680803/1073741824) }, upper := { exponent := 0, mantissa := (249/128) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867945471/274862047232) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3495InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3495LocalValidity :
    LeafFacts leaf3495Box leaf3495Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3495Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431023616) }) = true
      norm_num [leaf3495Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3495CertificateValid :
    WideCertificateValid leaf3495Box leaf3495Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi190ValidityFacts
    leaf3495LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3495CoverageChecked :
    coverageCheck (innerAD leaf3495Box) leaf3495InnerLog = true := by
  rfl'

private theorem leaf3495InnerLogValid :
    leaf3495InnerLog.Valid 8 (innerAD leaf3495Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3495CoverageChecked

private noncomputable def leaf3495InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3495InputLogOnePlusV_eq :
    leaf3495InputLogOnePlusV = outerEnclosure 24
      (leaf3495Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3495RoundedFacts : LeafRoundedFacts 8
    leaf3495Certificate.logOnePlusV leaf3495InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3495InputLogOnePlusV_eq }

private noncomputable def leaf3495Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi190InputQChi innerPair304Input
    leaf3495InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3495LowerChecked :
    lowerCheck 24 leaf3495Box leaf3495Inputs = true := by
  rfl'

private theorem leaf3495CoversExact : CoversExact 8
    leaf3495Box leaf3495Certificate leaf3495InnerLog leaf3495Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi190RoundedFacts
    innerPair304RoundedFacts leaf3495RoundedFacts (by rfl)

private theorem leaf3495FlatSound : Sound leaf3495Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3495CertificateValid
    leaf3495InnerLogValid leaf3495CoversExact leaf3495LowerChecked

private noncomputable def leaf3496Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3496Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196072448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2056950575/1073741824) }, upper := { exponent := 0, mantissa := (31693/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392279933/6392144896) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3496InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3496LocalValidity :
    LeafFacts leaf3496Box leaf3496Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3496Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196072448) }) = true
      norm_num [leaf3496Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3496CertificateValid :
    WideCertificateValid leaf3496Box leaf3496Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi189ValidityFacts
    leaf3496LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3496CoverageChecked :
    coverageCheck (innerAD leaf3496Box) leaf3496InnerLog = true := by
  rfl'

private theorem leaf3496InnerLogValid :
    leaf3496InnerLog.Valid 8 (innerAD leaf3496Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3496CoverageChecked

private noncomputable def leaf3496InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3496InputLogOnePlusV_eq :
    leaf3496InputLogOnePlusV = outerEnclosure 24
      (leaf3496Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3496RoundedFacts : LeafRoundedFacts 8
    leaf3496Certificate.logOnePlusV leaf3496InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3496InputLogOnePlusV_eq }

private noncomputable def leaf3496Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3496InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3496LowerChecked :
    lowerCheck 24 leaf3496Box leaf3496Inputs = true := by
  rfl'

private theorem leaf3496CoversExact : CoversExact 8
    leaf3496Box leaf3496Certificate leaf3496InnerLog leaf3496Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3496RoundedFacts (by rfl)

private theorem leaf3496FlatSound : Sound leaf3496Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3496CertificateValid
    leaf3496InnerLogValid leaf3496CoversExact leaf3496LowerChecked

private noncomputable def leaf3497Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3497Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431083008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2061013557/1073741824) }, upper := { exponent := 0, mantissa := (7939/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868004863/274862166016) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3497InnerLog : WideLogData :=
  innerPair233Data

set_option maxRecDepth 1000000 in
private theorem leaf3497LocalValidity :
    LeafFacts leaf3497Box leaf3497Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3497Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431083008) }) = true
      norm_num [leaf3497Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3497CertificateValid :
    WideCertificateValid leaf3497Box leaf3497Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi189ValidityFacts
    leaf3497LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3497CoverageChecked :
    coverageCheck (innerAD leaf3497Box) leaf3497InnerLog = true := by
  rfl'

private theorem leaf3497InnerLogValid :
    leaf3497InnerLog.Valid 8 (innerAD leaf3497Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint71PositiveFacts.valid leaf3497CoverageChecked

private noncomputable def leaf3497InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3497InputLogOnePlusV_eq :
    leaf3497InputLogOnePlusV = outerEnclosure 24
      (leaf3497Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3497RoundedFacts : LeafRoundedFacts 8
    leaf3497Certificate.logOnePlusV leaf3497InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3497InputLogOnePlusV_eq }

private noncomputable def leaf3497Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi189InputQChi innerPair233Input
    leaf3497InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3497LowerChecked :
    lowerCheck 24 leaf3497Box leaf3497Inputs = true := by
  rfl'

private theorem leaf3497CoversExact : CoversExact 8
    leaf3497Box leaf3497Certificate leaf3497InnerLog leaf3497Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi189RoundedFacts
    innerPair233RoundedFacts leaf3497RoundedFacts (by rfl)

private theorem leaf3497FlatSound : Sound leaf3497Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3497CertificateValid
    leaf3497InnerLogValid leaf3497CoversExact leaf3497LowerChecked

private noncomputable def leaf3498Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3498Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430990848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2072809317/1073741824) }, upper := { exponent := 0, mantissa := (499/256) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867912703/274861981696) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3498InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3498LocalValidity :
    LeafFacts leaf3498Box leaf3498Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3498Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430990848) }) = true
      norm_num [leaf3498Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3498CertificateValid :
    WideCertificateValid leaf3498Box leaf3498Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi190ValidityFacts
    leaf3498LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3498CoverageChecked :
    coverageCheck (innerAD leaf3498Box) leaf3498InnerLog = true := by
  rfl'

private theorem leaf3498InnerLogValid :
    leaf3498InnerLog.Valid 8 (innerAD leaf3498Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3498CoverageChecked

private noncomputable def leaf3498InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3498InputLogOnePlusV_eq :
    leaf3498InputLogOnePlusV = outerEnclosure 24
      (leaf3498Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3498RoundedFacts : LeafRoundedFacts 8
    leaf3498Certificate.logOnePlusV leaf3498InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3498InputLogOnePlusV_eq }

private noncomputable def leaf3498Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi190InputQChi innerPair304Input
    leaf3498InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3498LowerChecked :
    lowerCheck 24 leaf3498Box leaf3498Inputs = true := by
  rfl'

private theorem leaf3498CoversExact : CoversExact 8
    leaf3498Box leaf3498Certificate leaf3498InnerLog leaf3498Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi190RoundedFacts
    innerPair304RoundedFacts leaf3498RoundedFacts (by rfl)

private theorem leaf3498FlatSound : Sound leaf3498Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3498CertificateValid
    leaf3498InnerLogValid leaf3498CoversExact leaf3498LowerChecked

private noncomputable def leaf3499Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3499Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162063872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2076937831/1073741824) }, upper := { exponent := 0, mantissa := (125/64) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324525329/18324127744) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3499InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3499LocalValidity :
    LeafFacts leaf3499Box leaf3499Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3499Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162063872) }) = true
      norm_num [leaf3499Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3499CertificateValid :
    WideCertificateValid leaf3499Box leaf3499Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi190ValidityFacts
    leaf3499LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3499CoverageChecked :
    coverageCheck (innerAD leaf3499Box) leaf3499InnerLog = true := by
  rfl'

private theorem leaf3499InnerLogValid :
    leaf3499InnerLog.Valid 8 (innerAD leaf3499Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3499CoverageChecked

private noncomputable def leaf3499InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3499InputLogOnePlusV_eq :
    leaf3499InputLogOnePlusV = outerEnclosure 24
      (leaf3499Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3499RoundedFacts : LeafRoundedFacts 8
    leaf3499Certificate.logOnePlusV leaf3499InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3499InputLogOnePlusV_eq }

private noncomputable def leaf3499Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi190InputQChi innerPair304Input
    leaf3499InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3499LowerChecked :
    lowerCheck 24 leaf3499Box leaf3499Inputs = true := by
  rfl'

private theorem leaf3499CoversExact : CoversExact 8
    leaf3499Box leaf3499Certificate leaf3499InnerLog leaf3499Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi190RoundedFacts
    innerPair304RoundedFacts leaf3499RoundedFacts (by rfl)

private theorem leaf3499FlatSound : Sound leaf3499Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3499CertificateValid
    leaf3499InnerLogValid leaf3499CoversExact leaf3499LowerChecked

private noncomputable def leaf3500Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3500Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431301632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2033096927/1073741824) }, upper := { exponent := 0, mantissa := (31329/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868223487/274862603264) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3500InnerLog : WideLogData :=
  innerPair229Data

set_option maxRecDepth 1000000 in
private theorem leaf3500LocalValidity :
    LeafFacts leaf3500Box leaf3500Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3500Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431301632) }) = true
      norm_num [leaf3500Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3500CertificateValid :
    WideCertificateValid leaf3500Box leaf3500Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi191ValidityFacts
    leaf3500LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3500CoverageChecked :
    coverageCheck (innerAD leaf3500Box) leaf3500InnerLog = true := by
  rfl'

private theorem leaf3500InnerLogValid :
    leaf3500InnerLog.Valid 8 (innerAD leaf3500Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint81PositiveFacts.valid leaf3500CoverageChecked

private noncomputable def leaf3500InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3500InputLogOnePlusV_eq :
    leaf3500InputLogOnePlusV = outerEnclosure 24
      (leaf3500Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3500RoundedFacts : LeafRoundedFacts 8
    leaf3500Certificate.logOnePlusV leaf3500InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3500InputLogOnePlusV_eq }

private noncomputable def leaf3500Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi191InputQChi innerPair229Input
    leaf3500InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3500LowerChecked :
    lowerCheck 24 leaf3500Box leaf3500Inputs = true := by
  rfl'

private theorem leaf3500CoversExact : CoversExact 8
    leaf3500Box leaf3500Certificate leaf3500InnerLog leaf3500Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi191RoundedFacts
    innerPair229RoundedFacts leaf3500RoundedFacts (by rfl)

private theorem leaf3500FlatSound : Sound leaf3500Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3500CertificateValid
    leaf3500InnerLogValid leaf3500CoversExact leaf3500LowerChecked

private noncomputable def leaf3501Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3501Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486254080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2037028845/1073741824) }, upper := { exponent := 0, mantissa := (15695/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973638451/54972508160) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3501InnerLog : WideLogData :=
  innerPair229Data

set_option maxRecDepth 1000000 in
private theorem leaf3501LocalValidity :
    LeafFacts leaf3501Box leaf3501Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3501Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486254080) }) = true
      norm_num [leaf3501Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3501CertificateValid :
    WideCertificateValid leaf3501Box leaf3501Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi191ValidityFacts
    leaf3501LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3501CoverageChecked :
    coverageCheck (innerAD leaf3501Box) leaf3501InnerLog = true := by
  rfl'

private theorem leaf3501InnerLogValid :
    leaf3501InnerLog.Valid 8 (innerAD leaf3501Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint81PositiveFacts.valid leaf3501CoverageChecked

private noncomputable def leaf3501InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3501InputLogOnePlusV_eq :
    leaf3501InputLogOnePlusV = outerEnclosure 24
      (leaf3501Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3501RoundedFacts : LeafRoundedFacts 8
    leaf3501Certificate.logOnePlusV leaf3501InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3501InputLogOnePlusV_eq }

private noncomputable def leaf3501Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi191InputQChi innerPair229Input
    leaf3501InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3501LowerChecked :
    lowerCheck 24 leaf3501Box leaf3501Inputs = true := by
  rfl'

private theorem leaf3501CoversExact : CoversExact 8
    leaf3501Box leaf3501Certificate leaf3501InnerLog leaf3501Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi191RoundedFacts
    innerPair229RoundedFacts leaf3501RoundedFacts (by rfl)

private theorem leaf3501FlatSound : Sound leaf3501Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3501CertificateValid
    leaf3501InnerLogValid leaf3501CoversExact leaf3501LowerChecked

private noncomputable def leaf3502Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3502Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270130688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2049086733/1073741824) }, upper := { exponent := 0, mantissa := (15787/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540899783/30540261376) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3502InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3502LocalValidity :
    LeafFacts leaf3502Box leaf3502Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3502Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270130688) }) = true
      norm_num [leaf3502Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3502CertificateValid :
    WideCertificateValid leaf3502Box leaf3502Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi192ValidityFacts
    leaf3502LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3502CoverageChecked :
    coverageCheck (innerAD leaf3502Box) leaf3502InnerLog = true := by
  rfl'

private theorem leaf3502InnerLogValid :
    leaf3502InnerLog.Valid 8 (innerAD leaf3502Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3502CoverageChecked

private noncomputable def leaf3502InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3502InputLogOnePlusV_eq :
    leaf3502InputLogOnePlusV = outerEnclosure 24
      (leaf3502Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3502RoundedFacts : LeafRoundedFacts 8
    leaf3502Certificate.logOnePlusV leaf3502InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3502InputLogOnePlusV_eq }

private noncomputable def leaf3502Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi192InputQChi innerPair100Input
    leaf3502InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3502LowerChecked :
    lowerCheck 24 leaf3502Box leaf3502Inputs = true := by
  rfl'

private theorem leaf3502CoversExact : CoversExact 8
    leaf3502Box leaf3502Certificate leaf3502InnerLog leaf3502Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi192RoundedFacts
    innerPair100RoundedFacts leaf3502RoundedFacts (by rfl)

private theorem leaf3502FlatSound : Sound leaf3502Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3502CertificateValid
    leaf3502InnerLogValid leaf3502CoversExact leaf3502LowerChecked

private noncomputable def leaf3503Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3503Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431144448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2053084183/1073741824) }, upper := { exponent := 0, mantissa := (7909/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868066303/274862288896) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3503InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3503LocalValidity :
    LeafFacts leaf3503Box leaf3503Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3503Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431144448) }) = true
      norm_num [leaf3503Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3503CertificateValid :
    WideCertificateValid leaf3503Box leaf3503Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi192ValidityFacts
    leaf3503LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3503CoverageChecked :
    coverageCheck (innerAD leaf3503Box) leaf3503InnerLog = true := by
  rfl'

private theorem leaf3503InnerLogValid :
    leaf3503InnerLog.Valid 8 (innerAD leaf3503Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3503CoverageChecked

private noncomputable def leaf3503InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3503InputLogOnePlusV_eq :
    leaf3503InputLogOnePlusV = outerEnclosure 24
      (leaf3503Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3503RoundedFacts : LeafRoundedFacts 8
    leaf3503Certificate.logOnePlusV leaf3503InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3503InputLogOnePlusV_eq }

private noncomputable def leaf3503Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi192InputQChi innerPair100Input
    leaf3503InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3503LowerChecked :
    lowerCheck 24 leaf3503Box leaf3503Inputs = true := by
  rfl'

private theorem leaf3503CoversExact : CoversExact 8
    leaf3503Box leaf3503Certificate leaf3503InnerLog leaf3503Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi192RoundedFacts
    innerPair100RoundedFacts leaf3503RoundedFacts (by rfl)

private theorem leaf3503FlatSound : Sound leaf3503Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3503CertificateValid
    leaf3503InnerLogValid leaf3503CoversExact leaf3503LowerChecked

private noncomputable def leaf3504Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3504Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810413056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2040960763/1073741824) }, upper := { exponent := 0, mantissa := (31451/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622720341/91620826112) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3504InnerLog : WideLogData :=
  innerPair229Data

set_option maxRecDepth 1000000 in
private theorem leaf3504LocalValidity :
    LeafFacts leaf3504Box leaf3504Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3504Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810413056) }) = true
      norm_num [leaf3504Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3504CertificateValid :
    WideCertificateValid leaf3504Box leaf3504Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi191ValidityFacts
    leaf3504LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3504CoverageChecked :
    coverageCheck (innerAD leaf3504Box) leaf3504InnerLog = true := by
  rfl'

private theorem leaf3504InnerLogValid :
    leaf3504InnerLog.Valid 8 (innerAD leaf3504Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint81PositiveFacts.valid leaf3504CoverageChecked

private noncomputable def leaf3504InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3504InputLogOnePlusV_eq :
    leaf3504InputLogOnePlusV = outerEnclosure 24
      (leaf3504Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3504RoundedFacts : LeafRoundedFacts 8
    leaf3504Certificate.logOnePlusV leaf3504InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3504InputLogOnePlusV_eq }

private noncomputable def leaf3504Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi191InputQChi innerPair229Input
    leaf3504InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3504LowerChecked :
    lowerCheck 24 leaf3504Box leaf3504Inputs = true := by
  rfl'

private theorem leaf3504CoversExact : CoversExact 8
    leaf3504Box leaf3504Certificate leaf3504InnerLog leaf3504Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi191RoundedFacts
    innerPair229RoundedFacts leaf3504RoundedFacts (by rfl)

private theorem leaf3504FlatSound : Sound leaf3504Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3504CertificateValid
    leaf3504InnerLogValid leaf3504CoversExact leaf3504LowerChecked

private noncomputable def leaf3505Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3505Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431207936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2044892681/1073741824) }, upper := { exponent := 0, mantissa := (3939/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868129791/274862415872) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3505InnerLog : WideLogData :=
  innerPair517Data

set_option maxRecDepth 1000000 in
private theorem leaf3505LocalValidity :
    LeafFacts leaf3505Box leaf3505Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3505Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431207936) }) = true
      norm_num [leaf3505Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3505CertificateValid :
    WideCertificateValid leaf3505Box leaf3505Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi191ValidityFacts
    leaf3505LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3505CoverageChecked :
    coverageCheck (innerAD leaf3505Box) leaf3505InnerLog = true := by
  rfl'

private theorem leaf3505InnerLogValid :
    leaf3505InnerLog.Valid 8 (innerAD leaf3505Box) :=
  wideLogDataValid_of_cachedCheck endpoint247PositiveFacts
    endpoint248PositiveFacts.valid leaf3505CoverageChecked

private noncomputable def leaf3505InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3505InputLogOnePlusV_eq :
    leaf3505InputLogOnePlusV = outerEnclosure 24
      (leaf3505Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3505RoundedFacts : LeafRoundedFacts 8
    leaf3505Certificate.logOnePlusV leaf3505InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3505InputLogOnePlusV_eq }

private noncomputable def leaf3505Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi191InputQChi innerPair517Input
    leaf3505InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3505LowerChecked :
    lowerCheck 24 leaf3505Box leaf3505Inputs = true := by
  rfl'

private theorem leaf3505CoversExact : CoversExact 8
    leaf3505Box leaf3505Certificate leaf3505InnerLog leaf3505Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi191RoundedFacts
    innerPair517RoundedFacts leaf3505RoundedFacts (by rfl)

private theorem leaf3505FlatSound : Sound leaf3505Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3505CertificateValid
    leaf3505InnerLogValid leaf3505CoversExact leaf3505LowerChecked

private noncomputable def leaf3506Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3506Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431112704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2057081633/1073741824) }, upper := { exponent := 0, mantissa := (15849/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868034559/274862225408) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3506InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3506LocalValidity :
    LeafFacts leaf3506Box leaf3506Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3506Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431112704) }) = true
      norm_num [leaf3506Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3506CertificateValid :
    WideCertificateValid leaf3506Box leaf3506Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi192ValidityFacts
    leaf3506LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3506CoverageChecked :
    coverageCheck (innerAD leaf3506Box) leaf3506InnerLog = true := by
  rfl'

private theorem leaf3506InnerLogValid :
    leaf3506InnerLog.Valid 8 (innerAD leaf3506Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3506CoverageChecked

private noncomputable def leaf3506InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3506InputLogOnePlusV_eq :
    leaf3506InputLogOnePlusV = outerEnclosure 24
      (leaf3506Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3506RoundedFacts : LeafRoundedFacts 8
    leaf3506Certificate.logOnePlusV leaf3506InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3506InputLogOnePlusV_eq }

private noncomputable def leaf3506Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi192InputQChi innerPair100Input
    leaf3506InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3506LowerChecked :
    lowerCheck 24 leaf3506Box leaf3506Inputs = true := by
  rfl'

private theorem leaf3506CoversExact : CoversExact 8
    leaf3506Box leaf3506Certificate leaf3506InnerLog leaf3506Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi192RoundedFacts
    innerPair100RoundedFacts leaf3506RoundedFacts (by rfl)

private theorem leaf3506FlatSound : Sound leaf3506Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3506CertificateValid
    leaf3506InnerLogValid leaf3506CoversExact leaf3506LowerChecked

private noncomputable def leaf3507Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3507Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162072064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2061079083/1073741824) }, upper := { exponent := 0, mantissa := (1985/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324533521/18324144128) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3507InnerLog : WideLogData :=
  innerPair519Data

set_option maxRecDepth 1000000 in
private theorem leaf3507LocalValidity :
    LeafFacts leaf3507Box leaf3507Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3507Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162072064) }) = true
      norm_num [leaf3507Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3507CertificateValid :
    WideCertificateValid leaf3507Box leaf3507Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi192ValidityFacts
    leaf3507LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3507CoverageChecked :
    coverageCheck (innerAD leaf3507Box) leaf3507InnerLog = true := by
  rfl'

private theorem leaf3507InnerLogValid :
    leaf3507InnerLog.Valid 8 (innerAD leaf3507Box) :=
  wideLogDataValid_of_cachedCheck endpoint249PositiveFacts
    endpoint250PositiveFacts.valid leaf3507CoverageChecked

private noncomputable def leaf3507InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3507InputLogOnePlusV_eq :
    leaf3507InputLogOnePlusV = outerEnclosure 24
      (leaf3507Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3507RoundedFacts : LeafRoundedFacts 8
    leaf3507Certificate.logOnePlusV leaf3507InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3507InputLogOnePlusV_eq }

private noncomputable def leaf3507Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi192InputQChi innerPair519Input
    leaf3507InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3507LowerChecked :
    lowerCheck 24 leaf3507Box leaf3507Inputs = true := by
  rfl'

private theorem leaf3507CoversExact : CoversExact 8
    leaf3507Box leaf3507Certificate leaf3507InnerLog leaf3507Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi192RoundedFacts
    innerPair519RoundedFacts leaf3507RoundedFacts (by rfl)

private theorem leaf3507FlatSound : Sound leaf3507Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3507CertificateValid
    leaf3507InnerLogValid leaf3507CoversExact leaf3507LowerChecked

private noncomputable def leaf3508Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3508Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084179456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2065076539/1073741824) }, upper := { exponent := 0, mantissa := (31819/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168704271/16168358912) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3508InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3508LocalValidity :
    LeafFacts leaf3508Box leaf3508Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3508Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084179456) }) = true
      norm_num [leaf3508Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3508CertificateValid :
    WideCertificateValid leaf3508Box leaf3508Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi189ValidityFacts
    leaf3508LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3508CoverageChecked :
    coverageCheck (innerAD leaf3508Box) leaf3508InnerLog = true := by
  rfl'

private theorem leaf3508InnerLogValid :
    leaf3508InnerLog.Valid 8 (innerAD leaf3508Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3508CoverageChecked

private noncomputable def leaf3508InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3508InputLogOnePlusV_eq :
    leaf3508InputLogOnePlusV = outerEnclosure 24
      (leaf3508Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3508RoundedFacts : LeafRoundedFacts 8
    leaf3508Certificate.logOnePlusV leaf3508InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3508InputLogOnePlusV_eq }

private noncomputable def leaf3508Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi189InputQChi innerPair304Input
    leaf3508InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3508LowerChecked :
    lowerCheck 24 leaf3508Box leaf3508Inputs = true := by
  rfl'

private theorem leaf3508CoversExact : CoversExact 8
    leaf3508Box leaf3508Certificate leaf3508InnerLog leaf3508Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi189RoundedFacts
    innerPair304RoundedFacts leaf3508RoundedFacts (by rfl)

private theorem leaf3508FlatSound : Sound leaf3508Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3508CertificateValid
    leaf3508InnerLogValid leaf3508CoversExact leaf3508LowerChecked

private noncomputable def leaf3509Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3509Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431018496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2069139521/1073741824) }, upper := { exponent := 0, mantissa := (15941/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867940351/274862036992) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3509InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3509LocalValidity :
    LeafFacts leaf3509Box leaf3509Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3509Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431018496) }) = true
      norm_num [leaf3509Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3509CertificateValid :
    WideCertificateValid leaf3509Box leaf3509Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi189ValidityFacts
    leaf3509LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3509CoverageChecked :
    coverageCheck (innerAD leaf3509Box) leaf3509InnerLog = true := by
  rfl'

private theorem leaf3509InnerLogValid :
    leaf3509InnerLog.Valid 8 (innerAD leaf3509Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3509CoverageChecked

private noncomputable def leaf3509InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3509InputLogOnePlusV_eq :
    leaf3509InputLogOnePlusV = outerEnclosure 24
      (leaf3509Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3509RoundedFacts : LeafRoundedFacts 8
    leaf3509Certificate.logOnePlusV leaf3509InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3509InputLogOnePlusV_eq }

private noncomputable def leaf3509Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi189InputQChi innerPair304Input
    leaf3509InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3509LowerChecked :
    lowerCheck 24 leaf3509Box leaf3509Inputs = true := by
  rfl'

private theorem leaf3509CoversExact : CoversExact 8
    leaf3509Box leaf3509Certificate leaf3509InnerLog leaf3509Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi189RoundedFacts
    innerPair304RoundedFacts leaf3509RoundedFacts (by rfl)

private theorem leaf3509FlatSound : Sound leaf3509Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3509CertificateValid
    leaf3509InnerLogValid leaf3509CoversExact leaf3509LowerChecked

private noncomputable def leaf3510Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3510Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430925312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2081066345/1073741824) }, upper := { exponent := 0, mantissa := (501/256) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867847167/274861850624) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3510InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf3510LocalValidity :
    LeafFacts leaf3510Box leaf3510Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3510Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430925312) }) = true
      norm_num [leaf3510Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3510CertificateValid :
    WideCertificateValid leaf3510Box leaf3510Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi190ValidityFacts
    leaf3510LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3510CoverageChecked :
    coverageCheck (innerAD leaf3510Box) leaf3510InnerLog = true := by
  rfl'

private theorem leaf3510InnerLogValid :
    leaf3510InnerLog.Valid 8 (innerAD leaf3510Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf3510CoverageChecked

private noncomputable def leaf3510InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3510InputLogOnePlusV_eq :
    leaf3510InputLogOnePlusV = outerEnclosure 24
      (leaf3510Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3510RoundedFacts : LeafRoundedFacts 8
    leaf3510Certificate.logOnePlusV leaf3510InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3510InputLogOnePlusV_eq }

private noncomputable def leaf3510Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi190InputQChi innerPair113Input
    leaf3510InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3510LowerChecked :
    lowerCheck 24 leaf3510Box leaf3510Inputs = true := by
  rfl'

private theorem leaf3510CoversExact : CoversExact 8
    leaf3510Box leaf3510Certificate leaf3510InnerLog leaf3510Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi190RoundedFacts
    innerPair113RoundedFacts leaf3510RoundedFacts (by rfl)

private theorem leaf3510FlatSound : Sound leaf3510Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3510CertificateValid
    leaf3510InnerLogValid leaf3510CoversExact leaf3510LowerChecked

private noncomputable def leaf3511Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3511Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430892544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2085194859/1073741824) }, upper := { exponent := 0, mantissa := (251/128) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867814399/274861785088) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3511InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf3511LocalValidity :
    LeafFacts leaf3511Box leaf3511Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3511Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430892544) }) = true
      norm_num [leaf3511Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3511CertificateValid :
    WideCertificateValid leaf3511Box leaf3511Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi190ValidityFacts
    leaf3511LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3511CoverageChecked :
    coverageCheck (innerAD leaf3511Box) leaf3511InnerLog = true := by
  rfl'

private theorem leaf3511InnerLogValid :
    leaf3511InnerLog.Valid 8 (innerAD leaf3511Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf3511CoverageChecked

private noncomputable def leaf3511InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3511InputLogOnePlusV_eq :
    leaf3511InputLogOnePlusV = outerEnclosure 24
      (leaf3511Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3511RoundedFacts : LeafRoundedFacts 8
    leaf3511Certificate.logOnePlusV leaf3511InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3511InputLogOnePlusV_eq }

private noncomputable def leaf3511Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi190InputQChi innerPair113Input
    leaf3511InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3511LowerChecked :
    lowerCheck 24 leaf3511Box leaf3511Inputs = true := by
  rfl'

private theorem leaf3511CoversExact : CoversExact 8
    leaf3511Box leaf3511Certificate leaf3511InnerLog leaf3511Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi190RoundedFacts
    innerPair113RoundedFacts leaf3511RoundedFacts (by rfl)

private theorem leaf3511FlatSound : Sound leaf3511Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3511CertificateValid
    leaf3511InnerLogValid leaf3511CoversExact leaf3511LowerChecked

private noncomputable def leaf3512Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3512Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486197248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2073202503/1073741824) }, upper := { exponent := 0, mantissa := (31945/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973581619/54972394496) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3512InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3512LocalValidity :
    LeafFacts leaf3512Box leaf3512Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3512Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486197248) }) = true
      norm_num [leaf3512Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3512CertificateValid :
    WideCertificateValid leaf3512Box leaf3512Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi189ValidityFacts
    leaf3512LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3512CoverageChecked :
    coverageCheck (innerAD leaf3512Box) leaf3512InnerLog = true := by
  rfl'

private theorem leaf3512InnerLogValid :
    leaf3512InnerLog.Valid 8 (innerAD leaf3512Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3512CoverageChecked

private noncomputable def leaf3512InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3512InputLogOnePlusV_eq :
    leaf3512InputLogOnePlusV = outerEnclosure 24
      (leaf3512Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3512RoundedFacts : LeafRoundedFacts 8
    leaf3512Certificate.logOnePlusV leaf3512InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3512InputLogOnePlusV_eq }

private noncomputable def leaf3512Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi189InputQChi innerPair304Input
    leaf3512InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3512LowerChecked :
    lowerCheck 24 leaf3512Box leaf3512Inputs = true := by
  rfl'

private theorem leaf3512CoversExact : CoversExact 8
    leaf3512Box leaf3512Certificate leaf3512InnerLog leaf3512Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi189RoundedFacts
    innerPair304RoundedFacts leaf3512RoundedFacts (by rfl)

private theorem leaf3512FlatSound : Sound leaf3512Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3512CertificateValid
    leaf3512InnerLogValid leaf3512CoversExact leaf3512LowerChecked

private noncomputable def leaf3513Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3513Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430953984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2077265485/1073741824) }, upper := { exponent := 0, mantissa := (4001/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867875839/274861907968) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3513InnerLog : WideLogData :=
  innerPair306Data

set_option maxRecDepth 1000000 in
private theorem leaf3513LocalValidity :
    LeafFacts leaf3513Box leaf3513Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3513Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430953984) }) = true
      norm_num [leaf3513Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3513CertificateValid :
    WideCertificateValid leaf3513Box leaf3513Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi189ValidityFacts
    leaf3513LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3513CoverageChecked :
    coverageCheck (innerAD leaf3513Box) leaf3513InnerLog = true := by
  rfl'

private theorem leaf3513InnerLogValid :
    leaf3513InnerLog.Valid 8 (innerAD leaf3513Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint85PositiveFacts.valid leaf3513CoverageChecked

private noncomputable def leaf3513InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3513InputLogOnePlusV_eq :
    leaf3513InputLogOnePlusV = outerEnclosure 24
      (leaf3513Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3513RoundedFacts : LeafRoundedFacts 8
    leaf3513Certificate.logOnePlusV leaf3513InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3513InputLogOnePlusV_eq }

private noncomputable def leaf3513Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi189InputQChi innerPair306Input
    leaf3513InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3513LowerChecked :
    lowerCheck 24 leaf3513Box leaf3513Inputs = true := by
  rfl'

private theorem leaf3513CoversExact : CoversExact 8
    leaf3513Box leaf3513Certificate leaf3513InnerLog leaf3513Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi189RoundedFacts
    innerPair306RoundedFacts leaf3513RoundedFacts (by rfl)

private theorem leaf3513FlatSound : Sound leaf3513Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3513CertificateValid
    leaf3513InnerLogValid leaf3513CoversExact leaf3513LowerChecked

private noncomputable def leaf3514Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3514Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810286592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2089323373/1073741824) }, upper := { exponent := 0, mantissa := (503/256) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622593877/91620573184) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3514InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf3514LocalValidity :
    LeafFacts leaf3514Box leaf3514Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3514Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810286592) }) = true
      norm_num [leaf3514Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3514CertificateValid :
    WideCertificateValid leaf3514Box leaf3514Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi190ValidityFacts
    leaf3514LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3514CoverageChecked :
    coverageCheck (innerAD leaf3514Box) leaf3514InnerLog = true := by
  rfl'

private theorem leaf3514InnerLogValid :
    leaf3514InnerLog.Valid 8 (innerAD leaf3514Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf3514CoverageChecked

private noncomputable def leaf3514InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3514InputLogOnePlusV_eq :
    leaf3514InputLogOnePlusV = outerEnclosure 24
      (leaf3514Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3514RoundedFacts : LeafRoundedFacts 8
    leaf3514Certificate.logOnePlusV leaf3514InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3514InputLogOnePlusV_eq }

private noncomputable def leaf3514Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi190InputQChi innerPair113Input
    leaf3514InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3514LowerChecked :
    lowerCheck 24 leaf3514Box leaf3514Inputs = true := by
  rfl'

private theorem leaf3514CoversExact : CoversExact 8
    leaf3514Box leaf3514Certificate leaf3514InnerLog leaf3514Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi190RoundedFacts
    innerPair113RoundedFacts leaf3514RoundedFacts (by rfl)

private theorem leaf3514FlatSound : Sound leaf3514Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3514CertificateValid
    leaf3514InnerLogValid leaf3514CoversExact leaf3514LowerChecked

private noncomputable def leaf3515Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3515Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430827008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2093451887/1073741824) }, upper := { exponent := 0, mantissa := (63/32) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867748863/274861654016) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3515InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf3515LocalValidity :
    LeafFacts leaf3515Box leaf3515Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3515Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430827008) }) = true
      norm_num [leaf3515Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3515CertificateValid :
    WideCertificateValid leaf3515Box leaf3515Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi190ValidityFacts
    leaf3515LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3515CoverageChecked :
    coverageCheck (innerAD leaf3515Box) leaf3515InnerLog = true := by
  rfl'

private theorem leaf3515InnerLogValid :
    leaf3515InnerLog.Valid 8 (innerAD leaf3515Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf3515CoverageChecked

private noncomputable def leaf3515InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3515InputLogOnePlusV_eq :
    leaf3515InputLogOnePlusV = outerEnclosure 24
      (leaf3515Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3515RoundedFacts : LeafRoundedFacts 8
    leaf3515Certificate.logOnePlusV leaf3515InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3515InputLogOnePlusV_eq }

private noncomputable def leaf3515Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi190InputQChi innerPair113Input
    leaf3515InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3515LowerChecked :
    lowerCheck 24 leaf3515Box leaf3515Inputs = true := by
  rfl'

private theorem leaf3515CoversExact : CoversExact 8
    leaf3515Box leaf3515Certificate leaf3515InnerLog leaf3515Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi190RoundedFacts
    innerPair113RoundedFacts leaf3515RoundedFacts (by rfl)

private theorem leaf3515FlatSound : Sound leaf3515Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3515CertificateValid
    leaf3515InnerLogValid leaf3515CoversExact leaf3515LowerChecked

private noncomputable def component71Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node0_sound : Sound component71Node0Box :=
  sound_of_literal_split component71Node0Box leaf3452Box leaf3453Box
    .k (241/64) (by rfl) (by rfl)
    leaf3452FlatSound leaf3453FlatSound

private noncomputable def component71Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node1_sound : Sound component71Node1Box :=
  sound_of_literal_split component71Node1Box leaf3454Box leaf3455Box
    .k (241/64) (by rfl) (by rfl)
    leaf3454FlatSound leaf3455FlatSound

private noncomputable def component71Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node2_sound : Sound component71Node2Box :=
  sound_of_literal_split component71Node2Box component71Node0Box component71Node1Box
    .chi (57/256) (by rfl) (by rfl)
    component71Node0_sound component71Node1_sound

private noncomputable def component71Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node3_sound : Sound component71Node3Box :=
  sound_of_literal_split component71Node3Box leaf3456Box leaf3457Box
    .k (243/64) (by rfl) (by rfl)
    leaf3456FlatSound leaf3457FlatSound

private noncomputable def component71Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node4_sound : Sound component71Node4Box :=
  sound_of_literal_split component71Node4Box leaf3458Box leaf3459Box
    .k (243/64) (by rfl) (by rfl)
    leaf3458FlatSound leaf3459FlatSound

private noncomputable def component71Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node5_sound : Sound component71Node5Box :=
  sound_of_literal_split component71Node5Box component71Node3Box component71Node4Box
    .chi (57/256) (by rfl) (by rfl)
    component71Node3_sound component71Node4_sound

private noncomputable def component71Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node6_sound : Sound component71Node6Box :=
  sound_of_literal_split component71Node6Box component71Node2Box component71Node5Box
    .k (121/32) (by rfl) (by rfl)
    component71Node2_sound component71Node5_sound

private noncomputable def component71Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node7_sound : Sound component71Node7Box :=
  sound_of_literal_split component71Node7Box leaf3460Box leaf3461Box
    .k (241/64) (by rfl) (by rfl)
    leaf3460FlatSound leaf3461FlatSound

private noncomputable def component71Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node8_sound : Sound component71Node8Box :=
  sound_of_literal_split component71Node8Box leaf3462Box leaf3463Box
    .k (241/64) (by rfl) (by rfl)
    leaf3462FlatSound leaf3463FlatSound

private noncomputable def component71Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node9_sound : Sound component71Node9Box :=
  sound_of_literal_split component71Node9Box component71Node7Box component71Node8Box
    .chi (59/256) (by rfl) (by rfl)
    component71Node7_sound component71Node8_sound

private noncomputable def component71Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node10_sound : Sound component71Node10Box :=
  sound_of_literal_split component71Node10Box leaf3464Box leaf3465Box
    .k (243/64) (by rfl) (by rfl)
    leaf3464FlatSound leaf3465FlatSound

private noncomputable def component71Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node11_sound : Sound component71Node11Box :=
  sound_of_literal_split component71Node11Box leaf3466Box leaf3467Box
    .k (243/64) (by rfl) (by rfl)
    leaf3466FlatSound leaf3467FlatSound

private noncomputable def component71Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node12_sound : Sound component71Node12Box :=
  sound_of_literal_split component71Node12Box component71Node10Box component71Node11Box
    .chi (59/256) (by rfl) (by rfl)
    component71Node10_sound component71Node11_sound

private noncomputable def component71Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node13_sound : Sound component71Node13Box :=
  sound_of_literal_split component71Node13Box component71Node9Box component71Node12Box
    .k (121/32) (by rfl) (by rfl)
    component71Node9_sound component71Node12_sound

private noncomputable def component71Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node14_sound : Sound component71Node14Box :=
  sound_of_literal_split component71Node14Box component71Node6Box component71Node13Box
    .chi (29/128) (by rfl) (by rfl)
    component71Node6_sound component71Node13_sound

private noncomputable def component71Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node15_sound : Sound component71Node15Box :=
  sound_of_literal_split component71Node15Box leaf3468Box leaf3469Box
    .k (245/64) (by rfl) (by rfl)
    leaf3468FlatSound leaf3469FlatSound

private noncomputable def component71Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node16_sound : Sound component71Node16Box :=
  sound_of_literal_split component71Node16Box leaf3470Box leaf3471Box
    .k (245/64) (by rfl) (by rfl)
    leaf3470FlatSound leaf3471FlatSound

private noncomputable def component71Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node17_sound : Sound component71Node17Box :=
  sound_of_literal_split component71Node17Box component71Node15Box component71Node16Box
    .chi (57/256) (by rfl) (by rfl)
    component71Node15_sound component71Node16_sound

private noncomputable def component71Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node18_sound : Sound component71Node18Box :=
  sound_of_literal_split component71Node18Box leaf3472Box leaf3473Box
    .k (247/64) (by rfl) (by rfl)
    leaf3472FlatSound leaf3473FlatSound

private noncomputable def component71Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node19_sound : Sound component71Node19Box :=
  sound_of_literal_split component71Node19Box leaf3474Box leaf3475Box
    .k (247/64) (by rfl) (by rfl)
    leaf3474FlatSound leaf3475FlatSound

private noncomputable def component71Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node20_sound : Sound component71Node20Box :=
  sound_of_literal_split component71Node20Box component71Node18Box component71Node19Box
    .chi (57/256) (by rfl) (by rfl)
    component71Node18_sound component71Node19_sound

private noncomputable def component71Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node21_sound : Sound component71Node21Box :=
  sound_of_literal_split component71Node21Box component71Node17Box component71Node20Box
    .k (123/32) (by rfl) (by rfl)
    component71Node17_sound component71Node20_sound

private noncomputable def component71Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node22_sound : Sound component71Node22Box :=
  sound_of_literal_split component71Node22Box leaf3476Box leaf3477Box
    .k (245/64) (by rfl) (by rfl)
    leaf3476FlatSound leaf3477FlatSound

private noncomputable def component71Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node23_sound : Sound component71Node23Box :=
  sound_of_literal_split component71Node23Box leaf3478Box leaf3479Box
    .k (245/64) (by rfl) (by rfl)
    leaf3478FlatSound leaf3479FlatSound

private noncomputable def component71Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node24_sound : Sound component71Node24Box :=
  sound_of_literal_split component71Node24Box component71Node22Box component71Node23Box
    .chi (59/256) (by rfl) (by rfl)
    component71Node22_sound component71Node23_sound

private noncomputable def component71Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node25_sound : Sound component71Node25Box :=
  sound_of_literal_split component71Node25Box leaf3480Box leaf3481Box
    .k (247/64) (by rfl) (by rfl)
    leaf3480FlatSound leaf3481FlatSound

private noncomputable def component71Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node26_sound : Sound component71Node26Box :=
  sound_of_literal_split component71Node26Box leaf3482Box leaf3483Box
    .k (247/64) (by rfl) (by rfl)
    leaf3482FlatSound leaf3483FlatSound

private noncomputable def component71Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node27_sound : Sound component71Node27Box :=
  sound_of_literal_split component71Node27Box component71Node25Box component71Node26Box
    .chi (59/256) (by rfl) (by rfl)
    component71Node25_sound component71Node26_sound

private noncomputable def component71Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node28_sound : Sound component71Node28Box :=
  sound_of_literal_split component71Node28Box component71Node24Box component71Node27Box
    .k (123/32) (by rfl) (by rfl)
    component71Node24_sound component71Node27_sound

private noncomputable def component71Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node29_sound : Sound component71Node29Box :=
  sound_of_literal_split component71Node29Box component71Node21Box component71Node28Box
    .chi (29/128) (by rfl) (by rfl)
    component71Node21_sound component71Node28_sound

private noncomputable def component71Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component71Node30_sound : Sound component71Node30Box :=
  sound_of_literal_split component71Node30Box component71Node14Box component71Node29Box
    .k (61/16) (by rfl) (by rfl)
    component71Node14_sound component71Node29_sound

private noncomputable def component71Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node31_sound : Sound component71Node31Box :=
  sound_of_literal_split component71Node31Box leaf3484Box leaf3485Box
    .k (241/64) (by rfl) (by rfl)
    leaf3484FlatSound leaf3485FlatSound

private noncomputable def component71Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node32_sound : Sound component71Node32Box :=
  sound_of_literal_split component71Node32Box leaf3486Box leaf3487Box
    .k (241/64) (by rfl) (by rfl)
    leaf3486FlatSound leaf3487FlatSound

private noncomputable def component71Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node33_sound : Sound component71Node33Box :=
  sound_of_literal_split component71Node33Box component71Node31Box component71Node32Box
    .chi (61/256) (by rfl) (by rfl)
    component71Node31_sound component71Node32_sound

private noncomputable def component71Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node34_sound : Sound component71Node34Box :=
  sound_of_literal_split component71Node34Box leaf3488Box leaf3489Box
    .k (243/64) (by rfl) (by rfl)
    leaf3488FlatSound leaf3489FlatSound

private noncomputable def component71Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node35_sound : Sound component71Node35Box :=
  sound_of_literal_split component71Node35Box leaf3490Box leaf3491Box
    .k (243/64) (by rfl) (by rfl)
    leaf3490FlatSound leaf3491FlatSound

private noncomputable def component71Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node36_sound : Sound component71Node36Box :=
  sound_of_literal_split component71Node36Box component71Node34Box component71Node35Box
    .chi (61/256) (by rfl) (by rfl)
    component71Node34_sound component71Node35_sound

private noncomputable def component71Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node37_sound : Sound component71Node37Box :=
  sound_of_literal_split component71Node37Box component71Node33Box component71Node36Box
    .k (121/32) (by rfl) (by rfl)
    component71Node33_sound component71Node36_sound

private noncomputable def component71Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node38_sound : Sound component71Node38Box :=
  sound_of_literal_split component71Node38Box leaf3492Box leaf3493Box
    .k (241/64) (by rfl) (by rfl)
    leaf3492FlatSound leaf3493FlatSound

private noncomputable def component71Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node39_sound : Sound component71Node39Box :=
  sound_of_literal_split component71Node39Box leaf3494Box leaf3495Box
    .k (241/64) (by rfl) (by rfl)
    leaf3494FlatSound leaf3495FlatSound

private noncomputable def component71Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node40_sound : Sound component71Node40Box :=
  sound_of_literal_split component71Node40Box component71Node38Box component71Node39Box
    .chi (63/256) (by rfl) (by rfl)
    component71Node38_sound component71Node39_sound

private noncomputable def component71Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node41_sound : Sound component71Node41Box :=
  sound_of_literal_split component71Node41Box leaf3496Box leaf3497Box
    .k (243/64) (by rfl) (by rfl)
    leaf3496FlatSound leaf3497FlatSound

private noncomputable def component71Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node42_sound : Sound component71Node42Box :=
  sound_of_literal_split component71Node42Box leaf3498Box leaf3499Box
    .k (243/64) (by rfl) (by rfl)
    leaf3498FlatSound leaf3499FlatSound

private noncomputable def component71Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node43_sound : Sound component71Node43Box :=
  sound_of_literal_split component71Node43Box component71Node41Box component71Node42Box
    .chi (63/256) (by rfl) (by rfl)
    component71Node41_sound component71Node42_sound

private noncomputable def component71Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node44_sound : Sound component71Node44Box :=
  sound_of_literal_split component71Node44Box component71Node40Box component71Node43Box
    .k (121/32) (by rfl) (by rfl)
    component71Node40_sound component71Node43_sound

private noncomputable def component71Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node45_sound : Sound component71Node45Box :=
  sound_of_literal_split component71Node45Box component71Node37Box component71Node44Box
    .chi (31/128) (by rfl) (by rfl)
    component71Node37_sound component71Node44_sound

private noncomputable def component71Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node46_sound : Sound component71Node46Box :=
  sound_of_literal_split component71Node46Box leaf3500Box leaf3501Box
    .k (245/64) (by rfl) (by rfl)
    leaf3500FlatSound leaf3501FlatSound

private noncomputable def component71Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node47_sound : Sound component71Node47Box :=
  sound_of_literal_split component71Node47Box leaf3502Box leaf3503Box
    .k (245/64) (by rfl) (by rfl)
    leaf3502FlatSound leaf3503FlatSound

private noncomputable def component71Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node48_sound : Sound component71Node48Box :=
  sound_of_literal_split component71Node48Box component71Node46Box component71Node47Box
    .chi (61/256) (by rfl) (by rfl)
    component71Node46_sound component71Node47_sound

private noncomputable def component71Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node49_sound : Sound component71Node49Box :=
  sound_of_literal_split component71Node49Box leaf3504Box leaf3505Box
    .k (247/64) (by rfl) (by rfl)
    leaf3504FlatSound leaf3505FlatSound

private noncomputable def component71Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node50_sound : Sound component71Node50Box :=
  sound_of_literal_split component71Node50Box leaf3506Box leaf3507Box
    .k (247/64) (by rfl) (by rfl)
    leaf3506FlatSound leaf3507FlatSound

private noncomputable def component71Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node51_sound : Sound component71Node51Box :=
  sound_of_literal_split component71Node51Box component71Node49Box component71Node50Box
    .chi (61/256) (by rfl) (by rfl)
    component71Node49_sound component71Node50_sound

private noncomputable def component71Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component71Node52_sound : Sound component71Node52Box :=
  sound_of_literal_split component71Node52Box component71Node48Box component71Node51Box
    .k (123/32) (by rfl) (by rfl)
    component71Node48_sound component71Node51_sound

private noncomputable def component71Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node53_sound : Sound component71Node53Box :=
  sound_of_literal_split component71Node53Box leaf3508Box leaf3509Box
    .k (245/64) (by rfl) (by rfl)
    leaf3508FlatSound leaf3509FlatSound

private noncomputable def component71Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node54_sound : Sound component71Node54Box :=
  sound_of_literal_split component71Node54Box leaf3510Box leaf3511Box
    .k (245/64) (by rfl) (by rfl)
    leaf3510FlatSound leaf3511FlatSound

private noncomputable def component71Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node55_sound : Sound component71Node55Box :=
  sound_of_literal_split component71Node55Box component71Node53Box component71Node54Box
    .chi (63/256) (by rfl) (by rfl)
    component71Node53_sound component71Node54_sound

private noncomputable def component71Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component71Node56_sound : Sound component71Node56Box :=
  sound_of_literal_split component71Node56Box leaf3512Box leaf3513Box
    .k (247/64) (by rfl) (by rfl)
    leaf3512FlatSound leaf3513FlatSound

private noncomputable def component71Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node57_sound : Sound component71Node57Box :=
  sound_of_literal_split component71Node57Box leaf3514Box leaf3515Box
    .k (247/64) (by rfl) (by rfl)
    leaf3514FlatSound leaf3515FlatSound

private noncomputable def component71Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node58_sound : Sound component71Node58Box :=
  sound_of_literal_split component71Node58Box component71Node56Box component71Node57Box
    .chi (63/256) (by rfl) (by rfl)
    component71Node56_sound component71Node57_sound

private noncomputable def component71Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node59_sound : Sound component71Node59Box :=
  sound_of_literal_split component71Node59Box component71Node55Box component71Node58Box
    .k (123/32) (by rfl) (by rfl)
    component71Node55_sound component71Node58_sound

private noncomputable def component71Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node60_sound : Sound component71Node60Box :=
  sound_of_literal_split component71Node60Box component71Node52Box component71Node59Box
    .chi (31/128) (by rfl) (by rfl)
    component71Node52_sound component71Node59_sound

private noncomputable def component71Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component71Node61_sound : Sound component71Node61Box :=
  sound_of_literal_split component71Node61Box component71Node45Box component71Node60Box
    .k (61/16) (by rfl) (by rfl)
    component71Node45_sound component71Node60_sound

noncomputable def component71Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component71_sound : Sound component71Box :=
  sound_of_literal_split component71Box component71Node30Box component71Node61Box
    .chi (15/64) (by rfl) (by rfl)
    component71Node30_sound component71Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
