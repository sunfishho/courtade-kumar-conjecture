import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf4749Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4749Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431465472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2013175231/1073741824) }, upper := { exponent := 0, mantissa := (31009/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868387327/274862930944) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4749InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4749LocalValidity :
    LeafFacts leaf4749Box leaf4749Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4749Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431465472) }) = true
      norm_num [leaf4749Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4749CertificateValid :
    WideCertificateValid leaf4749Box leaf4749Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi277ValidityFacts
    leaf4749LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4749CoverageChecked :
    coverageCheck (innerAD leaf4749Box) leaf4749InnerLog = true := by
  rfl'

private theorem leaf4749InnerLogValid :
    leaf4749InnerLog.Valid 8 (innerAD leaf4749Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4749CoverageChecked

private noncomputable def leaf4749InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4749InputLogOnePlusV_eq :
    leaf4749InputLogOnePlusV = outerEnclosure 24
      (leaf4749Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4749RoundedFacts : LeafRoundedFacts 8
    leaf4749Certificate.logOnePlusV leaf4749InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4749InputLogOnePlusV_eq }

private noncomputable def leaf4749Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi277InputQChi innerPair92Input
    leaf4749InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4749LowerChecked :
    lowerCheck 24 leaf4749Box leaf4749Inputs = true := by
  rfl'

private theorem leaf4749CoversExact : CoversExact 8
    leaf4749Box leaf4749Certificate leaf4749InnerLog leaf4749Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi277RoundedFacts
    innerPair92RoundedFacts leaf4749RoundedFacts (by rfl)

private theorem leaf4749FlatSound : Sound leaf4749Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4749CertificateValid
    leaf4749InnerLogValid leaf4749CoversExact leaf4749LowerChecked

private noncomputable def leaf4750Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4750Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431432192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2017369277/1073741824) }, upper := { exponent := 0, mantissa := (15537/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868354047/274862864384) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4750InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4750LocalValidity :
    LeafFacts leaf4750Box leaf4750Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4750Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431432192) }) = true
      norm_num [leaf4750Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4750CertificateValid :
    WideCertificateValid leaf4750Box leaf4750Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi277ValidityFacts
    leaf4750LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4750CoverageChecked :
    coverageCheck (innerAD leaf4750Box) leaf4750InnerLog = true := by
  rfl'

private theorem leaf4750InnerLogValid :
    leaf4750InnerLog.Valid 8 (innerAD leaf4750Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4750CoverageChecked

private noncomputable def leaf4750InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4750InputLogOnePlusV_eq :
    leaf4750InputLogOnePlusV = outerEnclosure 24
      (leaf4750Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4750RoundedFacts : LeafRoundedFacts 8
    leaf4750Certificate.logOnePlusV leaf4750InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4750InputLogOnePlusV_eq }

private noncomputable def leaf4750Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4750InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4750LowerChecked :
    lowerCheck 24 leaf4750Box leaf4750Inputs = true := by
  rfl'

private theorem leaf4750CoversExact : CoversExact 8
    leaf4750Box leaf4750Certificate leaf4750InnerLog leaf4750Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4750RoundedFacts (by rfl)

private theorem leaf4750FlatSound : Sound leaf4750Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4750CertificateValid
    leaf4750InnerLogValid leaf4750CoversExact leaf4750LowerChecked

private noncomputable def leaf4751Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4751Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431350272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2027854397/1073741824) }, upper := { exponent := 0, mantissa := (15617/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868272127/274862700544) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4751InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4751LocalValidity :
    LeafFacts leaf4751Box leaf4751Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4751Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431350272) }) = true
      norm_num [leaf4751Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4751CertificateValid :
    WideCertificateValid leaf4751Box leaf4751Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi278ValidityFacts
    leaf4751LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4751CoverageChecked :
    coverageCheck (innerAD leaf4751Box) leaf4751InnerLog = true := by
  rfl'

private theorem leaf4751InnerLogValid :
    leaf4751InnerLog.Valid 8 (innerAD leaf4751Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4751CoverageChecked

private noncomputable def leaf4751InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4751InputLogOnePlusV_eq :
    leaf4751InputLogOnePlusV = outerEnclosure 24
      (leaf4751Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4751RoundedFacts : LeafRoundedFacts 8
    leaf4751Certificate.logOnePlusV leaf4751InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4751InputLogOnePlusV_eq }

private noncomputable def leaf4751Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4751InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4751LowerChecked :
    lowerCheck 24 leaf4751Box leaf4751Inputs = true := by
  rfl'

private theorem leaf4751CoversExact : CoversExact 8
    leaf4751Box leaf4751Certificate leaf4751InnerLog leaf4751Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4751RoundedFacts (by rfl)

private theorem leaf4751FlatSound : Sound leaf4751Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4751CertificateValid
    leaf4751InnerLogValid leaf4751CoversExact leaf4751LowerChecked

private noncomputable def leaf4752Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4752Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486263296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2032113975/1073741824) }, upper := { exponent := 0, mantissa := (7825/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973647667/54972526592) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4752InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4752LocalValidity :
    LeafFacts leaf4752Box leaf4752Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4752Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486263296) }) = true
      norm_num [leaf4752Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4752CertificateValid :
    WideCertificateValid leaf4752Box leaf4752Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi278ValidityFacts
    leaf4752LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4752CoverageChecked :
    coverageCheck (innerAD leaf4752Box) leaf4752InnerLog = true := by
  rfl'

private theorem leaf4752InnerLogValid :
    leaf4752InnerLog.Valid 8 (innerAD leaf4752Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4752CoverageChecked

private noncomputable def leaf4752InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4752InputLogOnePlusV_eq :
    leaf4752InputLogOnePlusV = outerEnclosure 24
      (leaf4752Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4752RoundedFacts : LeafRoundedFacts 8
    leaf4752Certificate.logOnePlusV leaf4752InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4752InputLogOnePlusV_eq }

private noncomputable def leaf4752Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4752InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4752LowerChecked :
    lowerCheck 24 leaf4752Box leaf4752Inputs = true := by
  rfl'

private theorem leaf4752CoversExact : CoversExact 8
    leaf4752Box leaf4752Certificate leaf4752InnerLog leaf4752Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4752RoundedFacts (by rfl)

private theorem leaf4752FlatSound : Sound leaf4752Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4752CertificateValid
    leaf4752InnerLogValid leaf4752CoversExact leaf4752LowerChecked

private noncomputable def leaf4753Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4753Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2694841605/2694733312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2021563323/1073741824) }, upper := { exponent := 0, mantissa := (31139/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5389574917/5389466624) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4753InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4753LocalValidity :
    LeafFacts leaf4753Box leaf4753Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4753Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2694841605/2694733312) }) = true
      norm_num [leaf4753Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4753CertificateValid :
    WideCertificateValid leaf4753Box leaf4753Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi277ValidityFacts
    leaf4753LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4753CoverageChecked :
    coverageCheck (innerAD leaf4753Box) leaf4753InnerLog = true := by
  rfl'

private theorem leaf4753InnerLogValid :
    leaf4753InnerLog.Valid 8 (innerAD leaf4753Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4753CoverageChecked

private noncomputable def leaf4753InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4753InputLogOnePlusV_eq :
    leaf4753InputLogOnePlusV = outerEnclosure 24
      (leaf4753Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4753RoundedFacts : LeafRoundedFacts 8
    leaf4753Certificate.logOnePlusV leaf4753InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4753InputLogOnePlusV_eq }

private noncomputable def leaf4753Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4753InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4753LowerChecked :
    lowerCheck 24 leaf4753Box leaf4753Inputs = true := by
  rfl'

private theorem leaf4753CoversExact : CoversExact 8
    leaf4753Box leaf4753Certificate leaf4753InnerLog leaf4753Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4753RoundedFacts (by rfl)

private theorem leaf4753FlatSound : Sound leaf4753Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4753CertificateValid
    leaf4753InnerLogValid leaf4753CoversExact leaf4753LowerChecked

private noncomputable def leaf4754Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4754Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431365632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2025757369/1073741824) }, upper := { exponent := 0, mantissa := (7801/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868287487/274862731264) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4754InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4754LocalValidity :
    LeafFacts leaf4754Box leaf4754Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4754Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431365632) }) = true
      norm_num [leaf4754Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4754CertificateValid :
    WideCertificateValid leaf4754Box leaf4754Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi277ValidityFacts
    leaf4754LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4754CoverageChecked :
    coverageCheck (innerAD leaf4754Box) leaf4754InnerLog = true := by
  rfl'

private theorem leaf4754InnerLogValid :
    leaf4754InnerLog.Valid 8 (innerAD leaf4754Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4754CoverageChecked

private noncomputable def leaf4754InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4754InputLogOnePlusV_eq :
    leaf4754InputLogOnePlusV = outerEnclosure 24
      (leaf4754Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4754RoundedFacts : LeafRoundedFacts 8
    leaf4754Certificate.logOnePlusV leaf4754InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4754InputLogOnePlusV_eq }

private noncomputable def leaf4754Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4754InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4754LowerChecked :
    lowerCheck 24 leaf4754Box leaf4754Inputs = true := by
  rfl'

private theorem leaf4754CoversExact : CoversExact 8
    leaf4754Box leaf4754Certificate leaf4754InnerLog leaf4754Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4754RoundedFacts (by rfl)

private theorem leaf4754FlatSound : Sound leaf4754Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4754CertificateValid
    leaf4754InnerLogValid leaf4754CoversExact leaf4754LowerChecked

private noncomputable def leaf4755Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4755Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431282688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2036373553/1073741824) }, upper := { exponent := 0, mantissa := (15683/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868204543/274862565376) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4755InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4755LocalValidity :
    LeafFacts leaf4755Box leaf4755Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4755Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431282688) }) = true
      norm_num [leaf4755Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4755CertificateValid :
    WideCertificateValid leaf4755Box leaf4755Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi278ValidityFacts
    leaf4755LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4755CoverageChecked :
    coverageCheck (innerAD leaf4755Box) leaf4755InnerLog = true := by
  rfl'

private theorem leaf4755InnerLogValid :
    leaf4755InnerLog.Valid 8 (innerAD leaf4755Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4755CoverageChecked

private noncomputable def leaf4755InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4755InputLogOnePlusV_eq :
    leaf4755InputLogOnePlusV = outerEnclosure 24
      (leaf4755Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4755RoundedFacts : LeafRoundedFacts 8
    leaf4755Certificate.logOnePlusV leaf4755InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4755InputLogOnePlusV_eq }

private noncomputable def leaf4755Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4755InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4755LowerChecked :
    lowerCheck 24 leaf4755Box leaf4755Inputs = true := by
  rfl'

private theorem leaf4755CoversExact : CoversExact 8
    leaf4755Box leaf4755Certificate leaf4755InnerLog leaf4755Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4755RoundedFacts (by rfl)

private theorem leaf4755FlatSound : Sound leaf4755Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4755CertificateValid
    leaf4755InnerLogValid leaf4755CoversExact leaf4755LowerChecked

private noncomputable def leaf4756Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4756Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431248896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2040633131/1073741824) }, upper := { exponent := 0, mantissa := (3929/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868170751/274862497792) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4756InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4756LocalValidity :
    LeafFacts leaf4756Box leaf4756Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4756Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431248896) }) = true
      norm_num [leaf4756Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4756CertificateValid :
    WideCertificateValid leaf4756Box leaf4756Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi278ValidityFacts
    leaf4756LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4756CoverageChecked :
    coverageCheck (innerAD leaf4756Box) leaf4756InnerLog = true := by
  rfl'

private theorem leaf4756InnerLogValid :
    leaf4756InnerLog.Valid 8 (innerAD leaf4756Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4756CoverageChecked

private noncomputable def leaf4756InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4756InputLogOnePlusV_eq :
    leaf4756InputLogOnePlusV = outerEnclosure 24
      (leaf4756Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4756RoundedFacts : LeafRoundedFacts 8
    leaf4756Certificate.logOnePlusV leaf4756InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4756InputLogOnePlusV_eq }

private noncomputable def leaf4756Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4756InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4756LowerChecked :
    lowerCheck 24 leaf4756Box leaf4756Inputs = true := by
  rfl'

private theorem leaf4756CoversExact : CoversExact 8
    leaf4756Box leaf4756Certificate leaf4756InnerLog leaf4756Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4756RoundedFacts (by rfl)

private theorem leaf4756FlatSound : Sound leaf4756Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4756CertificateValid
    leaf4756InnerLogValid leaf4756CoversExact leaf4756LowerChecked

private noncomputable def leaf4757Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4757Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431235072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2042533563/1073741824) }, upper := { exponent := 0, mantissa := (31459/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868156927/274862470144) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4757InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4757LocalValidity :
    LeafFacts leaf4757Box leaf4757Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4757Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431235072) }) = true
      norm_num [leaf4757Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4757CertificateValid :
    WideCertificateValid leaf4757Box leaf4757Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi275ValidityFacts
    leaf4757LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4757CoverageChecked :
    coverageCheck (innerAD leaf4757Box) leaf4757InnerLog = true := by
  rfl'

private theorem leaf4757InnerLogValid :
    leaf4757InnerLog.Valid 8 (innerAD leaf4757Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4757CoverageChecked

private noncomputable def leaf4757InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4757InputLogOnePlusV_eq :
    leaf4757InputLogOnePlusV = outerEnclosure 24
      (leaf4757Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4757RoundedFacts : LeafRoundedFacts 8
    leaf4757Certificate.logOnePlusV leaf4757InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4757InputLogOnePlusV_eq }

private noncomputable def leaf4757Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4757InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4757LowerChecked :
    lowerCheck 24 leaf4757Box leaf4757Inputs = true := by
  rfl'

private theorem leaf4757CoversExact : CoversExact 8
    leaf4757Box leaf4757Certificate leaf4757InnerLog leaf4757Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4757RoundedFacts (by rfl)

private theorem leaf4757FlatSound : Sound leaf4757Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4757CertificateValid
    leaf4757InnerLogValid leaf4757CoversExact leaf4757LowerChecked

private noncomputable def leaf4758Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4758Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810400256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2046858673/1073741824) }, upper := { exponent := 0, mantissa := (15763/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622707541/91620800512) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4758InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4758LocalValidity :
    LeafFacts leaf4758Box leaf4758Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4758Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810400256) }) = true
      norm_num [leaf4758Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4758CertificateValid :
    WideCertificateValid leaf4758Box leaf4758Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi275ValidityFacts
    leaf4758LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4758CoverageChecked :
    coverageCheck (innerAD leaf4758Box) leaf4758InnerLog = true := by
  rfl'

private theorem leaf4758InnerLogValid :
    leaf4758InnerLog.Valid 8 (innerAD leaf4758Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4758CoverageChecked

private noncomputable def leaf4758InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4758InputLogOnePlusV_eq :
    leaf4758InputLogOnePlusV = outerEnclosure 24
      (leaf4758Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4758RoundedFacts : LeafRoundedFacts 8
    leaf4758Certificate.logOnePlusV leaf4758InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4758InputLogOnePlusV_eq }

private noncomputable def leaf4758Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4758InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4758LowerChecked :
    lowerCheck 24 leaf4758Box leaf4758Inputs = true := by
  rfl'

private theorem leaf4758CoversExact : CoversExact 8
    leaf4758Box leaf4758Certificate leaf4758InnerLog leaf4758Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4758RoundedFacts (by rfl)

private theorem leaf4758FlatSound : Sound leaf4758Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4758CertificateValid
    leaf4758InnerLogValid leaf4758CoversExact leaf4758LowerChecked

private noncomputable def leaf4759Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4759Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431119872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2057212729/1073741824) }, upper := { exponent := 0, mantissa := (7921/4096) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868041727/274862239744) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4759InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4759LocalValidity :
    LeafFacts leaf4759Box leaf4759Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4759Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431119872) }) = true
      norm_num [leaf4759Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4759CertificateValid :
    WideCertificateValid leaf4759Box leaf4759Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi276ValidityFacts
    leaf4759LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4759CoverageChecked :
    coverageCheck (innerAD leaf4759Box) leaf4759InnerLog = true := by
  rfl'

private theorem leaf4759InnerLogValid :
    leaf4759InnerLog.Valid 8 (innerAD leaf4759Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4759CoverageChecked

private noncomputable def leaf4759InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4759InputLogOnePlusV_eq :
    leaf4759InputLogOnePlusV = outerEnclosure 24
      (leaf4759Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4759RoundedFacts : LeafRoundedFacts 8
    leaf4759Certificate.logOnePlusV leaf4759InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4759InputLogOnePlusV_eq }

private noncomputable def leaf4759Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi276InputQChi innerPair100Input
    leaf4759InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4759LowerChecked :
    lowerCheck 24 leaf4759Box leaf4759Inputs = true := by
  rfl'

private theorem leaf4759CoversExact : CoversExact 8
    leaf4759Box leaf4759Certificate leaf4759InnerLog leaf4759Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi276RoundedFacts
    innerPair100RoundedFacts leaf4759RoundedFacts (by rfl)

private theorem leaf4759FlatSound : Sound leaf4759Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4759CertificateValid
    leaf4759InnerLogValid leaf4759CoversExact leaf4759LowerChecked

private noncomputable def leaf4760Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4760Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431085056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2061603371/1073741824) }, upper := { exponent := 0, mantissa := (3969/2048) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868006911/274862170112) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4760InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4760LocalValidity :
    LeafFacts leaf4760Box leaf4760Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4760Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431085056) }) = true
      norm_num [leaf4760Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4760CertificateValid :
    WideCertificateValid leaf4760Box leaf4760Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi276ValidityFacts
    leaf4760LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4760CoverageChecked :
    coverageCheck (innerAD leaf4760Box) leaf4760InnerLog = true := by
  rfl'

private theorem leaf4760InnerLogValid :
    leaf4760InnerLog.Valid 8 (innerAD leaf4760Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4760CoverageChecked

private noncomputable def leaf4760InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4760InputLogOnePlusV_eq :
    leaf4760InputLogOnePlusV = outerEnclosure 24
      (leaf4760Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4760RoundedFacts : LeafRoundedFacts 8
    leaf4760Certificate.logOnePlusV leaf4760InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4760InputLogOnePlusV_eq }

private noncomputable def leaf4760Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi276InputQChi innerPair101Input
    leaf4760InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4760LowerChecked :
    lowerCheck 24 leaf4760Box leaf4760Inputs = true := by
  rfl'

private theorem leaf4760CoversExact : CoversExact 8
    leaf4760Box leaf4760Certificate leaf4760InnerLog leaf4760Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi276RoundedFacts
    innerPair101RoundedFacts leaf4760RoundedFacts (by rfl)

private theorem leaf4760FlatSound : Sound leaf4760Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4760CertificateValid
    leaf4760InnerLogValid leaf4760CoversExact leaf4760LowerChecked

private noncomputable def leaf4761Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4761Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431166464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2051183783/1073741824) }, upper := { exponent := 0, mantissa := (31593/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868088319/274862332928) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4761InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4761LocalValidity :
    LeafFacts leaf4761Box leaf4761Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4761Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431166464) }) = true
      norm_num [leaf4761Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4761CertificateValid :
    WideCertificateValid leaf4761Box leaf4761Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi275ValidityFacts
    leaf4761LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4761CoverageChecked :
    coverageCheck (innerAD leaf4761Box) leaf4761InnerLog = true := by
  rfl'

private theorem leaf4761InnerLogValid :
    leaf4761InnerLog.Valid 8 (innerAD leaf4761Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4761CoverageChecked

private noncomputable def leaf4761InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4761InputLogOnePlusV_eq :
    leaf4761InputLogOnePlusV = outerEnclosure 24
      (leaf4761Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4761RoundedFacts : LeafRoundedFacts 8
    leaf4761Certificate.logOnePlusV leaf4761InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4761InputLogOnePlusV_eq }

private noncomputable def leaf4761Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4761InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4761LowerChecked :
    lowerCheck 24 leaf4761Box leaf4761Inputs = true := by
  rfl'

private theorem leaf4761CoversExact : CoversExact 8
    leaf4761Box leaf4761Certificate leaf4761InnerLog leaf4761Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4761RoundedFacts (by rfl)

private theorem leaf4761FlatSound : Sound leaf4761Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4761CertificateValid
    leaf4761InnerLogValid leaf4761CoversExact leaf4761LowerChecked

private noncomputable def leaf4762Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4762Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486226432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2055508893/1073741824) }, upper := { exponent := 0, mantissa := (7915/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973610803/54972452864) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4762InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4762LocalValidity :
    LeafFacts leaf4762Box leaf4762Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4762Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486226432) }) = true
      norm_num [leaf4762Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4762CertificateValid :
    WideCertificateValid leaf4762Box leaf4762Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi275ValidityFacts
    leaf4762LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4762CoverageChecked :
    coverageCheck (innerAD leaf4762Box) leaf4762InnerLog = true := by
  rfl'

private theorem leaf4762InnerLogValid :
    leaf4762InnerLog.Valid 8 (innerAD leaf4762Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4762CoverageChecked

private noncomputable def leaf4762InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4762InputLogOnePlusV_eq :
    leaf4762InputLogOnePlusV = outerEnclosure 24
      (leaf4762Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4762RoundedFacts : LeafRoundedFacts 8
    leaf4762Certificate.logOnePlusV leaf4762InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4762InputLogOnePlusV_eq }

private noncomputable def leaf4762Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4762InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4762LowerChecked :
    lowerCheck 24 leaf4762Box leaf4762Inputs = true := by
  rfl'

private theorem leaf4762CoversExact : CoversExact 8
    leaf4762Box leaf4762Certificate leaf4762InnerLog leaf4762Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4762RoundedFacts (by rfl)

private theorem leaf4762FlatSound : Sound leaf4762Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4762CertificateValid
    leaf4762InnerLogValid leaf4762CoversExact leaf4762LowerChecked

private noncomputable def leaf4763Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4763Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162070016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2065994013/1073741824) }, upper := { exponent := 0, mantissa := (7955/4096) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324531473/18324140032) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4763InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4763LocalValidity :
    LeafFacts leaf4763Box leaf4763Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4763Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162070016) }) = true
      norm_num [leaf4763Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4763CertificateValid :
    WideCertificateValid leaf4763Box leaf4763Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi276ValidityFacts
    leaf4763LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4763CoverageChecked :
    coverageCheck (innerAD leaf4763Box) leaf4763InnerLog = true := by
  rfl'

private theorem leaf4763InnerLogValid :
    leaf4763InnerLog.Valid 8 (innerAD leaf4763Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4763CoverageChecked

private noncomputable def leaf4763InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4763InputLogOnePlusV_eq :
    leaf4763InputLogOnePlusV = outerEnclosure 24
      (leaf4763Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4763RoundedFacts : LeafRoundedFacts 8
    leaf4763Certificate.logOnePlusV leaf4763InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4763InputLogOnePlusV_eq }

private noncomputable def leaf4763Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi276InputQChi innerPair101Input
    leaf4763InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4763LowerChecked :
    lowerCheck 24 leaf4763Box leaf4763Inputs = true := by
  rfl'

private theorem leaf4763CoversExact : CoversExact 8
    leaf4763Box leaf4763Certificate leaf4763InnerLog leaf4763Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi276RoundedFacts
    innerPair101RoundedFacts leaf4763RoundedFacts (by rfl)

private theorem leaf4763FlatSound : Sound leaf4763Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4763CertificateValid
    leaf4763InnerLogValid leaf4763CoversExact leaf4763LowerChecked

private noncomputable def leaf4764Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4764Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431015424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2070384655/1073741824) }, upper := { exponent := 0, mantissa := (1993/1024) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867937279/274862030848) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4764InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4764LocalValidity :
    LeafFacts leaf4764Box leaf4764Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4764Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431015424) }) = true
      norm_num [leaf4764Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4764CertificateValid :
    WideCertificateValid leaf4764Box leaf4764Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi276ValidityFacts
    leaf4764LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4764CoverageChecked :
    coverageCheck (innerAD leaf4764Box) leaf4764InnerLog = true := by
  rfl'

private theorem leaf4764InnerLogValid :
    leaf4764InnerLog.Valid 8 (innerAD leaf4764Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4764CoverageChecked

private noncomputable def leaf4764InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4764InputLogOnePlusV_eq :
    leaf4764InputLogOnePlusV = outerEnclosure 24
      (leaf4764Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4764RoundedFacts : LeafRoundedFacts 8
    leaf4764Certificate.logOnePlusV leaf4764InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4764InputLogOnePlusV_eq }

private noncomputable def leaf4764Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi276InputQChi innerPair101Input
    leaf4764InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4764LowerChecked :
    lowerCheck 24 leaf4764Box leaf4764Inputs = true := by
  rfl'

private theorem leaf4764CoversExact : CoversExact 8
    leaf4764Box leaf4764Certificate leaf4764InnerLog leaf4764Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi276RoundedFacts
    innerPair101RoundedFacts leaf4764RoundedFacts (by rfl)

private theorem leaf4764FlatSound : Sound leaf4764Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4764CertificateValid
    leaf4764InnerLogValid leaf4764CoversExact leaf4764LowerChecked

private noncomputable def leaf4765Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4765Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431332352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2029951415/1073741824) }, upper := { exponent := 0, mantissa := (31269/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868254207/274862664704) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4765InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4765LocalValidity :
    LeafFacts leaf4765Box leaf4765Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4765Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431332352) }) = true
      norm_num [leaf4765Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4765CertificateValid :
    WideCertificateValid leaf4765Box leaf4765Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi277ValidityFacts
    leaf4765LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4765CoverageChecked :
    coverageCheck (innerAD leaf4765Box) leaf4765InnerLog = true := by
  rfl'

private theorem leaf4765InnerLogValid :
    leaf4765InnerLog.Valid 8 (innerAD leaf4765Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4765CoverageChecked

private noncomputable def leaf4765InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4765InputLogOnePlusV_eq :
    leaf4765InputLogOnePlusV = outerEnclosure 24
      (leaf4765Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4765RoundedFacts : LeafRoundedFacts 8
    leaf4765Certificate.logOnePlusV leaf4765InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4765InputLogOnePlusV_eq }

private noncomputable def leaf4765Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4765InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4765LowerChecked :
    lowerCheck 24 leaf4765Box leaf4765Inputs = true := by
  rfl'

private theorem leaf4765CoversExact : CoversExact 8
    leaf4765Box leaf4765Certificate leaf4765InnerLog leaf4765Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4765RoundedFacts (by rfl)

private theorem leaf4765FlatSound : Sound leaf4765Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4765CertificateValid
    leaf4765InnerLogValid leaf4765CoversExact leaf4765LowerChecked

private noncomputable def leaf4766Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4766Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810433024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2034145461/1073741824) }, upper := { exponent := 0, mantissa := (15667/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622740309/91620866048) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4766InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4766LocalValidity :
    LeafFacts leaf4766Box leaf4766Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4766Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810433024) }) = true
      norm_num [leaf4766Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4766CertificateValid :
    WideCertificateValid leaf4766Box leaf4766Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi277ValidityFacts
    leaf4766LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4766CoverageChecked :
    coverageCheck (innerAD leaf4766Box) leaf4766InnerLog = true := by
  rfl'

private theorem leaf4766InnerLogValid :
    leaf4766InnerLog.Valid 8 (innerAD leaf4766Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4766CoverageChecked

private noncomputable def leaf4766InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4766InputLogOnePlusV_eq :
    leaf4766InputLogOnePlusV = outerEnclosure 24
      (leaf4766Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4766RoundedFacts : LeafRoundedFacts 8
    leaf4766Certificate.logOnePlusV leaf4766InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4766InputLogOnePlusV_eq }

private noncomputable def leaf4766Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4766InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4766LowerChecked :
    lowerCheck 24 leaf4766Box leaf4766Inputs = true := by
  rfl'

private theorem leaf4766CoversExact : CoversExact 8
    leaf4766Box leaf4766Certificate leaf4766InnerLog leaf4766Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4766RoundedFacts (by rfl)

private theorem leaf4766FlatSound : Sound leaf4766Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4766CertificateValid
    leaf4766InnerLogValid leaf4766CoversExact leaf4766LowerChecked

private noncomputable def leaf4767Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4767Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431215104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2044892709/1073741824) }, upper := { exponent := 0, mantissa := (15749/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868136959/274862430208) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4767InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4767LocalValidity :
    LeafFacts leaf4767Box leaf4767Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4767Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431215104) }) = true
      norm_num [leaf4767Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4767CertificateValid :
    WideCertificateValid leaf4767Box leaf4767Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi278ValidityFacts
    leaf4767LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4767CoverageChecked :
    coverageCheck (innerAD leaf4767Box) leaf4767InnerLog = true := by
  rfl'

private theorem leaf4767InnerLogValid :
    leaf4767InnerLog.Valid 8 (innerAD leaf4767Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4767CoverageChecked

private noncomputable def leaf4767InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4767InputLogOnePlusV_eq :
    leaf4767InputLogOnePlusV = outerEnclosure 24
      (leaf4767Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4767RoundedFacts : LeafRoundedFacts 8
    leaf4767Certificate.logOnePlusV leaf4767InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4767InputLogOnePlusV_eq }

private noncomputable def leaf4767Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4767InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4767LowerChecked :
    lowerCheck 24 leaf4767Box leaf4767Inputs = true := by
  rfl'

private theorem leaf4767CoversExact : CoversExact 8
    leaf4767Box leaf4767Certificate leaf4767InnerLog leaf4767Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4767RoundedFacts (by rfl)

private theorem leaf4767FlatSound : Sound leaf4767Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4767CertificateValid
    leaf4767InnerLogValid leaf4767CoversExact leaf4767LowerChecked

private noncomputable def leaf4768Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4768Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (188012205/188004352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2049152287/1073741824) }, upper := { exponent := 0, mantissa := (7891/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (376016557/376008704) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4768InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4768LocalValidity :
    LeafFacts leaf4768Box leaf4768Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4768Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (188012205/188004352) }) = true
      norm_num [leaf4768Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4768CertificateValid :
    WideCertificateValid leaf4768Box leaf4768Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi278ValidityFacts
    leaf4768LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4768CoverageChecked :
    coverageCheck (innerAD leaf4768Box) leaf4768InnerLog = true := by
  rfl'

private theorem leaf4768InnerLogValid :
    leaf4768InnerLog.Valid 8 (innerAD leaf4768Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4768CoverageChecked

private noncomputable def leaf4768InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4768InputLogOnePlusV_eq :
    leaf4768InputLogOnePlusV = outerEnclosure 24
      (leaf4768Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4768RoundedFacts : LeafRoundedFacts 8
    leaf4768Certificate.logOnePlusV leaf4768InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4768InputLogOnePlusV_eq }

private noncomputable def leaf4768Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4768InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4768LowerChecked :
    lowerCheck 24 leaf4768Box leaf4768Inputs = true := by
  rfl'

private theorem leaf4768CoversExact : CoversExact 8
    leaf4768Box leaf4768Certificate leaf4768InnerLog leaf4768Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4768RoundedFacts (by rfl)

private theorem leaf4768FlatSound : Sound leaf4768Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4768CertificateValid
    leaf4768InnerLogValid leaf4768CoversExact leaf4768LowerChecked

private noncomputable def leaf4769Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4769Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431265792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2038339507/1073741824) }, upper := { exponent := 0, mantissa := (31399/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868187647/274862531584) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4769InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4769LocalValidity :
    LeafFacts leaf4769Box leaf4769Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4769Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431265792) }) = true
      norm_num [leaf4769Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4769CertificateValid :
    WideCertificateValid leaf4769Box leaf4769Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi277ValidityFacts
    leaf4769LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4769CoverageChecked :
    coverageCheck (innerAD leaf4769Box) leaf4769InnerLog = true := by
  rfl'

private theorem leaf4769InnerLogValid :
    leaf4769InnerLog.Valid 8 (innerAD leaf4769Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4769CoverageChecked

private noncomputable def leaf4769InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4769InputLogOnePlusV_eq :
    leaf4769InputLogOnePlusV = outerEnclosure 24
      (leaf4769Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4769RoundedFacts : LeafRoundedFacts 8
    leaf4769Certificate.logOnePlusV leaf4769InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4769InputLogOnePlusV_eq }

private noncomputable def leaf4769Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4769InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4769LowerChecked :
    lowerCheck 24 leaf4769Box leaf4769Inputs = true := by
  rfl'

private theorem leaf4769CoversExact : CoversExact 8
    leaf4769Box leaf4769Certificate leaf4769InnerLog leaf4769Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4769RoundedFacts (by rfl)

private theorem leaf4769FlatSound : Sound leaf4769Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4769CertificateValid
    leaf4769InnerLogValid leaf4769CoversExact leaf4769LowerChecked

private noncomputable def leaf4770Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4770Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431232512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2042533553/1073741824) }, upper := { exponent := 0, mantissa := (3933/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868154367/274862465024) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4770InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4770LocalValidity :
    LeafFacts leaf4770Box leaf4770Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4770Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431232512) }) = true
      norm_num [leaf4770Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4770CertificateValid :
    WideCertificateValid leaf4770Box leaf4770Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi277ValidityFacts
    leaf4770LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4770CoverageChecked :
    coverageCheck (innerAD leaf4770Box) leaf4770InnerLog = true := by
  rfl'

private theorem leaf4770InnerLogValid :
    leaf4770InnerLog.Valid 8 (innerAD leaf4770Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4770CoverageChecked

private noncomputable def leaf4770InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4770InputLogOnePlusV_eq :
    leaf4770InputLogOnePlusV = outerEnclosure 24
      (leaf4770Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4770RoundedFacts : LeafRoundedFacts 8
    leaf4770Certificate.logOnePlusV leaf4770InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4770InputLogOnePlusV_eq }

private noncomputable def leaf4770Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi277InputQChi innerPair100Input
    leaf4770InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4770LowerChecked :
    lowerCheck 24 leaf4770Box leaf4770Inputs = true := by
  rfl'

private theorem leaf4770CoversExact : CoversExact 8
    leaf4770Box leaf4770Certificate leaf4770InnerLog leaf4770Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi277RoundedFacts
    innerPair100RoundedFacts leaf4770RoundedFacts (by rfl)

private theorem leaf4770FlatSound : Sound leaf4770Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4770CertificateValid
    leaf4770InnerLogValid leaf4770CoversExact leaf4770LowerChecked

private noncomputable def leaf4771Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4771Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486229504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2053411865/1073741824) }, upper := { exponent := 0, mantissa := (15815/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973613875/54972459008) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4771InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4771LocalValidity :
    LeafFacts leaf4771Box leaf4771Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4771Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486229504) }) = true
      norm_num [leaf4771Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4771CertificateValid :
    WideCertificateValid leaf4771Box leaf4771Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi278ValidityFacts
    leaf4771LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4771CoverageChecked :
    coverageCheck (innerAD leaf4771Box) leaf4771InnerLog = true := by
  rfl'

private theorem leaf4771InnerLogValid :
    leaf4771InnerLog.Valid 8 (innerAD leaf4771Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4771CoverageChecked

private noncomputable def leaf4771InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4771InputLogOnePlusV_eq :
    leaf4771InputLogOnePlusV = outerEnclosure 24
      (leaf4771Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4771RoundedFacts : LeafRoundedFacts 8
    leaf4771Certificate.logOnePlusV leaf4771InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4771InputLogOnePlusV_eq }

private noncomputable def leaf4771Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4771InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4771LowerChecked :
    lowerCheck 24 leaf4771Box leaf4771Inputs = true := by
  rfl'

private theorem leaf4771CoversExact : CoversExact 8
    leaf4771Box leaf4771Certificate leaf4771InnerLog leaf4771Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4771RoundedFacts (by rfl)

private theorem leaf4771FlatSound : Sound leaf4771Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4771CertificateValid
    leaf4771InnerLogValid leaf4771CoversExact leaf4771LowerChecked

private noncomputable def leaf4772Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4772Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431113728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2057671443/1073741824) }, upper := { exponent := 0, mantissa := (1981/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868035583/274862227456) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4772InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4772LocalValidity :
    LeafFacts leaf4772Box leaf4772Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4772Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431113728) }) = true
      norm_num [leaf4772Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4772CertificateValid :
    WideCertificateValid leaf4772Box leaf4772Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi278ValidityFacts
    leaf4772LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4772CoverageChecked :
    coverageCheck (innerAD leaf4772Box) leaf4772InnerLog = true := by
  rfl'

private theorem leaf4772InnerLogValid :
    leaf4772InnerLog.Valid 8 (innerAD leaf4772Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4772CoverageChecked

private noncomputable def leaf4772InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4772InputLogOnePlusV_eq :
    leaf4772InputLogOnePlusV = outerEnclosure 24
      (leaf4772Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4772RoundedFacts : LeafRoundedFacts 8
    leaf4772Certificate.logOnePlusV leaf4772InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4772InputLogOnePlusV_eq }

private noncomputable def leaf4772Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4772InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4772LowerChecked :
    lowerCheck 24 leaf4772Box leaf4772Inputs = true := by
  rfl'

private theorem leaf4772CoversExact : CoversExact 8
    leaf4772Box leaf4772Certificate leaf4772InnerLog leaf4772Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4772RoundedFacts (by rfl)

private theorem leaf4772FlatSound : Sound leaf4772Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4772CertificateValid
    leaf4772InnerLogValid leaf4772CoversExact leaf4772LowerChecked

private noncomputable def leaf4773Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4773Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270121984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2059834003/1073741824) }, upper := { exponent := 0, mantissa := (31727/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540891079/30540243968) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4773InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4773LocalValidity :
    LeafFacts leaf4773Box leaf4773Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4773Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270121984) }) = true
      norm_num [leaf4773Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4773CertificateValid :
    WideCertificateValid leaf4773Box leaf4773Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi275ValidityFacts
    leaf4773LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4773CoverageChecked :
    coverageCheck (innerAD leaf4773Box) leaf4773InnerLog = true := by
  rfl'

private theorem leaf4773InnerLogValid :
    leaf4773InnerLog.Valid 8 (innerAD leaf4773Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4773CoverageChecked

private noncomputable def leaf4773InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4773InputLogOnePlusV_eq :
    leaf4773InputLogOnePlusV = outerEnclosure 24
      (leaf4773Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4773RoundedFacts : LeafRoundedFacts 8
    leaf4773Certificate.logOnePlusV leaf4773InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4773InputLogOnePlusV_eq }

private noncomputable def leaf4773Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4773InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4773LowerChecked :
    lowerCheck 24 leaf4773Box leaf4773Inputs = true := by
  rfl'

private theorem leaf4773CoversExact : CoversExact 8
    leaf4773Box leaf4773Certificate leaf4773InnerLog leaf4773Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4773RoundedFacts (by rfl)

private theorem leaf4773FlatSound : Sound leaf4773Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4773CertificateValid
    leaf4773InnerLogValid leaf4773CoversExact leaf4773LowerChecked

private noncomputable def leaf4774Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4774Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431063552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2064159113/1073741824) }, upper := { exponent := 0, mantissa := (15897/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867985407/274862127104) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4774InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4774LocalValidity :
    LeafFacts leaf4774Box leaf4774Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4774Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431063552) }) = true
      norm_num [leaf4774Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4774CertificateValid :
    WideCertificateValid leaf4774Box leaf4774Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi275ValidityFacts
    leaf4774LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4774CoverageChecked :
    coverageCheck (innerAD leaf4774Box) leaf4774InnerLog = true := by
  rfl'

private theorem leaf4774InnerLogValid :
    leaf4774InnerLog.Valid 8 (innerAD leaf4774Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4774CoverageChecked

private noncomputable def leaf4774InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4774InputLogOnePlusV_eq :
    leaf4774InputLogOnePlusV = outerEnclosure 24
      (leaf4774Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4774RoundedFacts : LeafRoundedFacts 8
    leaf4774Certificate.logOnePlusV leaf4774InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4774InputLogOnePlusV_eq }

private noncomputable def leaf4774Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi275InputQChi innerPair304Input
    leaf4774InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4774LowerChecked :
    lowerCheck 24 leaf4774Box leaf4774Inputs = true := by
  rfl'

private theorem leaf4774CoversExact : CoversExact 8
    leaf4774Box leaf4774Certificate leaf4774InnerLog leaf4774Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi275RoundedFacts
    innerPair304RoundedFacts leaf4774RoundedFacts (by rfl)

private theorem leaf4774FlatSound : Sound leaf4774Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4774CertificateValid
    leaf4774InnerLogValid leaf4774CoversExact leaf4774LowerChecked

private noncomputable def leaf4775Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4775Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430980608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2074775297/1073741824) }, upper := { exponent := 0, mantissa := (7989/4096) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867902463/274861961216) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4775InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4775LocalValidity :
    LeafFacts leaf4775Box leaf4775Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4775Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430980608) }) = true
      norm_num [leaf4775Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4775CertificateValid :
    WideCertificateValid leaf4775Box leaf4775Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi276ValidityFacts
    leaf4775LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4775CoverageChecked :
    coverageCheck (innerAD leaf4775Box) leaf4775InnerLog = true := by
  rfl'

private theorem leaf4775InnerLogValid :
    leaf4775InnerLog.Valid 8 (innerAD leaf4775Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4775CoverageChecked

private noncomputable def leaf4775InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4775InputLogOnePlusV_eq :
    leaf4775InputLogOnePlusV = outerEnclosure 24
      (leaf4775Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4775RoundedFacts : LeafRoundedFacts 8
    leaf4775Certificate.logOnePlusV leaf4775InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4775InputLogOnePlusV_eq }

private noncomputable def leaf4775Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi276InputQChi innerPair101Input
    leaf4775InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4775LowerChecked :
    lowerCheck 24 leaf4775Box leaf4775Inputs = true := by
  rfl'

private theorem leaf4775CoversExact : CoversExact 8
    leaf4775Box leaf4775Certificate leaf4775InnerLog leaf4775Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi276RoundedFacts
    innerPair101RoundedFacts leaf4775RoundedFacts (by rfl)

private theorem leaf4775FlatSound : Sound leaf4775Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4775CertificateValid
    leaf4775InnerLogValid leaf4775CoversExact leaf4775LowerChecked

private noncomputable def leaf4776Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4776Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270105088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2079165939/1073741824) }, upper := { exponent := 0, mantissa := (4003/2048) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540874183/30540210176) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4776InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4776LocalValidity :
    LeafFacts leaf4776Box leaf4776Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4776Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270105088) }) = true
      norm_num [leaf4776Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4776CertificateValid :
    WideCertificateValid leaf4776Box leaf4776Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi276ValidityFacts
    leaf4776LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4776CoverageChecked :
    coverageCheck (innerAD leaf4776Box) leaf4776InnerLog = true := by
  rfl'

private theorem leaf4776InnerLogValid :
    leaf4776InnerLog.Valid 8 (innerAD leaf4776Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4776CoverageChecked

private noncomputable def leaf4776InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4776InputLogOnePlusV_eq :
    leaf4776InputLogOnePlusV = outerEnclosure 24
      (leaf4776Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4776RoundedFacts : LeafRoundedFacts 8
    leaf4776Certificate.logOnePlusV leaf4776InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4776InputLogOnePlusV_eq }

private noncomputable def leaf4776Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi276InputQChi innerPair101Input
    leaf4776InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4776LowerChecked :
    lowerCheck 24 leaf4776Box leaf4776Inputs = true := by
  rfl'

private theorem leaf4776CoversExact : CoversExact 8
    leaf4776Box leaf4776Certificate leaf4776InnerLog leaf4776Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi276RoundedFacts
    innerPair101RoundedFacts leaf4776RoundedFacts (by rfl)

private theorem leaf4776FlatSound : Sound leaf4776Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4776CertificateValid
    leaf4776InnerLogValid leaf4776CoversExact leaf4776LowerChecked

private noncomputable def leaf4777Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4777Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431029248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2068484223/1073741824) }, upper := { exponent := 0, mantissa := (31861/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867951103/274862058496) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4777InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf4777LocalValidity :
    LeafFacts leaf4777Box leaf4777Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4777Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431029248) }) = true
      norm_num [leaf4777Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4777CertificateValid :
    WideCertificateValid leaf4777Box leaf4777Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi275ValidityFacts
    leaf4777LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4777CoverageChecked :
    coverageCheck (innerAD leaf4777Box) leaf4777InnerLog = true := by
  rfl'

private theorem leaf4777InnerLogValid :
    leaf4777InnerLog.Valid 8 (innerAD leaf4777Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf4777CoverageChecked

private noncomputable def leaf4777InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4777InputLogOnePlusV_eq :
    leaf4777InputLogOnePlusV = outerEnclosure 24
      (leaf4777Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4777RoundedFacts : LeafRoundedFacts 8
    leaf4777Certificate.logOnePlusV leaf4777InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4777InputLogOnePlusV_eq }

private noncomputable def leaf4777Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi275InputQChi innerPair304Input
    leaf4777InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4777LowerChecked :
    lowerCheck 24 leaf4777Box leaf4777Inputs = true := by
  rfl'

private theorem leaf4777CoversExact : CoversExact 8
    leaf4777Box leaf4777Certificate leaf4777InnerLog leaf4777Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi275RoundedFacts
    innerPair304RoundedFacts leaf4777RoundedFacts (by rfl)

private theorem leaf4777FlatSound : Sound leaf4777Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4777CertificateValid
    leaf4777InnerLogValid leaf4777CoversExact leaf4777LowerChecked

private noncomputable def leaf4778Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4778Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810331648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2072809333/1073741824) }, upper := { exponent := 0, mantissa := (3991/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622638933/91620663296) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4778InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4778LocalValidity :
    LeafFacts leaf4778Box leaf4778Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4778Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810331648) }) = true
      norm_num [leaf4778Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4778CertificateValid :
    WideCertificateValid leaf4778Box leaf4778Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi275ValidityFacts
    leaf4778LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4778CoverageChecked :
    coverageCheck (innerAD leaf4778Box) leaf4778InnerLog = true := by
  rfl'

private theorem leaf4778InnerLogValid :
    leaf4778InnerLog.Valid 8 (innerAD leaf4778Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4778CoverageChecked

private noncomputable def leaf4778InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4778InputLogOnePlusV_eq :
    leaf4778InputLogOnePlusV = outerEnclosure 24
      (leaf4778Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4778RoundedFacts : LeafRoundedFacts 8
    leaf4778Certificate.logOnePlusV leaf4778InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4778InputLogOnePlusV_eq }

private noncomputable def leaf4778Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi275InputQChi innerPair101Input
    leaf4778InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4778LowerChecked :
    lowerCheck 24 leaf4778Box leaf4778Inputs = true := by
  rfl'

private theorem leaf4778CoversExact : CoversExact 8
    leaf4778Box leaf4778Certificate leaf4778InnerLog leaf4778Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi275RoundedFacts
    innerPair101RoundedFacts leaf4778RoundedFacts (by rfl)

private theorem leaf4778FlatSound : Sound leaf4778Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4778CertificateValid
    leaf4778InnerLogValid leaf4778CoversExact leaf4778LowerChecked

private noncomputable def leaf4779Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4779Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430910976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2083556581/1073741824) }, upper := { exponent := 0, mantissa := (8023/4096) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867832831/274861821952) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4779InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4779LocalValidity :
    LeafFacts leaf4779Box leaf4779Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4779Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430910976) }) = true
      norm_num [leaf4779Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4779CertificateValid :
    WideCertificateValid leaf4779Box leaf4779Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi276ValidityFacts
    leaf4779LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4779CoverageChecked :
    coverageCheck (innerAD leaf4779Box) leaf4779InnerLog = true := by
  rfl'

private theorem leaf4779InnerLogValid :
    leaf4779InnerLog.Valid 8 (innerAD leaf4779Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4779CoverageChecked

private noncomputable def leaf4779InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4779InputLogOnePlusV_eq :
    leaf4779InputLogOnePlusV = outerEnclosure 24
      (leaf4779Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4779RoundedFacts : LeafRoundedFacts 8
    leaf4779Certificate.logOnePlusV leaf4779InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4779InputLogOnePlusV_eq }

private noncomputable def leaf4779Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4779InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4779LowerChecked :
    lowerCheck 24 leaf4779Box leaf4779Inputs = true := by
  rfl'

private theorem leaf4779CoversExact : CoversExact 8
    leaf4779Box leaf4779Certificate leaf4779InnerLog leaf4779Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4779RoundedFacts (by rfl)

private theorem leaf4779FlatSound : Sound leaf4779Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4779CertificateValid
    leaf4779InnerLogValid leaf4779CoversExact leaf4779LowerChecked

private noncomputable def leaf4780Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4780Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486175232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2087947223/1073741824) }, upper := { exponent := 0, mantissa := (1005/512) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973559603/54972350464) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4780InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4780LocalValidity :
    LeafFacts leaf4780Box leaf4780Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4780Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486175232) }) = true
      norm_num [leaf4780Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4780CertificateValid :
    WideCertificateValid leaf4780Box leaf4780Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi276ValidityFacts
    leaf4780LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4780CoverageChecked :
    coverageCheck (innerAD leaf4780Box) leaf4780InnerLog = true := by
  rfl'

private theorem leaf4780InnerLogValid :
    leaf4780InnerLog.Valid 8 (innerAD leaf4780Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4780CoverageChecked

private noncomputable def leaf4780InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4780InputLogOnePlusV_eq :
    leaf4780InputLogOnePlusV = outerEnclosure 24
      (leaf4780Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4780RoundedFacts : LeafRoundedFacts 8
    leaf4780Certificate.logOnePlusV leaf4780InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4780InputLogOnePlusV_eq }

private noncomputable def leaf4780Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi276InputQChi innerPair108Input
    leaf4780InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4780LowerChecked :
    lowerCheck 24 leaf4780Box leaf4780Inputs = true := by
  rfl'

private theorem leaf4780CoversExact : CoversExact 8
    leaf4780Box leaf4780Certificate leaf4780InnerLog leaf4780Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi276RoundedFacts
    innerPair108RoundedFacts leaf4780RoundedFacts (by rfl)

private theorem leaf4780FlatSound : Sound leaf4780Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4780CertificateValid
    leaf4780InnerLogValid leaf4780CoversExact leaf4780LowerChecked

private noncomputable def leaf4781Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4781Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431004672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2071891895/1073741824) }, upper := { exponent := 0, mantissa := (31909/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867926527/274862009344) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4781InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4781LocalValidity :
    LeafFacts leaf4781Box leaf4781Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4781Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431004672) }) = true
      norm_num [leaf4781Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4781CertificateValid :
    WideCertificateValid leaf4781Box leaf4781Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi257ValidityFacts
    leaf4781LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4781CoverageChecked :
    coverageCheck (innerAD leaf4781Box) leaf4781InnerLog = true := by
  rfl'

private theorem leaf4781InnerLogValid :
    leaf4781InnerLog.Valid 8 (innerAD leaf4781Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4781CoverageChecked

private noncomputable def leaf4781InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4781InputLogOnePlusV_eq :
    leaf4781InputLogOnePlusV = outerEnclosure 24
      (leaf4781Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4781RoundedFacts : LeafRoundedFacts 8
    leaf4781Certificate.logOnePlusV leaf4781InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4781InputLogOnePlusV_eq }

private noncomputable def leaf4781Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi257InputQChi innerPair101Input
    leaf4781InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4781LowerChecked :
    lowerCheck 24 leaf4781Box leaf4781Inputs = true := by
  rfl'

private theorem leaf4781CoversExact : CoversExact 8
    leaf4781Box leaf4781Certificate leaf4781InnerLog leaf4781Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi257RoundedFacts
    innerPair101RoundedFacts leaf4781RoundedFacts (by rfl)

private theorem leaf4781FlatSound : Sound leaf4781Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4781CertificateValid
    leaf4781InnerLogValid leaf4781CoversExact leaf4781LowerChecked

private noncomputable def leaf4782Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4782Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430969344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2076348069/1073741824) }, upper := { exponent := 0, mantissa := (15989/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867891199/274861938688) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4782InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4782LocalValidity :
    LeafFacts leaf4782Box leaf4782Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4782Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430969344) }) = true
      norm_num [leaf4782Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4782CertificateValid :
    WideCertificateValid leaf4782Box leaf4782Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi257ValidityFacts
    leaf4782LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4782CoverageChecked :
    coverageCheck (innerAD leaf4782Box) leaf4782InnerLog = true := by
  rfl'

private theorem leaf4782InnerLogValid :
    leaf4782InnerLog.Valid 8 (innerAD leaf4782Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4782CoverageChecked

private noncomputable def leaf4782InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4782InputLogOnePlusV_eq :
    leaf4782InputLogOnePlusV = outerEnclosure 24
      (leaf4782Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4782RoundedFacts : LeafRoundedFacts 8
    leaf4782Certificate.logOnePlusV leaf4782InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4782InputLogOnePlusV_eq }

private noncomputable def leaf4782Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi257InputQChi innerPair101Input
    leaf4782InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4782LowerChecked :
    lowerCheck 24 leaf4782Box leaf4782Inputs = true := by
  rfl'

private theorem leaf4782CoversExact : CoversExact 8
    leaf4782Box leaf4782Certificate leaf4782InnerLog leaf4782Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi257RoundedFacts
    innerPair101RoundedFacts leaf4782RoundedFacts (by rfl)

private theorem leaf4782FlatSound : Sound leaf4782Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4782CertificateValid
    leaf4782InnerLogValid leaf4782CoversExact leaf4782LowerChecked

private noncomputable def leaf4783Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4783Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430889472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2086571061/1073741824) }, upper := { exponent := 0, mantissa := (16067/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867811327/274861778944) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4783InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4783LocalValidity :
    LeafFacts leaf4783Box leaf4783Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4783Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430889472) }) = true
      norm_num [leaf4783Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4783CertificateValid :
    WideCertificateValid leaf4783Box leaf4783Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi258ValidityFacts
    leaf4783LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4783CoverageChecked :
    coverageCheck (innerAD leaf4783Box) leaf4783InnerLog = true := by
  rfl'

private theorem leaf4783InnerLogValid :
    leaf4783InnerLog.Valid 8 (innerAD leaf4783Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4783CoverageChecked

private noncomputable def leaf4783InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4783InputLogOnePlusV_eq :
    leaf4783InputLogOnePlusV = outerEnclosure 24
      (leaf4783Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4783RoundedFacts : LeafRoundedFacts 8
    leaf4783Certificate.logOnePlusV leaf4783InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4783InputLogOnePlusV_eq }

private noncomputable def leaf4783Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4783InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4783LowerChecked :
    lowerCheck 24 leaf4783Box leaf4783Inputs = true := by
  rfl'

private theorem leaf4783CoversExact : CoversExact 8
    leaf4783Box leaf4783Certificate leaf4783InnerLog leaf4783Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4783RoundedFacts (by rfl)

private theorem leaf4783FlatSound : Sound leaf4783Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4783CertificateValid
    leaf4783InnerLogValid leaf4783CoversExact leaf4783LowerChecked

private noncomputable def leaf4784Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4784Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090031616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2091092767/1073741824) }, upper := { exponent := 0, mantissa := (8051/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180287981/10180063232) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4784InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4784LocalValidity :
    LeafFacts leaf4784Box leaf4784Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4784Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090031616) }) = true
      norm_num [leaf4784Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4784CertificateValid :
    WideCertificateValid leaf4784Box leaf4784Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi258ValidityFacts
    leaf4784LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4784CoverageChecked :
    coverageCheck (innerAD leaf4784Box) leaf4784InnerLog = true := by
  rfl'

private theorem leaf4784InnerLogValid :
    leaf4784InnerLog.Valid 8 (innerAD leaf4784Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4784CoverageChecked

private noncomputable def leaf4784InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4784InputLogOnePlusV_eq :
    leaf4784InputLogOnePlusV = outerEnclosure 24
      (leaf4784Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4784RoundedFacts : LeafRoundedFacts 8
    leaf4784Certificate.logOnePlusV leaf4784InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4784InputLogOnePlusV_eq }

private noncomputable def leaf4784Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4784InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4784LowerChecked :
    lowerCheck 24 leaf4784Box leaf4784Inputs = true := by
  rfl'

private theorem leaf4784CoversExact : CoversExact 8
    leaf4784Box leaf4784Certificate leaf4784InnerLog leaf4784Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4784RoundedFacts (by rfl)

private theorem leaf4784FlatSound : Sound leaf4784Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4784CertificateValid
    leaf4784InnerLogValid leaf4784CoversExact leaf4784LowerChecked

private noncomputable def leaf4785Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4785Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430934016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2080804243/1073741824) }, upper := { exponent := 0, mantissa := (32047/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867855871/274861868032) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4785InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4785LocalValidity :
    LeafFacts leaf4785Box leaf4785Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4785Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430934016) }) = true
      norm_num [leaf4785Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4785CertificateValid :
    WideCertificateValid leaf4785Box leaf4785Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi257ValidityFacts
    leaf4785LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4785CoverageChecked :
    coverageCheck (innerAD leaf4785Box) leaf4785InnerLog = true := by
  rfl'

private theorem leaf4785InnerLogValid :
    leaf4785InnerLog.Valid 8 (innerAD leaf4785Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4785CoverageChecked

private noncomputable def leaf4785InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4785InputLogOnePlusV_eq :
    leaf4785InputLogOnePlusV = outerEnclosure 24
      (leaf4785Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4785RoundedFacts : LeafRoundedFacts 8
    leaf4785Certificate.logOnePlusV leaf4785InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4785InputLogOnePlusV_eq }

private noncomputable def leaf4785Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4785InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4785LowerChecked :
    lowerCheck 24 leaf4785Box leaf4785Inputs = true := by
  rfl'

private theorem leaf4785CoversExact : CoversExact 8
    leaf4785Box leaf4785Certificate leaf4785InnerLog leaf4785Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4785RoundedFacts (by rfl)

private theorem leaf4785FlatSound : Sound leaf4785Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4785CertificateValid
    leaf4785InnerLogValid leaf4785CoversExact leaf4785LowerChecked

private noncomputable def leaf4786Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4786Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430898688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2085260417/1073741824) }, upper := { exponent := 0, mantissa := (8029/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867820543/274861797376) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4786InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4786LocalValidity :
    LeafFacts leaf4786Box leaf4786Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4786Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430898688) }) = true
      norm_num [leaf4786Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4786CertificateValid :
    WideCertificateValid leaf4786Box leaf4786Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi257ValidityFacts
    leaf4786LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4786CoverageChecked :
    coverageCheck (innerAD leaf4786Box) leaf4786InnerLog = true := by
  rfl'

private theorem leaf4786InnerLogValid :
    leaf4786InnerLog.Valid 8 (innerAD leaf4786Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4786CoverageChecked

private noncomputable def leaf4786InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4786InputLogOnePlusV_eq :
    leaf4786InputLogOnePlusV = outerEnclosure 24
      (leaf4786Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4786RoundedFacts : LeafRoundedFacts 8
    leaf4786Certificate.logOnePlusV leaf4786InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4786InputLogOnePlusV_eq }

private noncomputable def leaf4786Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4786InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4786LowerChecked :
    lowerCheck 24 leaf4786Box leaf4786Inputs = true := by
  rfl'

private theorem leaf4786CoversExact : CoversExact 8
    leaf4786Box leaf4786Certificate leaf4786InnerLog leaf4786Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4786RoundedFacts (by rfl)

private theorem leaf4786FlatSound : Sound leaf4786Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4786CertificateValid
    leaf4786InnerLogValid leaf4786CoversExact leaf4786LowerChecked

private noncomputable def leaf4787Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4787Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430817792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2095614473/1073741824) }, upper := { exponent := 0, mantissa := (16137/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867739647/274861635584) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4787InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4787LocalValidity :
    LeafFacts leaf4787Box leaf4787Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4787Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430817792) }) = true
      norm_num [leaf4787Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4787CertificateValid :
    WideCertificateValid leaf4787Box leaf4787Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi258ValidityFacts
    leaf4787LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4787CoverageChecked :
    coverageCheck (innerAD leaf4787Box) leaf4787InnerLog = true := by
  rfl'

private theorem leaf4787InnerLogValid :
    leaf4787InnerLog.Valid 8 (innerAD leaf4787Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4787CoverageChecked

private noncomputable def leaf4787InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4787InputLogOnePlusV_eq :
    leaf4787InputLogOnePlusV = outerEnclosure 24
      (leaf4787Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4787RoundedFacts : LeafRoundedFacts 8
    leaf4787Certificate.logOnePlusV leaf4787InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4787InputLogOnePlusV_eq }

private noncomputable def leaf4787Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4787InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4787LowerChecked :
    lowerCheck 24 leaf4787Box leaf4787Inputs = true := by
  rfl'

private theorem leaf4787CoversExact : CoversExact 8
    leaf4787Box leaf4787Certificate leaf4787InnerLog leaf4787Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4787RoundedFacts (by rfl)

private theorem leaf4787FlatSound : Sound leaf4787Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4787CertificateValid
    leaf4787InnerLogValid leaf4787CoversExact leaf4787LowerChecked

private noncomputable def leaf4788Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4788Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430781952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2100136179/1073741824) }, upper := { exponent := 0, mantissa := (4043/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867703807/274861563904) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4788InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4788LocalValidity :
    LeafFacts leaf4788Box leaf4788Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4788Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430781952) }) = true
      norm_num [leaf4788Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4788CertificateValid :
    WideCertificateValid leaf4788Box leaf4788Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi258ValidityFacts
    leaf4788LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4788CoverageChecked :
    coverageCheck (innerAD leaf4788Box) leaf4788InnerLog = true := by
  rfl'

private theorem leaf4788InnerLogValid :
    leaf4788InnerLog.Valid 8 (innerAD leaf4788Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4788CoverageChecked

private noncomputable def leaf4788InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4788InputLogOnePlusV_eq :
    leaf4788InputLogOnePlusV = outerEnclosure 24
      (leaf4788Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4788RoundedFacts : LeafRoundedFacts 8
    leaf4788Certificate.logOnePlusV leaf4788InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4788InputLogOnePlusV_eq }

private noncomputable def leaf4788Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4788InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4788LowerChecked :
    lowerCheck 24 leaf4788Box leaf4788Inputs = true := by
  rfl'

private theorem leaf4788CoversExact : CoversExact 8
    leaf4788Box leaf4788Certificate leaf4788InnerLog leaf4788Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4788RoundedFacts (by rfl)

private theorem leaf4788FlatSound : Sound leaf4788Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4788CertificateValid
    leaf4788InnerLogValid leaf4788CoversExact leaf4788LowerChecked

private noncomputable def leaf4789Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4789Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430774272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2101250227/1073741824) }, upper := { exponent := 0, mantissa := (32359/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867696127/274861548544) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4789InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4789LocalValidity :
    LeafFacts leaf4789Box leaf4789Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4789Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430774272) }) = true
      norm_num [leaf4789Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4789CertificateValid :
    WideCertificateValid leaf4789Box leaf4789Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi279ValidityFacts
    leaf4789LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4789CoverageChecked :
    coverageCheck (innerAD leaf4789Box) leaf4789InnerLog = true := by
  rfl'

private theorem leaf4789InnerLogValid :
    leaf4789InnerLog.Valid 8 (innerAD leaf4789Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4789CoverageChecked

private noncomputable def leaf4789InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4789InputLogOnePlusV_eq :
    leaf4789InputLogOnePlusV = outerEnclosure 24
      (leaf4789Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4789RoundedFacts : LeafRoundedFacts 8
    leaf4789Certificate.logOnePlusV leaf4789InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4789InputLogOnePlusV_eq }

private noncomputable def leaf4789Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4789InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4789LowerChecked :
    lowerCheck 24 leaf4789Box leaf4789Inputs = true := by
  rfl'

private theorem leaf4789CoversExact : CoversExact 8
    leaf4789Box leaf4789Certificate leaf4789InnerLog leaf4789Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4789RoundedFacts (by rfl)

private theorem leaf4789FlatSound : Sound leaf4789Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4789CertificateValid
    leaf4789InnerLogValid leaf4789CoversExact leaf4789LowerChecked

private noncomputable def leaf4790Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4790Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486147584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2105837465/1073741824) }, upper := { exponent := 0, mantissa := (16215/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973531955/54972295168) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4790InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4790LocalValidity :
    LeafFacts leaf4790Box leaf4790Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4790Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486147584) }) = true
      norm_num [leaf4790Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4790CertificateValid :
    WideCertificateValid leaf4790Box leaf4790Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi279ValidityFacts
    leaf4790LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4790CoverageChecked :
    coverageCheck (innerAD leaf4790Box) leaf4790InnerLog = true := by
  rfl'

private theorem leaf4790InnerLogValid :
    leaf4790InnerLog.Valid 8 (innerAD leaf4790Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4790CoverageChecked

private noncomputable def leaf4790InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4790InputLogOnePlusV_eq :
    leaf4790InputLogOnePlusV = outerEnclosure 24
      (leaf4790Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4790RoundedFacts : LeafRoundedFacts 8
    leaf4790Certificate.logOnePlusV leaf4790InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4790InputLogOnePlusV_eq }

private noncomputable def leaf4790Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4790InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4790LowerChecked :
    lowerCheck 24 leaf4790Box leaf4790Inputs = true := by
  rfl'

private theorem leaf4790CoversExact : CoversExact 8
    leaf4790Box leaf4790Certificate leaf4790InnerLog leaf4790Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4790RoundedFacts (by rfl)

private theorem leaf4790FlatSound : Sound leaf4790Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4790CertificateValid
    leaf4790InnerLogValid leaf4790CoversExact leaf4790LowerChecked

private noncomputable def leaf4791Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4791Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084156416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2115929393/1073741824) }, upper := { exponent := 0, mantissa := (4073/2048) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168681231/16168312832) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf4791InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4791LocalValidity :
    LeafFacts leaf4791Box leaf4791Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4791Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084156416) }) = true
      norm_num [leaf4791Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4791CertificateValid :
    WideCertificateValid leaf4791Box leaf4791Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi280ValidityFacts
    leaf4791LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4791CoverageChecked :
    coverageCheck (innerAD leaf4791Box) leaf4791InnerLog = true := by
  rfl'

private theorem leaf4791InnerLogValid :
    leaf4791InnerLog.Valid 8 (innerAD leaf4791Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4791CoverageChecked

private noncomputable def leaf4791InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4791InputLogOnePlusV_eq :
    leaf4791InputLogOnePlusV = outerEnclosure 24
      (leaf4791Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4791RoundedFacts : LeafRoundedFacts 8
    leaf4791Certificate.logOnePlusV leaf4791InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4791InputLogOnePlusV_eq }

private noncomputable def leaf4791Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi280InputQChi innerPair108Input
    leaf4791InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4791LowerChecked :
    lowerCheck 24 leaf4791Box leaf4791Inputs = true := by
  rfl'

private theorem leaf4791CoversExact : CoversExact 8
    leaf4791Box leaf4791Certificate leaf4791InnerLog leaf4791Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi280RoundedFacts
    innerPair108RoundedFacts leaf4791RoundedFacts (by rfl)

private theorem leaf4791FlatSound : Sound leaf4791Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4791CertificateValid
    leaf4791InnerLogValid leaf4791CoversExact leaf4791LowerChecked

private noncomputable def leaf4792Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4792Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715311104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2120582163/1073741824) }, upper := { exponent := 0, mantissa := (2041/1024) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432723455/137430622208) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf4792InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4792LocalValidity :
    LeafFacts leaf4792Box leaf4792Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4792Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715311104) }) = true
      norm_num [leaf4792Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4792CertificateValid :
    WideCertificateValid leaf4792Box leaf4792Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi280ValidityFacts
    leaf4792LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4792CoverageChecked :
    coverageCheck (innerAD leaf4792Box) leaf4792InnerLog = true := by
  rfl'

private theorem leaf4792InnerLogValid :
    leaf4792InnerLog.Valid 8 (innerAD leaf4792Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4792CoverageChecked

private noncomputable def leaf4792InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4792InputLogOnePlusV_eq :
    leaf4792InputLogOnePlusV = outerEnclosure 24
      (leaf4792Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4792RoundedFacts : LeafRoundedFacts 8
    leaf4792Certificate.logOnePlusV leaf4792InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4792InputLogOnePlusV_eq }

private noncomputable def leaf4792Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi280InputQChi innerPair108Input
    leaf4792InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4792LowerChecked :
    lowerCheck 24 leaf4792Box leaf4792Inputs = true := by
  rfl'

private theorem leaf4792CoversExact : CoversExact 8
    leaf4792Box leaf4792Certificate leaf4792InnerLog leaf4792Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi280RoundedFacts
    innerPair108RoundedFacts leaf4792RoundedFacts (by rfl)

private theorem leaf4792FlatSound : Sound leaf4792Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4792CertificateValid
    leaf4792InnerLogValid leaf4792CoversExact leaf4792LowerChecked

private noncomputable def leaf4793Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4793Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090025984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2110424703/1073741824) }, upper := { exponent := 0, mantissa := (32501/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180282349/10180051968) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4793InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4793LocalValidity :
    LeafFacts leaf4793Box leaf4793Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4793Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090025984) }) = true
      norm_num [leaf4793Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4793CertificateValid :
    WideCertificateValid leaf4793Box leaf4793Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi279ValidityFacts
    leaf4793LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4793CoverageChecked :
    coverageCheck (innerAD leaf4793Box) leaf4793InnerLog = true := by
  rfl'

private theorem leaf4793InnerLogValid :
    leaf4793InnerLog.Valid 8 (innerAD leaf4793Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4793CoverageChecked

private noncomputable def leaf4793InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4793InputLogOnePlusV_eq :
    leaf4793InputLogOnePlusV = outerEnclosure 24
      (leaf4793Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4793RoundedFacts : LeafRoundedFacts 8
    leaf4793Certificate.logOnePlusV leaf4793InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4793InputLogOnePlusV_eq }

private noncomputable def leaf4793Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4793InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4793LowerChecked :
    lowerCheck 24 leaf4793Box leaf4793Inputs = true := by
  rfl'

private theorem leaf4793CoversExact : CoversExact 8
    leaf4793Box leaf4793Certificate leaf4793InnerLog leaf4793Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4793RoundedFacts (by rfl)

private theorem leaf4793FlatSound : Sound leaf4793Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4793CertificateValid
    leaf4793InnerLogValid leaf4793CoversExact leaf4793LowerChecked

private noncomputable def leaf4794Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4794Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430665216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2115011941/1073741824) }, upper := { exponent := 0, mantissa := (8143/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867587071/274861330432) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4794InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4794LocalValidity :
    LeafFacts leaf4794Box leaf4794Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4794Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430665216) }) = true
      norm_num [leaf4794Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4794CertificateValid :
    WideCertificateValid leaf4794Box leaf4794Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi279ValidityFacts
    leaf4794LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4794CoverageChecked :
    coverageCheck (innerAD leaf4794Box) leaf4794InnerLog = true := by
  rfl'

private theorem leaf4794InnerLogValid :
    leaf4794InnerLog.Valid 8 (innerAD leaf4794Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4794CoverageChecked

private noncomputable def leaf4794InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4794InputLogOnePlusV_eq :
    leaf4794InputLogOnePlusV = outerEnclosure 24
      (leaf4794Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4794RoundedFacts : LeafRoundedFacts 8
    leaf4794Certificate.logOnePlusV leaf4794InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4794InputLogOnePlusV_eq }

private noncomputable def leaf4794Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4794InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4794LowerChecked :
    lowerCheck 24 leaf4794Box leaf4794Inputs = true := by
  rfl'

private theorem leaf4794CoversExact : CoversExact 8
    leaf4794Box leaf4794Certificate leaf4794InnerLog leaf4794Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4794RoundedFacts (by rfl)

private theorem leaf4794FlatSound : Sound leaf4794Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4794CertificateValid
    leaf4794InnerLogValid leaf4794CoversExact leaf4794LowerChecked

private noncomputable def leaf4795Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4795Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715292672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2125234933/1073741824) }, upper := { exponent := 0, mantissa := (4091/2048) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432705023/137430585344) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf4795InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4795LocalValidity :
    LeafFacts leaf4795Box leaf4795Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4795Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715292672) }) = true
      norm_num [leaf4795Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4795CertificateValid :
    WideCertificateValid leaf4795Box leaf4795Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi280ValidityFacts
    leaf4795LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4795CoverageChecked :
    coverageCheck (innerAD leaf4795Box) leaf4795InnerLog = true := by
  rfl'

private theorem leaf4795InnerLogValid :
    leaf4795InnerLog.Valid 8 (innerAD leaf4795Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4795CoverageChecked

private noncomputable def leaf4795InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4795InputLogOnePlusV_eq :
    leaf4795InputLogOnePlusV = outerEnclosure 24
      (leaf4795Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4795RoundedFacts : LeafRoundedFacts 8
    leaf4795Certificate.logOnePlusV leaf4795InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4795InputLogOnePlusV_eq }

private noncomputable def leaf4795Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi280InputQChi innerPair108Input
    leaf4795InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4795LowerChecked :
    lowerCheck 24 leaf4795Box leaf4795Inputs = true := by
  rfl'

private theorem leaf4795CoversExact : CoversExact 8
    leaf4795Box leaf4795Certificate leaf4795InnerLog leaf4795Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi280RoundedFacts
    innerPair108RoundedFacts leaf4795RoundedFacts (by rfl)

private theorem leaf4795FlatSound : Sound leaf4795Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4795CertificateValid
    leaf4795InnerLogValid leaf4795CoversExact leaf4795LowerChecked

private noncomputable def leaf4796Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4796Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715274240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2129887703/1073741824) }, upper := { exponent := 1, mantissa := (1025/1024) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432686591/137430548480) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf4796InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4796LocalValidity :
    LeafFacts leaf4796Box leaf4796Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4796Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715274240) }) = true
      norm_num [leaf4796Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4796CertificateValid :
    WideCertificateValid leaf4796Box leaf4796Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi280ValidityFacts
    leaf4796LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4796CoverageChecked :
    coverageCheck (innerAD leaf4796Box) leaf4796InnerLog = true := by
  rfl'

private theorem leaf4796InnerLogValid :
    leaf4796InnerLog.Valid 8 (innerAD leaf4796Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4796CoverageChecked

private noncomputable def leaf4796InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4796InputLogOnePlusV_eq :
    leaf4796InputLogOnePlusV = outerEnclosure 24
      (leaf4796Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4796RoundedFacts : LeafRoundedFacts 8
    leaf4796Certificate.logOnePlusV leaf4796InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4796InputLogOnePlusV_eq }

private noncomputable def leaf4796Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi280InputQChi innerPair110Input
    leaf4796InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4796LowerChecked :
    lowerCheck 24 leaf4796Box leaf4796Inputs = true := by
  rfl'

private theorem leaf4796CoversExact : CoversExact 8
    leaf4796Box leaf4796Certificate leaf4796InnerLog leaf4796Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi280RoundedFacts
    innerPair110RoundedFacts leaf4796RoundedFacts (by rfl)

private theorem leaf4796FlatSound : Sound leaf4796Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4796CertificateValid
    leaf4796InnerLogValid leaf4796CoversExact leaf4796LowerChecked

private noncomputable def leaf4797Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4797Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486172672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2089716591/1073741824) }, upper := { exponent := 0, mantissa := (32185/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973557043/54972345344) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4797InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4797LocalValidity :
    LeafFacts leaf4797Box leaf4797Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4797Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486172672) }) = true
      norm_num [leaf4797Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4797CertificateValid :
    WideCertificateValid leaf4797Box leaf4797Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi257ValidityFacts
    leaf4797LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4797CoverageChecked :
    coverageCheck (innerAD leaf4797Box) leaf4797InnerLog = true := by
  rfl'

private theorem leaf4797InnerLogValid :
    leaf4797InnerLog.Valid 8 (innerAD leaf4797Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4797CoverageChecked

private noncomputable def leaf4797InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4797InputLogOnePlusV_eq :
    leaf4797InputLogOnePlusV = outerEnclosure 24
      (leaf4797Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4797RoundedFacts : LeafRoundedFacts 8
    leaf4797Certificate.logOnePlusV leaf4797InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4797InputLogOnePlusV_eq }

private noncomputable def leaf4797Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4797InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4797LowerChecked :
    lowerCheck 24 leaf4797Box leaf4797Inputs = true := by
  rfl'

private theorem leaf4797CoversExact : CoversExact 8
    leaf4797Box leaf4797Certificate leaf4797InnerLog leaf4797Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4797RoundedFacts (by rfl)

private theorem leaf4797FlatSound : Sound leaf4797Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4797CertificateValid
    leaf4797InnerLogValid leaf4797CoversExact leaf4797LowerChecked

private noncomputable def leaf4798Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4798Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430828032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2094172765/1073741824) }, upper := { exponent := 0, mantissa := (16127/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867749887/274861656064) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4798InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4798LocalValidity :
    LeafFacts leaf4798Box leaf4798Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4798Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430828032) }) = true
      norm_num [leaf4798Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4798CertificateValid :
    WideCertificateValid leaf4798Box leaf4798Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi257ValidityFacts
    leaf4798LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4798CoverageChecked :
    coverageCheck (innerAD leaf4798Box) leaf4798InnerLog = true := by
  rfl'

private theorem leaf4798InnerLogValid :
    leaf4798InnerLog.Valid 8 (innerAD leaf4798Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4798CoverageChecked

private noncomputable def leaf4798InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4798InputLogOnePlusV_eq :
    leaf4798InputLogOnePlusV = outerEnclosure 24
      (leaf4798Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4798RoundedFacts : LeafRoundedFacts 8
    leaf4798Certificate.logOnePlusV leaf4798InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4798InputLogOnePlusV_eq }

private noncomputable def leaf4798Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4798InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4798LowerChecked :
    lowerCheck 24 leaf4798Box leaf4798Inputs = true := by
  rfl'

private theorem leaf4798CoversExact : CoversExact 8
    leaf4798Box leaf4798Certificate leaf4798InnerLog leaf4798Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4798RoundedFacts (by rfl)

private theorem leaf4798FlatSound : Sound leaf4798Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4798CertificateValid
    leaf4798InnerLogValid leaf4798CoversExact leaf4798LowerChecked

private noncomputable def leaf4799Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4799Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2694841605/2694720512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2104657885/1073741824) }, upper := { exponent := 0, mantissa := (16207/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5389562117/5389441024) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4799InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4799LocalValidity :
    LeafFacts leaf4799Box leaf4799Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4799Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2694841605/2694720512) }) = true
      norm_num [leaf4799Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4799CertificateValid :
    WideCertificateValid leaf4799Box leaf4799Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi258ValidityFacts
    leaf4799LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4799CoverageChecked :
    coverageCheck (innerAD leaf4799Box) leaf4799InnerLog = true := by
  rfl'

private theorem leaf4799InnerLogValid :
    leaf4799InnerLog.Valid 8 (innerAD leaf4799Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4799CoverageChecked

private noncomputable def leaf4799InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4799InputLogOnePlusV_eq :
    leaf4799InputLogOnePlusV = outerEnclosure 24
      (leaf4799Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4799RoundedFacts : LeafRoundedFacts 8
    leaf4799Certificate.logOnePlusV leaf4799InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4799InputLogOnePlusV_eq }

private noncomputable def leaf4799Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4799InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4799LowerChecked :
    lowerCheck 24 leaf4799Box leaf4799Inputs = true := by
  rfl'

private theorem leaf4799CoversExact : CoversExact 8
    leaf4799Box leaf4799Certificate leaf4799InnerLog leaf4799Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4799RoundedFacts (by rfl)

private theorem leaf4799FlatSound : Sound leaf4799Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4799CertificateValid
    leaf4799InnerLogValid leaf4799CoversExact leaf4799LowerChecked

private noncomputable def leaf4800Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4800Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430710272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2109179591/1073741824) }, upper := { exponent := 0, mantissa := (8121/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867632127/274861420544) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4800InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4800LocalValidity :
    LeafFacts leaf4800Box leaf4800Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4800Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430710272) }) = true
      norm_num [leaf4800Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4800CertificateValid :
    WideCertificateValid leaf4800Box leaf4800Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi258ValidityFacts
    leaf4800LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4800CoverageChecked :
    coverageCheck (innerAD leaf4800Box) leaf4800InnerLog = true := by
  rfl'

private theorem leaf4800InnerLogValid :
    leaf4800InnerLog.Valid 8 (innerAD leaf4800Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4800CoverageChecked

private noncomputable def leaf4800InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4800InputLogOnePlusV_eq :
    leaf4800InputLogOnePlusV = outerEnclosure 24
      (leaf4800Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4800RoundedFacts : LeafRoundedFacts 8
    leaf4800Certificate.logOnePlusV leaf4800InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4800InputLogOnePlusV_eq }

private noncomputable def leaf4800Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4800InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4800LowerChecked :
    lowerCheck 24 leaf4800Box leaf4800Inputs = true := by
  rfl'

private theorem leaf4800CoversExact : CoversExact 8
    leaf4800Box leaf4800Certificate leaf4800InnerLog leaf4800Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4800RoundedFacts (by rfl)

private theorem leaf4800FlatSound : Sound leaf4800Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4800CertificateValid
    leaf4800InnerLogValid leaf4800CoversExact leaf4800LowerChecked

private noncomputable def leaf4801Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4801Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430792704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2098628939/1073741824) }, upper := { exponent := 0, mantissa := (32323/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867714559/274861585408) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4801InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4801LocalValidity :
    LeafFacts leaf4801Box leaf4801Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4801Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430792704) }) = true
      norm_num [leaf4801Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4801CertificateValid :
    WideCertificateValid leaf4801Box leaf4801Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi257ValidityFacts
    leaf4801LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4801CoverageChecked :
    coverageCheck (innerAD leaf4801Box) leaf4801InnerLog = true := by
  rfl'

private theorem leaf4801InnerLogValid :
    leaf4801InnerLog.Valid 8 (innerAD leaf4801Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4801CoverageChecked

private noncomputable def leaf4801InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4801InputLogOnePlusV_eq :
    leaf4801InputLogOnePlusV = outerEnclosure 24
      (leaf4801Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4801RoundedFacts : LeafRoundedFacts 8
    leaf4801Certificate.logOnePlusV leaf4801InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4801InputLogOnePlusV_eq }

private noncomputable def leaf4801Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4801InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4801LowerChecked :
    lowerCheck 24 leaf4801Box leaf4801Inputs = true := by
  rfl'

private theorem leaf4801CoversExact : CoversExact 8
    leaf4801Box leaf4801Certificate leaf4801InnerLog leaf4801Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4801RoundedFacts (by rfl)

private theorem leaf4801FlatSound : Sound leaf4801Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4801CertificateValid
    leaf4801InnerLogValid leaf4801CoversExact leaf4801LowerChecked

private noncomputable def leaf4802Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4802Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430757376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2103085113/1073741824) }, upper := { exponent := 0, mantissa := (4049/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867679231/274861514752) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4802InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4802LocalValidity :
    LeafFacts leaf4802Box leaf4802Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4802Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430757376) }) = true
      norm_num [leaf4802Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4802CertificateValid :
    WideCertificateValid leaf4802Box leaf4802Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi257ValidityFacts
    leaf4802LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4802CoverageChecked :
    coverageCheck (innerAD leaf4802Box) leaf4802InnerLog = true := by
  rfl'

private theorem leaf4802InnerLogValid :
    leaf4802InnerLog.Valid 8 (innerAD leaf4802Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4802CoverageChecked

private noncomputable def leaf4802InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4802InputLogOnePlusV_eq :
    leaf4802InputLogOnePlusV = outerEnclosure 24
      (leaf4802Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4802RoundedFacts : LeafRoundedFacts 8
    leaf4802Certificate.logOnePlusV leaf4802InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4802InputLogOnePlusV_eq }

private noncomputable def leaf4802Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi257InputQChi innerPair108Input
    leaf4802InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4802LowerChecked :
    lowerCheck 24 leaf4802Box leaf4802Inputs = true := by
  rfl'

private theorem leaf4802CoversExact : CoversExact 8
    leaf4802Box leaf4802Certificate leaf4802InnerLog leaf4802Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi257RoundedFacts
    innerPair108RoundedFacts leaf4802RoundedFacts (by rfl)

private theorem leaf4802FlatSound : Sound leaf4802Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4802CertificateValid
    leaf4802InnerLogValid leaf4802CoversExact leaf4802LowerChecked

private noncomputable def leaf4803Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4803Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430674432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2113701297/1073741824) }, upper := { exponent := 0, mantissa := (16277/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867596287/274861348864) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4803InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4803LocalValidity :
    LeafFacts leaf4803Box leaf4803Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4803Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430674432) }) = true
      norm_num [leaf4803Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4803CertificateValid :
    WideCertificateValid leaf4803Box leaf4803Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi258ValidityFacts
    leaf4803LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4803CoverageChecked :
    coverageCheck (innerAD leaf4803Box) leaf4803InnerLog = true := by
  rfl'

private theorem leaf4803InnerLogValid :
    leaf4803InnerLog.Valid 8 (innerAD leaf4803Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4803CoverageChecked

private noncomputable def leaf4803InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4803InputLogOnePlusV_eq :
    leaf4803InputLogOnePlusV = outerEnclosure 24
      (leaf4803Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4803RoundedFacts : LeafRoundedFacts 8
    leaf4803Certificate.logOnePlusV leaf4803InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4803InputLogOnePlusV_eq }

private noncomputable def leaf4803Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4803InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4803LowerChecked :
    lowerCheck 24 leaf4803Box leaf4803Inputs = true := by
  rfl'

private theorem leaf4803CoversExact : CoversExact 8
    leaf4803Box leaf4803Certificate leaf4803InnerLog leaf4803Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4803RoundedFacts (by rfl)

private theorem leaf4803FlatSound : Sound leaf4803Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4803CertificateValid
    leaf4803InnerLogValid leaf4803CoversExact leaf4803LowerChecked

private noncomputable def leaf4804Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4804Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810212864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2118223003/1073741824) }, upper := { exponent := 0, mantissa := (2039/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622520149/91620425728) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4804InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4804LocalValidity :
    LeafFacts leaf4804Box leaf4804Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4804Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810212864) }) = true
      norm_num [leaf4804Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4804CertificateValid :
    WideCertificateValid leaf4804Box leaf4804Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi258ValidityFacts
    leaf4804LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4804CoverageChecked :
    coverageCheck (innerAD leaf4804Box) leaf4804InnerLog = true := by
  rfl'

private theorem leaf4804InnerLogValid :
    leaf4804InnerLog.Valid 8 (innerAD leaf4804Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4804CoverageChecked

private noncomputable def leaf4804InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4804InputLogOnePlusV_eq :
    leaf4804InputLogOnePlusV = outerEnclosure 24
      (leaf4804Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4804RoundedFacts : LeafRoundedFacts 8
    leaf4804Certificate.logOnePlusV leaf4804InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4804InputLogOnePlusV_eq }

private noncomputable def leaf4804Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4804InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4804LowerChecked :
    lowerCheck 24 leaf4804Box leaf4804Inputs = true := by
  rfl'

private theorem leaf4804CoversExact : CoversExact 8
    leaf4804Box leaf4804Certificate leaf4804InnerLog leaf4804Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4804RoundedFacts (by rfl)

private theorem leaf4804FlatSound : Sound leaf4804Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4804CertificateValid
    leaf4804InnerLogValid leaf4804CoversExact leaf4804LowerChecked

private noncomputable def leaf4805Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4805Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715314432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2119599179/1073741824) }, upper := { exponent := 0, mantissa := (32643/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432726783/137430628864) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4805InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4805LocalValidity :
    LeafFacts leaf4805Box leaf4805Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4805Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715314432) }) = true
      norm_num [leaf4805Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4805CertificateValid :
    WideCertificateValid leaf4805Box leaf4805Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi279ValidityFacts
    leaf4805LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4805CoverageChecked :
    coverageCheck (innerAD leaf4805Box) leaf4805InnerLog = true := by
  rfl'

private theorem leaf4805InnerLogValid :
    leaf4805InnerLog.Valid 8 (innerAD leaf4805Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4805CoverageChecked

private noncomputable def leaf4805InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4805InputLogOnePlusV_eq :
    leaf4805InputLogOnePlusV = outerEnclosure 24
      (leaf4805Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4805RoundedFacts : LeafRoundedFacts 8
    leaf4805Certificate.logOnePlusV leaf4805InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4805InputLogOnePlusV_eq }

private noncomputable def leaf4805Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4805InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4805LowerChecked :
    lowerCheck 24 leaf4805Box leaf4805Inputs = true := by
  rfl'

private theorem leaf4805CoversExact : CoversExact 8
    leaf4805Box leaf4805Certificate leaf4805InnerLog leaf4805Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4805RoundedFacts (by rfl)

private theorem leaf4805FlatSound : Sound leaf4805Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4805CertificateValid
    leaf4805InnerLogValid leaf4805CoversExact leaf4805LowerChecked

private noncomputable def leaf4806Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4806Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22905098752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2124186417/1073741824) }, upper := { exponent := 0, mantissa := (16357/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810902869/45810197504) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4806InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4806LocalValidity :
    LeafFacts leaf4806Box leaf4806Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4806Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22905098752) }) = true
      norm_num [leaf4806Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4806CertificateValid :
    WideCertificateValid leaf4806Box leaf4806Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi279ValidityFacts
    leaf4806LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4806CoverageChecked :
    coverageCheck (innerAD leaf4806Box) leaf4806InnerLog = true := by
  rfl'

private theorem leaf4806InnerLogValid :
    leaf4806InnerLog.Valid 8 (innerAD leaf4806Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4806CoverageChecked

private noncomputable def leaf4806InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4806InputLogOnePlusV_eq :
    leaf4806InputLogOnePlusV = outerEnclosure 24
      (leaf4806Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4806RoundedFacts : LeafRoundedFacts 8
    leaf4806Certificate.logOnePlusV leaf4806InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4806InputLogOnePlusV_eq }

private noncomputable def leaf4806Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4806InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4806LowerChecked :
    lowerCheck 24 leaf4806Box leaf4806Inputs = true := by
  rfl'

private theorem leaf4806CoversExact : CoversExact 8
    leaf4806Box leaf4806Certificate leaf4806InnerLog leaf4806Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4806RoundedFacts (by rfl)

private theorem leaf4806FlatSound : Sound leaf4806Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4806CertificateValid
    leaf4806InnerLogValid leaf4806CoversExact leaf4806LowerChecked

private noncomputable def leaf4807Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4807Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715255808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2134540473/1073741824) }, upper := { exponent := 1, mantissa := (4109/4096) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432668159/137430511616) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf4807InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4807LocalValidity :
    LeafFacts leaf4807Box leaf4807Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4807Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715255808) }) = true
      norm_num [leaf4807Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4807CertificateValid :
    WideCertificateValid leaf4807Box leaf4807Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi280ValidityFacts
    leaf4807LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4807CoverageChecked :
    coverageCheck (innerAD leaf4807Box) leaf4807InnerLog = true := by
  rfl'

private theorem leaf4807InnerLogValid :
    leaf4807InnerLog.Valid 8 (innerAD leaf4807Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4807CoverageChecked

private noncomputable def leaf4807InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4807InputLogOnePlusV_eq :
    leaf4807InputLogOnePlusV = outerEnclosure 24
      (leaf4807Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4807RoundedFacts : LeafRoundedFacts 8
    leaf4807Certificate.logOnePlusV leaf4807InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4807InputLogOnePlusV_eq }

private noncomputable def leaf4807Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi280InputQChi innerPair110Input
    leaf4807InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4807LowerChecked :
    lowerCheck 24 leaf4807Box leaf4807Inputs = true := by
  rfl'

private theorem leaf4807CoversExact : CoversExact 8
    leaf4807Box leaf4807Certificate leaf4807InnerLog leaf4807Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi280RoundedFacts
    innerPair110RoundedFacts leaf4807RoundedFacts (by rfl)

private theorem leaf4807FlatSound : Sound leaf4807Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4807CertificateValid
    leaf4807InnerLogValid leaf4807CoversExact leaf4807LowerChecked

private noncomputable def leaf4808Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4808Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715237376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2139193243/1073741824) }, upper := { exponent := 1, mantissa := (2059/2048) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432649727/137430474752) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf4808InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4808LocalValidity :
    LeafFacts leaf4808Box leaf4808Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4808Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715237376) }) = true
      norm_num [leaf4808Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4808CertificateValid :
    WideCertificateValid leaf4808Box leaf4808Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi280ValidityFacts
    leaf4808LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4808CoverageChecked :
    coverageCheck (innerAD leaf4808Box) leaf4808InnerLog = true := by
  rfl'

private theorem leaf4808InnerLogValid :
    leaf4808InnerLog.Valid 8 (innerAD leaf4808Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4808CoverageChecked

private noncomputable def leaf4808InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4808InputLogOnePlusV_eq :
    leaf4808InputLogOnePlusV = outerEnclosure 24
      (leaf4808Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4808RoundedFacts : LeafRoundedFacts 8
    leaf4808Certificate.logOnePlusV leaf4808InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4808InputLogOnePlusV_eq }

private noncomputable def leaf4808Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi280InputQChi innerPair110Input
    leaf4808InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4808LowerChecked :
    lowerCheck 24 leaf4808Box leaf4808Inputs = true := by
  rfl'

private theorem leaf4808CoversExact : CoversExact 8
    leaf4808Box leaf4808Certificate leaf4808InnerLog leaf4808Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi280RoundedFacts
    innerPair110RoundedFacts leaf4808RoundedFacts (by rfl)

private theorem leaf4808FlatSound : Sound leaf4808Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4808CertificateValid
    leaf4808InnerLogValid leaf4808CoversExact leaf4808LowerChecked

private noncomputable def leaf4809Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4809Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715278080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2128773655/1073741824) }, upper := { exponent := 1, mantissa := (32785/32768) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432690431/137430556160) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4809InnerLog : WideLogData :=
  innerPair321Data

set_option maxRecDepth 1000000 in
private theorem leaf4809LocalValidity :
    LeafFacts leaf4809Box leaf4809Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4809Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715278080) }) = true
      norm_num [leaf4809Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4809CertificateValid :
    WideCertificateValid leaf4809Box leaf4809Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi279ValidityFacts
    leaf4809LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4809CoverageChecked :
    coverageCheck (innerAD leaf4809Box) leaf4809InnerLog = true := by
  rfl'

private theorem leaf4809InnerLogValid :
    leaf4809InnerLog.Valid 8 (innerAD leaf4809Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint283PositiveFacts.valid leaf4809CoverageChecked

private noncomputable def leaf4809InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4809InputLogOnePlusV_eq :
    leaf4809InputLogOnePlusV = outerEnclosure 24
      (leaf4809Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4809RoundedFacts : LeafRoundedFacts 8
    leaf4809Certificate.logOnePlusV leaf4809InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4809InputLogOnePlusV_eq }

private noncomputable def leaf4809Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi279InputQChi innerPair321Input
    leaf4809InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4809LowerChecked :
    lowerCheck 24 leaf4809Box leaf4809Inputs = true := by
  rfl'

private theorem leaf4809CoversExact : CoversExact 8
    leaf4809Box leaf4809Certificate leaf4809InnerLog leaf4809Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi279RoundedFacts
    innerPair321RoundedFacts leaf4809RoundedFacts (by rfl)

private theorem leaf4809FlatSound : Sound leaf4809Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4809CertificateValid
    leaf4809InnerLogValid leaf4809CoversExact leaf4809LowerChecked

private noncomputable def leaf4810Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4810Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715259904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2133360893/1073741824) }, upper := { exponent := 1, mantissa := (4107/4096) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432672255/137430519808) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4810InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4810LocalValidity :
    LeafFacts leaf4810Box leaf4810Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4810Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715259904) }) = true
      norm_num [leaf4810Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4810CertificateValid :
    WideCertificateValid leaf4810Box leaf4810Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi279ValidityFacts
    leaf4810LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4810CoverageChecked :
    coverageCheck (innerAD leaf4810Box) leaf4810InnerLog = true := by
  rfl'

private theorem leaf4810InnerLogValid :
    leaf4810InnerLog.Valid 8 (innerAD leaf4810Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4810CoverageChecked

private noncomputable def leaf4810InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4810InputLogOnePlusV_eq :
    leaf4810InputLogOnePlusV = outerEnclosure 24
      (leaf4810Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4810RoundedFacts : LeafRoundedFacts 8
    leaf4810Certificate.logOnePlusV leaf4810InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4810InputLogOnePlusV_eq }

private noncomputable def leaf4810Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi279InputQChi innerPair110Input
    leaf4810InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4810LowerChecked :
    lowerCheck 24 leaf4810Box leaf4810Inputs = true := by
  rfl'

private theorem leaf4810CoversExact : CoversExact 8
    leaf4810Box leaf4810Certificate leaf4810InnerLog leaf4810Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi279RoundedFacts
    innerPair110RoundedFacts leaf4810RoundedFacts (by rfl)

private theorem leaf4810FlatSound : Sound leaf4810Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4810CertificateValid
    leaf4810InnerLogValid leaf4810CoversExact leaf4810LowerChecked

private noncomputable def leaf4811Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4811Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715218944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2143846013/1073741824) }, upper := { exponent := 1, mantissa := (4127/4096) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432631295/137430437888) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf4811InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf4811LocalValidity :
    LeafFacts leaf4811Box leaf4811Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4811Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715218944) }) = true
      norm_num [leaf4811Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4811CertificateValid :
    WideCertificateValid leaf4811Box leaf4811Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi280ValidityFacts
    leaf4811LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4811CoverageChecked :
    coverageCheck (innerAD leaf4811Box) leaf4811InnerLog = true := by
  rfl'

private theorem leaf4811InnerLogValid :
    leaf4811InnerLog.Valid 8 (innerAD leaf4811Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf4811CoverageChecked

private noncomputable def leaf4811InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4811InputLogOnePlusV_eq :
    leaf4811InputLogOnePlusV = outerEnclosure 24
      (leaf4811Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4811RoundedFacts : LeafRoundedFacts 8
    leaf4811Certificate.logOnePlusV leaf4811InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4811InputLogOnePlusV_eq }

private noncomputable def leaf4811Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi280InputQChi innerPair110Input
    leaf4811InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4811LowerChecked :
    lowerCheck 24 leaf4811Box leaf4811Inputs = true := by
  rfl'

private theorem leaf4811CoversExact : CoversExact 8
    leaf4811Box leaf4811Certificate leaf4811InnerLog leaf4811Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi280RoundedFacts
    innerPair110RoundedFacts leaf4811RoundedFacts (by rfl)

private theorem leaf4811FlatSound : Sound leaf4811Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4811CertificateValid
    leaf4811InnerLogValid leaf4811CoversExact leaf4811LowerChecked

private noncomputable def leaf4812Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4812Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816457216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2148498783/2147483648) }, upper := { exponent := 1, mantissa := (517/512) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633230409/19632914432) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf4812InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4812LocalValidity :
    LeafFacts leaf4812Box leaf4812Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4812Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816457216) }) = true
      norm_num [leaf4812Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4812CertificateValid :
    WideCertificateValid leaf4812Box leaf4812Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi280ValidityFacts
    leaf4812LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4812CoverageChecked :
    coverageCheck (innerAD leaf4812Box) leaf4812InnerLog = true := by
  rfl'

private theorem leaf4812InnerLogValid :
    leaf4812InnerLog.Valid 8 (innerAD leaf4812Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4812CoverageChecked

private noncomputable def leaf4812InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4812InputLogOnePlusV_eq :
    leaf4812InputLogOnePlusV = outerEnclosure 24
      (leaf4812Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4812RoundedFacts : LeafRoundedFacts 8
    leaf4812Certificate.logOnePlusV leaf4812InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4812InputLogOnePlusV_eq }

private noncomputable def leaf4812Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi280InputQChi innerPair116Input
    leaf4812InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4812LowerChecked :
    lowerCheck 24 leaf4812Box leaf4812Inputs = true := by
  rfl'

private theorem leaf4812CoversExact : CoversExact 8
    leaf4812Box leaf4812Certificate leaf4812InnerLog leaf4812Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi280RoundedFacts
    innerPair116RoundedFacts leaf4812RoundedFacts (by rfl)

private theorem leaf4812FlatSound : Sound leaf4812Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4812CertificateValid
    leaf4812InnerLogValid leaf4812CoversExact leaf4812LowerChecked

private noncomputable def component98Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node0_sound : Sound component98Node0Box :=
  sound_of_literal_split component98Node0Box leaf4749Box leaf4750Box
    .k (225/64) (by rfl) (by rfl)
    leaf4749FlatSound leaf4750FlatSound

private noncomputable def component98Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node1_sound : Sound component98Node1Box :=
  sound_of_literal_split component98Node1Box leaf4751Box leaf4752Box
    .k (225/64) (by rfl) (by rfl)
    leaf4751FlatSound leaf4752FlatSound

private noncomputable def component98Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node2_sound : Sound component98Node2Box :=
  sound_of_literal_split component98Node2Box component98Node0Box component98Node1Box
    .chi (65/256) (by rfl) (by rfl)
    component98Node0_sound component98Node1_sound

private noncomputable def component98Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node3_sound : Sound component98Node3Box :=
  sound_of_literal_split component98Node3Box leaf4753Box leaf4754Box
    .k (227/64) (by rfl) (by rfl)
    leaf4753FlatSound leaf4754FlatSound

private noncomputable def component98Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node4_sound : Sound component98Node4Box :=
  sound_of_literal_split component98Node4Box leaf4755Box leaf4756Box
    .k (227/64) (by rfl) (by rfl)
    leaf4755FlatSound leaf4756FlatSound

private noncomputable def component98Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node5_sound : Sound component98Node5Box :=
  sound_of_literal_split component98Node5Box component98Node3Box component98Node4Box
    .chi (65/256) (by rfl) (by rfl)
    component98Node3_sound component98Node4_sound

private noncomputable def component98Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node6_sound : Sound component98Node6Box :=
  sound_of_literal_split component98Node6Box component98Node2Box component98Node5Box
    .k (113/32) (by rfl) (by rfl)
    component98Node2_sound component98Node5_sound

private noncomputable def component98Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node7_sound : Sound component98Node7Box :=
  sound_of_literal_split component98Node7Box leaf4757Box leaf4758Box
    .k (225/64) (by rfl) (by rfl)
    leaf4757FlatSound leaf4758FlatSound

private noncomputable def component98Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node8_sound : Sound component98Node8Box :=
  sound_of_literal_split component98Node8Box leaf4759Box leaf4760Box
    .k (225/64) (by rfl) (by rfl)
    leaf4759FlatSound leaf4760FlatSound

private noncomputable def component98Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node9_sound : Sound component98Node9Box :=
  sound_of_literal_split component98Node9Box component98Node7Box component98Node8Box
    .chi (67/256) (by rfl) (by rfl)
    component98Node7_sound component98Node8_sound

private noncomputable def component98Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node10_sound : Sound component98Node10Box :=
  sound_of_literal_split component98Node10Box leaf4761Box leaf4762Box
    .k (227/64) (by rfl) (by rfl)
    leaf4761FlatSound leaf4762FlatSound

private noncomputable def component98Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node11_sound : Sound component98Node11Box :=
  sound_of_literal_split component98Node11Box leaf4763Box leaf4764Box
    .k (227/64) (by rfl) (by rfl)
    leaf4763FlatSound leaf4764FlatSound

private noncomputable def component98Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node12_sound : Sound component98Node12Box :=
  sound_of_literal_split component98Node12Box component98Node10Box component98Node11Box
    .chi (67/256) (by rfl) (by rfl)
    component98Node10_sound component98Node11_sound

private noncomputable def component98Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node13_sound : Sound component98Node13Box :=
  sound_of_literal_split component98Node13Box component98Node9Box component98Node12Box
    .k (113/32) (by rfl) (by rfl)
    component98Node9_sound component98Node12_sound

private noncomputable def component98Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node14_sound : Sound component98Node14Box :=
  sound_of_literal_split component98Node14Box component98Node6Box component98Node13Box
    .chi (33/128) (by rfl) (by rfl)
    component98Node6_sound component98Node13_sound

private noncomputable def component98Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node15_sound : Sound component98Node15Box :=
  sound_of_literal_split component98Node15Box leaf4765Box leaf4766Box
    .k (229/64) (by rfl) (by rfl)
    leaf4765FlatSound leaf4766FlatSound

private noncomputable def component98Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node16_sound : Sound component98Node16Box :=
  sound_of_literal_split component98Node16Box leaf4767Box leaf4768Box
    .k (229/64) (by rfl) (by rfl)
    leaf4767FlatSound leaf4768FlatSound

private noncomputable def component98Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node17_sound : Sound component98Node17Box :=
  sound_of_literal_split component98Node17Box component98Node15Box component98Node16Box
    .chi (65/256) (by rfl) (by rfl)
    component98Node15_sound component98Node16_sound

private noncomputable def component98Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node18_sound : Sound component98Node18Box :=
  sound_of_literal_split component98Node18Box leaf4769Box leaf4770Box
    .k (231/64) (by rfl) (by rfl)
    leaf4769FlatSound leaf4770FlatSound

private noncomputable def component98Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node19_sound : Sound component98Node19Box :=
  sound_of_literal_split component98Node19Box leaf4771Box leaf4772Box
    .k (231/64) (by rfl) (by rfl)
    leaf4771FlatSound leaf4772FlatSound

private noncomputable def component98Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node20_sound : Sound component98Node20Box :=
  sound_of_literal_split component98Node20Box component98Node18Box component98Node19Box
    .chi (65/256) (by rfl) (by rfl)
    component98Node18_sound component98Node19_sound

private noncomputable def component98Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node21_sound : Sound component98Node21Box :=
  sound_of_literal_split component98Node21Box component98Node17Box component98Node20Box
    .k (115/32) (by rfl) (by rfl)
    component98Node17_sound component98Node20_sound

private noncomputable def component98Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node22_sound : Sound component98Node22Box :=
  sound_of_literal_split component98Node22Box leaf4773Box leaf4774Box
    .k (229/64) (by rfl) (by rfl)
    leaf4773FlatSound leaf4774FlatSound

private noncomputable def component98Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node23_sound : Sound component98Node23Box :=
  sound_of_literal_split component98Node23Box leaf4775Box leaf4776Box
    .k (229/64) (by rfl) (by rfl)
    leaf4775FlatSound leaf4776FlatSound

private noncomputable def component98Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node24_sound : Sound component98Node24Box :=
  sound_of_literal_split component98Node24Box component98Node22Box component98Node23Box
    .chi (67/256) (by rfl) (by rfl)
    component98Node22_sound component98Node23_sound

private noncomputable def component98Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node25_sound : Sound component98Node25Box :=
  sound_of_literal_split component98Node25Box leaf4777Box leaf4778Box
    .k (231/64) (by rfl) (by rfl)
    leaf4777FlatSound leaf4778FlatSound

private noncomputable def component98Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node26_sound : Sound component98Node26Box :=
  sound_of_literal_split component98Node26Box leaf4779Box leaf4780Box
    .k (231/64) (by rfl) (by rfl)
    leaf4779FlatSound leaf4780FlatSound

private noncomputable def component98Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node27_sound : Sound component98Node27Box :=
  sound_of_literal_split component98Node27Box component98Node25Box component98Node26Box
    .chi (67/256) (by rfl) (by rfl)
    component98Node25_sound component98Node26_sound

private noncomputable def component98Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node28_sound : Sound component98Node28Box :=
  sound_of_literal_split component98Node28Box component98Node24Box component98Node27Box
    .k (115/32) (by rfl) (by rfl)
    component98Node24_sound component98Node27_sound

private noncomputable def component98Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node29_sound : Sound component98Node29Box :=
  sound_of_literal_split component98Node29Box component98Node21Box component98Node28Box
    .chi (33/128) (by rfl) (by rfl)
    component98Node21_sound component98Node28_sound

private noncomputable def component98Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component98Node30_sound : Sound component98Node30Box :=
  sound_of_literal_split component98Node30Box component98Node14Box component98Node29Box
    .k (57/16) (by rfl) (by rfl)
    component98Node14_sound component98Node29_sound

private noncomputable def component98Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node31_sound : Sound component98Node31Box :=
  sound_of_literal_split component98Node31Box leaf4781Box leaf4782Box
    .k (225/64) (by rfl) (by rfl)
    leaf4781FlatSound leaf4782FlatSound

private noncomputable def component98Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node32_sound : Sound component98Node32Box :=
  sound_of_literal_split component98Node32Box leaf4783Box leaf4784Box
    .k (225/64) (by rfl) (by rfl)
    leaf4783FlatSound leaf4784FlatSound

private noncomputable def component98Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node33_sound : Sound component98Node33Box :=
  sound_of_literal_split component98Node33Box component98Node31Box component98Node32Box
    .chi (69/256) (by rfl) (by rfl)
    component98Node31_sound component98Node32_sound

private noncomputable def component98Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node34_sound : Sound component98Node34Box :=
  sound_of_literal_split component98Node34Box leaf4785Box leaf4786Box
    .k (227/64) (by rfl) (by rfl)
    leaf4785FlatSound leaf4786FlatSound

private noncomputable def component98Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node35_sound : Sound component98Node35Box :=
  sound_of_literal_split component98Node35Box leaf4787Box leaf4788Box
    .k (227/64) (by rfl) (by rfl)
    leaf4787FlatSound leaf4788FlatSound

private noncomputable def component98Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node36_sound : Sound component98Node36Box :=
  sound_of_literal_split component98Node36Box component98Node34Box component98Node35Box
    .chi (69/256) (by rfl) (by rfl)
    component98Node34_sound component98Node35_sound

private noncomputable def component98Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node37_sound : Sound component98Node37Box :=
  sound_of_literal_split component98Node37Box component98Node33Box component98Node36Box
    .k (113/32) (by rfl) (by rfl)
    component98Node33_sound component98Node36_sound

private noncomputable def component98Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node38_sound : Sound component98Node38Box :=
  sound_of_literal_split component98Node38Box leaf4789Box leaf4790Box
    .k (225/64) (by rfl) (by rfl)
    leaf4789FlatSound leaf4790FlatSound

private noncomputable def component98Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node39_sound : Sound component98Node39Box :=
  sound_of_literal_split component98Node39Box leaf4791Box leaf4792Box
    .k (225/64) (by rfl) (by rfl)
    leaf4791FlatSound leaf4792FlatSound

private noncomputable def component98Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node40_sound : Sound component98Node40Box :=
  sound_of_literal_split component98Node40Box component98Node38Box component98Node39Box
    .chi (71/256) (by rfl) (by rfl)
    component98Node38_sound component98Node39_sound

private noncomputable def component98Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node41_sound : Sound component98Node41Box :=
  sound_of_literal_split component98Node41Box leaf4793Box leaf4794Box
    .k (227/64) (by rfl) (by rfl)
    leaf4793FlatSound leaf4794FlatSound

private noncomputable def component98Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node42_sound : Sound component98Node42Box :=
  sound_of_literal_split component98Node42Box leaf4795Box leaf4796Box
    .k (227/64) (by rfl) (by rfl)
    leaf4795FlatSound leaf4796FlatSound

private noncomputable def component98Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node43_sound : Sound component98Node43Box :=
  sound_of_literal_split component98Node43Box component98Node41Box component98Node42Box
    .chi (71/256) (by rfl) (by rfl)
    component98Node41_sound component98Node42_sound

private noncomputable def component98Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node44_sound : Sound component98Node44Box :=
  sound_of_literal_split component98Node44Box component98Node40Box component98Node43Box
    .k (113/32) (by rfl) (by rfl)
    component98Node40_sound component98Node43_sound

private noncomputable def component98Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node45_sound : Sound component98Node45Box :=
  sound_of_literal_split component98Node45Box component98Node37Box component98Node44Box
    .chi (35/128) (by rfl) (by rfl)
    component98Node37_sound component98Node44_sound

private noncomputable def component98Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node46_sound : Sound component98Node46Box :=
  sound_of_literal_split component98Node46Box leaf4797Box leaf4798Box
    .k (229/64) (by rfl) (by rfl)
    leaf4797FlatSound leaf4798FlatSound

private noncomputable def component98Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node47_sound : Sound component98Node47Box :=
  sound_of_literal_split component98Node47Box leaf4799Box leaf4800Box
    .k (229/64) (by rfl) (by rfl)
    leaf4799FlatSound leaf4800FlatSound

private noncomputable def component98Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node48_sound : Sound component98Node48Box :=
  sound_of_literal_split component98Node48Box component98Node46Box component98Node47Box
    .chi (69/256) (by rfl) (by rfl)
    component98Node46_sound component98Node47_sound

private noncomputable def component98Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node49_sound : Sound component98Node49Box :=
  sound_of_literal_split component98Node49Box leaf4801Box leaf4802Box
    .k (231/64) (by rfl) (by rfl)
    leaf4801FlatSound leaf4802FlatSound

private noncomputable def component98Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node50_sound : Sound component98Node50Box :=
  sound_of_literal_split component98Node50Box leaf4803Box leaf4804Box
    .k (231/64) (by rfl) (by rfl)
    leaf4803FlatSound leaf4804FlatSound

private noncomputable def component98Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node51_sound : Sound component98Node51Box :=
  sound_of_literal_split component98Node51Box component98Node49Box component98Node50Box
    .chi (69/256) (by rfl) (by rfl)
    component98Node49_sound component98Node50_sound

private noncomputable def component98Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component98Node52_sound : Sound component98Node52Box :=
  sound_of_literal_split component98Node52Box component98Node48Box component98Node51Box
    .k (115/32) (by rfl) (by rfl)
    component98Node48_sound component98Node51_sound

private noncomputable def component98Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node53_sound : Sound component98Node53Box :=
  sound_of_literal_split component98Node53Box leaf4805Box leaf4806Box
    .k (229/64) (by rfl) (by rfl)
    leaf4805FlatSound leaf4806FlatSound

private noncomputable def component98Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node54_sound : Sound component98Node54Box :=
  sound_of_literal_split component98Node54Box leaf4807Box leaf4808Box
    .k (229/64) (by rfl) (by rfl)
    leaf4807FlatSound leaf4808FlatSound

private noncomputable def component98Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node55_sound : Sound component98Node55Box :=
  sound_of_literal_split component98Node55Box component98Node53Box component98Node54Box
    .chi (71/256) (by rfl) (by rfl)
    component98Node53_sound component98Node54_sound

private noncomputable def component98Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component98Node56_sound : Sound component98Node56Box :=
  sound_of_literal_split component98Node56Box leaf4809Box leaf4810Box
    .k (231/64) (by rfl) (by rfl)
    leaf4809FlatSound leaf4810FlatSound

private noncomputable def component98Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node57_sound : Sound component98Node57Box :=
  sound_of_literal_split component98Node57Box leaf4811Box leaf4812Box
    .k (231/64) (by rfl) (by rfl)
    leaf4811FlatSound leaf4812FlatSound

private noncomputable def component98Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node58_sound : Sound component98Node58Box :=
  sound_of_literal_split component98Node58Box component98Node56Box component98Node57Box
    .chi (71/256) (by rfl) (by rfl)
    component98Node56_sound component98Node57_sound

private noncomputable def component98Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node59_sound : Sound component98Node59Box :=
  sound_of_literal_split component98Node59Box component98Node55Box component98Node58Box
    .k (115/32) (by rfl) (by rfl)
    component98Node55_sound component98Node58_sound

private noncomputable def component98Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node60_sound : Sound component98Node60Box :=
  sound_of_literal_split component98Node60Box component98Node52Box component98Node59Box
    .chi (35/128) (by rfl) (by rfl)
    component98Node52_sound component98Node59_sound

private noncomputable def component98Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component98Node61_sound : Sound component98Node61Box :=
  sound_of_literal_split component98Node61Box component98Node45Box component98Node60Box
    .k (57/16) (by rfl) (by rfl)
    component98Node45_sound component98Node60_sound

noncomputable def component98Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
theorem component98_sound : Sound component98Box :=
  sound_of_literal_split component98Box component98Node30Box component98Node61Box
    .chi (17/64) (by rfl) (by rfl)
    component98Node30_sound component98Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
