import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0

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

private noncomputable def leaf605Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf605Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108987/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357778432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (125792647/67108864) }, upper := { exponent := 0, mantissa := (1981/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717058047/68715556864) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf605InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf605LocalValidity :
    LeafFacts leaf605Box leaf605Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf605Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357778432) }) = true
      norm_num [leaf605Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf605CertificateValid :
    WideCertificateValid leaf605Box leaf605Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi82ValidityFacts
    leaf605LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf605CoverageChecked :
    coverageCheck (innerAD leaf605Box) leaf605InnerLog = true := by
  rfl'

private theorem leaf605InnerLogValid :
    leaf605InnerLog.Valid 8 (innerAD leaf605Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf605CoverageChecked

private noncomputable def leaf605InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf605InputLogOnePlusV_eq :
    leaf605InputLogOnePlusV = outerEnclosure 24
      (leaf605Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf605RoundedFacts : LeafRoundedFacts 8
    leaf605Certificate.logOnePlusV leaf605InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf605InputLogOnePlusV_eq }

private noncomputable def leaf605Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi82InputQChi innerPair92Input
    leaf605InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf605LowerChecked :
    lowerCheck 24 leaf605Box leaf605Inputs = true := by
  rfl'

private theorem leaf605CoversExact : CoversExact 8
    leaf605Box leaf605Certificate leaf605InnerLog leaf605Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi82RoundedFacts
    innerPair92RoundedFacts leaf605RoundedFacts (by rfl)

private theorem leaf605FlatSound : Sound leaf605Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf605CertificateValid
    leaf605InnerLogValid leaf605CoversExact leaf605LowerChecked

private noncomputable def leaf606Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf606Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108989/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871543808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (127627541/67108864) }, upper := { exponent := 0, mantissa := (1005/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743399731/13743087616) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf606InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf606LocalValidity :
    LeafFacts leaf606Box leaf606Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf606Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871543808) }) = true
      norm_num [leaf606Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf606CertificateValid :
    WideCertificateValid leaf606Box leaf606Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi83ValidityFacts
    leaf606LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf606CoverageChecked :
    coverageCheck (innerAD leaf606Box) leaf606InnerLog = true := by
  rfl'

private theorem leaf606InnerLogValid :
    leaf606InnerLog.Valid 8 (innerAD leaf606Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf606CoverageChecked

private noncomputable def leaf606InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf606InputLogOnePlusV_eq :
    leaf606InputLogOnePlusV = outerEnclosure 24
      (leaf606Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf606RoundedFacts : LeafRoundedFacts 8
    leaf606Certificate.logOnePlusV leaf606InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf606InputLogOnePlusV_eq }

private noncomputable def leaf606Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi83InputQChi innerPair101Input
    leaf606InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf606LowerChecked :
    lowerCheck 24 leaf606Box leaf606Inputs = true := by
  rfl'

private theorem leaf606CoversExact : CoversExact 8
    leaf606Box leaf606Certificate leaf606InnerLog leaf606Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi83RoundedFacts
    innerPair101RoundedFacts leaf606RoundedFacts (by rfl)

private theorem leaf606FlatSound : Sound leaf606Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf606CertificateValid
    leaf606InnerLogValid leaf606CoversExact leaf606LowerChecked

private noncomputable def leaf607Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf607Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108989/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357710848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (127889669/67108864) }, upper := { exponent := 0, mantissa := (1007/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68716990463/68715421696) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf607InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf607LocalValidity :
    LeafFacts leaf607Box leaf607Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf607Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357710848) }) = true
      norm_num [leaf607Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf607CertificateValid :
    WideCertificateValid leaf607Box leaf607Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi82ValidityFacts
    leaf607LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf607CoverageChecked :
    coverageCheck (innerAD leaf607Box) leaf607InnerLog = true := by
  rfl'

private theorem leaf607InnerLogValid :
    leaf607InnerLog.Valid 8 (innerAD leaf607Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf607CoverageChecked

private noncomputable def leaf607InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf607InputLogOnePlusV_eq :
    leaf607InputLogOnePlusV = outerEnclosure 24
      (leaf607Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf607RoundedFacts : LeafRoundedFacts 8
    leaf607Certificate.logOnePlusV leaf607InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf607InputLogOnePlusV_eq }

private noncomputable def leaf607Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi82InputQChi innerPair101Input
    leaf607InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf607LowerChecked :
    lowerCheck 24 leaf607Box leaf607Inputs = true := by
  rfl'

private theorem leaf607CoversExact : CoversExact 8
    leaf607Box leaf607Certificate leaf607InnerLog leaf607Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi82RoundedFacts
    innerPair101RoundedFacts leaf607RoundedFacts (by rfl)

private theorem leaf607FlatSound : Sound leaf607Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf607CertificateValid
    leaf607InnerLogValid leaf607CoversExact leaf607LowerChecked

private noncomputable def leaf608Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf608Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108991/67108864) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178824704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (129790095/67108864) }, upper := { exponent := 0, mantissa := (511/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358202367/34357649408) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf608InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf608LocalValidity :
    LeafFacts leaf608Box leaf608Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf608Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178824704) }) = true
      norm_num [leaf608Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf608CertificateValid :
    WideCertificateValid leaf608Box leaf608Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi83ValidityFacts
    leaf608LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf608CoverageChecked :
    coverageCheck (innerAD leaf608Box) leaf608InnerLog = true := by
  rfl'

private theorem leaf608InnerLogValid :
    leaf608InnerLog.Valid 8 (innerAD leaf608Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf608CoverageChecked

private noncomputable def leaf608InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf608InputLogOnePlusV_eq :
    leaf608InputLogOnePlusV = outerEnclosure 24
      (leaf608Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf608RoundedFacts : LeafRoundedFacts 8
    leaf608Certificate.logOnePlusV leaf608InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf608InputLogOnePlusV_eq }

private noncomputable def leaf608Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi83InputQChi innerPair101Input
    leaf608InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf608LowerChecked :
    lowerCheck 24 leaf608Box leaf608Inputs = true := by
  rfl'

private theorem leaf608CoversExact : CoversExact 8
    leaf608Box leaf608Certificate leaf608InnerLog leaf608Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi83RoundedFacts
    innerPair101RoundedFacts leaf608RoundedFacts (by rfl)

private theorem leaf608FlatSound : Sound leaf608Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf608CertificateValid
    leaf608InnerLogValid leaf608CoversExact leaf608LowerChecked

private noncomputable def leaf609Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf609Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554525/33554432) }, vSqrt := { lower := (16383/16384), upper := (2454196809/2454114304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (64714805/33554432) }, upper := { exponent := 1, mantissa := (517/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4908311113/4908228608) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf609InnerLog : WideLogData :=
  innerPair305Data

set_option maxRecDepth 1000000 in
private theorem leaf609LocalValidity :
    LeafFacts leaf609Box leaf609Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf609Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2454196809/2454114304) }) = true
      norm_num [leaf609Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf609CertificateValid :
    WideCertificateValid leaf609Box leaf609Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi71ValidityFacts
    leaf609LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf609CoverageChecked :
    coverageCheck (innerAD leaf609Box) leaf609InnerLog = true := by
  rfl'

private theorem leaf609InnerLogValid :
    leaf609InnerLog.Valid 8 (innerAD leaf609Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint82PositiveFacts.valid leaf609CoverageChecked

private noncomputable def leaf609InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf609InputLogOnePlusV_eq :
    leaf609InputLogOnePlusV = outerEnclosure 24
      (leaf609Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf609RoundedFacts : LeafRoundedFacts 8
    leaf609Certificate.logOnePlusV leaf609InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf609InputLogOnePlusV_eq }

private noncomputable def leaf609Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi71InputQChi innerPair305Input
    leaf609InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf609LowerChecked :
    lowerCheck 24 leaf609Box leaf609Inputs = true := by
  rfl'

private theorem leaf609CoversExact : CoversExact 8
    leaf609Box leaf609Certificate leaf609InnerLog leaf609Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi71RoundedFacts
    innerPair305RoundedFacts leaf609RoundedFacts (by rfl)

private theorem leaf609FlatSound : Sound leaf609Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf609CertificateValid
    leaf609InnerLogValid leaf609CoversExact leaf609LowerChecked

private noncomputable def leaf610Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf610Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554527/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178763264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (65828847/33554432) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358140927/34357526528) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf610InnerLog : WideLogData :=
  innerPair313Data

set_option maxRecDepth 1000000 in
private theorem leaf610LocalValidity :
    LeafFacts leaf610Box leaf610Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf610Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178763264) }) = true
      norm_num [leaf610Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf610CertificateValid :
    WideCertificateValid leaf610Box leaf610Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi71ValidityFacts
    leaf610LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf610CoverageChecked :
    coverageCheck (innerAD leaf610Box) leaf610InnerLog = true := by
  rfl'

private theorem leaf610InnerLogValid :
    leaf610InnerLog.Valid 8 (innerAD leaf610Box) :=
  wideLogDataValid_of_cachedCheck endpoint83PositiveFacts
    endpoint84PositiveFacts.valid leaf610CoverageChecked

private noncomputable def leaf610InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf610InputLogOnePlusV_eq :
    leaf610InputLogOnePlusV = outerEnclosure 24
      (leaf610Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf610RoundedFacts : LeafRoundedFacts 8
    leaf610Certificate.logOnePlusV leaf610InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf610InputLogOnePlusV_eq }

private noncomputable def leaf610Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi71InputQChi innerPair313Input
    leaf610InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf610LowerChecked :
    lowerCheck 24 leaf610Box leaf610Inputs = true := by
  rfl'

private theorem leaf610CoversExact : CoversExact 8
    leaf610Box leaf610Certificate leaf610InnerLog leaf610Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi71RoundedFacts
    innerPair313RoundedFacts leaf610RoundedFacts (by rfl)

private theorem leaf610FlatSound : Sound leaf610Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf610CertificateValid
    leaf610InnerLogValid leaf610CoversExact leaf610LowerChecked

private noncomputable def leaf611Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf611Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108991/67108864) }, vSqrt := { lower := (16383/16384), upper := (2454196809/2454117376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (129986691/67108864) }, upper := { exponent := 0, mantissa := (2047/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4908314185/4908234752) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf611InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf611LocalValidity :
    LeafFacts leaf611Box leaf611Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf611Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2454196809/2454117376) }) = true
      norm_num [leaf611Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf611CertificateValid :
    WideCertificateValid leaf611Box leaf611Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi82ValidityFacts
    leaf611LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf611CoverageChecked :
    coverageCheck (innerAD leaf611Box) leaf611InnerLog = true := by
  rfl'

private theorem leaf611InnerLogValid :
    leaf611InnerLog.Valid 8 (innerAD leaf611Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf611CoverageChecked

private noncomputable def leaf611InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf611InputLogOnePlusV_eq :
    leaf611InputLogOnePlusV = outerEnclosure 24
      (leaf611Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf611RoundedFacts : LeafRoundedFacts 8
    leaf611Certificate.logOnePlusV leaf611InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf611InputLogOnePlusV_eq }

private noncomputable def leaf611Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi82InputQChi innerPair101Input
    leaf611InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf611LowerChecked :
    lowerCheck 24 leaf611Box leaf611Inputs = true := by
  rfl'

private theorem leaf611CoversExact : CoversExact 8
    leaf611Box leaf611Certificate leaf611InnerLog leaf611Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi82RoundedFacts
    innerPair101RoundedFacts leaf611RoundedFacts (by rfl)

private theorem leaf611FlatSound : Sound leaf611Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf611CertificateValid
    leaf611InnerLogValid leaf611CoversExact leaf611LowerChecked

private noncomputable def leaf612Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf612Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108993/67108864) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726263296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (131952649/67108864) }, upper := { exponent := 1, mantissa := (1039/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452722517/11452526592) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf612InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf612LocalValidity :
    LeafFacts leaf612Box leaf612Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf612Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726263296) }) = true
      norm_num [leaf612Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf612CertificateValid :
    WideCertificateValid leaf612Box leaf612Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi83ValidityFacts
    leaf612LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf612CoverageChecked :
    coverageCheck (innerAD leaf612Box) leaf612InnerLog = true := by
  rfl'

private theorem leaf612InnerLogValid :
    leaf612InnerLog.Valid 8 (innerAD leaf612Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf612CoverageChecked

private noncomputable def leaf612InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf612InputLogOnePlusV_eq :
    leaf612InputLogOnePlusV = outerEnclosure 24
      (leaf612Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf612RoundedFacts : LeafRoundedFacts 8
    leaf612Certificate.logOnePlusV leaf612InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf612InputLogOnePlusV_eq }

private noncomputable def leaf612Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi83InputQChi innerPair110Input
    leaf612InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf612LowerChecked :
    lowerCheck 24 leaf612Box leaf612Inputs = true := by
  rfl'

private theorem leaf612CoversExact : CoversExact 8
    leaf612Box leaf612Certificate leaf612InnerLog leaf612Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi83RoundedFacts
    innerPair110RoundedFacts leaf612RoundedFacts (by rfl)

private theorem leaf612FlatSound : Sound leaf612Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf612CertificateValid
    leaf612InnerLogValid leaf612CoversExact leaf612LowerChecked

private noncomputable def leaf613Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf613Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108993/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178787840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (132083713/67108864) }, upper := { exponent := 1, mantissa := (65/64) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358165503/34357575680) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf613InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf613LocalValidity :
    LeafFacts leaf613Box leaf613Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf613Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178787840) }) = true
      norm_num [leaf613Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf613CertificateValid :
    WideCertificateValid leaf613Box leaf613Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi82ValidityFacts
    leaf613LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf613CoverageChecked :
    coverageCheck (innerAD leaf613Box) leaf613InnerLog = true := by
  rfl'

private theorem leaf613InnerLogValid :
    leaf613InnerLog.Valid 8 (innerAD leaf613Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf613CoverageChecked

private noncomputable def leaf613InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf613InputLogOnePlusV_eq :
    leaf613InputLogOnePlusV = outerEnclosure 24
      (leaf613Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf613RoundedFacts : LeafRoundedFacts 8
    leaf613Certificate.logOnePlusV leaf613InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf613InputLogOnePlusV_eq }

private noncomputable def leaf613Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi82InputQChi innerPair110Input
    leaf613InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf613LowerChecked :
    lowerCheck 24 leaf613Box leaf613Inputs = true := by
  rfl'

private theorem leaf613CoversExact : CoversExact 8
    leaf613Box leaf613Certificate leaf613InnerLog leaf613Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi82RoundedFacts
    innerPair110RoundedFacts leaf613RoundedFacts (by rfl)

private theorem leaf613FlatSound : Sound leaf613Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf613CertificateValid
    leaf613InnerLogValid leaf613CoversExact leaf613LowerChecked

private noncomputable def leaf614Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf614Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108995/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178755072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (134115203/67108864) }, upper := { exponent := 1, mantissa := (33/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358132735/34357510144) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf614InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf614LocalValidity :
    LeafFacts leaf614Box leaf614Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf614Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178755072) }) = true
      norm_num [leaf614Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf614CertificateValid :
    WideCertificateValid leaf614Box leaf614Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi83ValidityFacts
    leaf614LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf614CoverageChecked :
    coverageCheck (innerAD leaf614Box) leaf614InnerLog = true := by
  rfl'

private theorem leaf614InnerLogValid :
    leaf614InnerLog.Valid 8 (innerAD leaf614Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf614CoverageChecked

private noncomputable def leaf614InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf614InputLogOnePlusV_eq :
    leaf614InputLogOnePlusV = outerEnclosure 24
      (leaf614Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf614RoundedFacts : LeafRoundedFacts 8
    leaf614Certificate.logOnePlusV leaf614InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf614InputLogOnePlusV_eq }

private noncomputable def leaf614Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi83InputQChi innerPair110Input
    leaf614InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf614LowerChecked :
    lowerCheck 24 leaf614Box leaf614Inputs = true := by
  rfl'

private theorem leaf614CoversExact : CoversExact 8
    leaf614Box leaf614Certificate leaf614InnerLog leaf614Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi83RoundedFacts
    innerPair110RoundedFacts leaf614RoundedFacts (by rfl)

private theorem leaf614FlatSound : Sound leaf614Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf614CertificateValid
    leaf614InnerLogValid leaf614CoversExact leaf614LowerChecked

private noncomputable def leaf615Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf615Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108995/67108864) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178758144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (133918607/67108864) }, upper := { exponent := 1, mantissa := (2109/2048) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358135807/34357516288) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf615InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf615LocalValidity :
    LeafFacts leaf615Box leaf615Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf615Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178758144) }) = true
      norm_num [leaf615Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf615CertificateValid :
    WideCertificateValid leaf615Box leaf615Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi84ValidityFacts
    leaf615LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf615CoverageChecked :
    coverageCheck (innerAD leaf615Box) leaf615InnerLog = true := by
  rfl'

private theorem leaf615InnerLogValid :
    leaf615InnerLog.Valid 8 (innerAD leaf615Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf615CoverageChecked

private noncomputable def leaf615InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf615InputLogOnePlusV_eq :
    leaf615InputLogOnePlusV = outerEnclosure 24
      (leaf615Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf615RoundedFacts : LeafRoundedFacts 8
    leaf615Certificate.logOnePlusV leaf615InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf615InputLogOnePlusV_eq }

private noncomputable def leaf615Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi84InputQChi innerPair110Input
    leaf615InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf615LowerChecked :
    lowerCheck 24 leaf615Box leaf615Inputs = true := by
  rfl'

private theorem leaf615CoversExact : CoversExact 8
    leaf615Box leaf615Certificate leaf615InnerLog leaf615Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi84RoundedFacts
    innerPair110RoundedFacts leaf615RoundedFacts (by rfl)

private theorem leaf615FlatSound : Sound leaf615Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf615CertificateValid
    leaf615InnerLogValid leaf615CoversExact leaf615LowerChecked

private noncomputable def leaf616Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf616Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108997/67108864) }, vSqrt := { lower := (16383/16384), upper := (113770713/113766400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (135884565/134217728) }, upper := { exponent := 1, mantissa := (535/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (227537113/227532800) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf616InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf616LocalValidity :
    LeafFacts leaf616Box leaf616Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf616Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (113770713/113766400) }) = true
      norm_num [leaf616Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf616CertificateValid :
    WideCertificateValid leaf616Box leaf616Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi85ValidityFacts
    leaf616LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf616CoverageChecked :
    coverageCheck (innerAD leaf616Box) leaf616InnerLog = true := by
  rfl'

private theorem leaf616InnerLogValid :
    leaf616InnerLog.Valid 8 (innerAD leaf616Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf616CoverageChecked

private noncomputable def leaf616InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf616InputLogOnePlusV_eq :
    leaf616InputLogOnePlusV = outerEnclosure 24
      (leaf616Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf616RoundedFacts : LeafRoundedFacts 8
    leaf616Certificate.logOnePlusV leaf616InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf616InputLogOnePlusV_eq }

private noncomputable def leaf616Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi85InputQChi innerPair117Input
    leaf616InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf616LowerChecked :
    lowerCheck 24 leaf616Box leaf616Inputs = true := by
  rfl'

private theorem leaf616CoversExact : CoversExact 8
    leaf616Box leaf616Certificate leaf616InnerLog leaf616Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi85RoundedFacts
    innerPair117RoundedFacts leaf616RoundedFacts (by rfl)

private theorem leaf616FlatSound : Sound leaf616Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf616CertificateValid
    leaf616InnerLogValid leaf616CoversExact leaf616LowerChecked

private noncomputable def leaf617Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf617Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108997/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726240768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (136146693/134217728) }, upper := { exponent := 1, mantissa := (67/64) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452699989/11452481536) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf617InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf617LocalValidity :
    LeafFacts leaf617Box leaf617Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf617Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726240768) }) = true
      norm_num [leaf617Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf617CertificateValid :
    WideCertificateValid leaf617Box leaf617Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi84ValidityFacts
    leaf617LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf617CoverageChecked :
    coverageCheck (innerAD leaf617Box) leaf617InnerLog = true := by
  rfl'

private theorem leaf617InnerLogValid :
    leaf617InnerLog.Valid 8 (innerAD leaf617Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf617CoverageChecked

private noncomputable def leaf617InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf617InputLogOnePlusV_eq :
    leaf617InputLogOnePlusV = outerEnclosure 24
      (leaf617Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf617RoundedFacts : LeafRoundedFacts 8
    leaf617Certificate.logOnePlusV leaf617InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf617InputLogOnePlusV_eq }

private noncomputable def leaf617Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi84InputQChi innerPair117Input
    leaf617InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf617LowerChecked :
    lowerCheck 24 leaf617Box leaf617Inputs = true := by
  rfl'

private theorem leaf617CoversExact : CoversExact 8
    leaf617Box leaf617Certificate leaf617InnerLog leaf617Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi84RoundedFacts
    innerPair117RoundedFacts leaf617RoundedFacts (by rfl)

private theorem leaf617FlatSound : Sound leaf617Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf617CertificateValid
    leaf617InnerLogValid leaf617CoversExact leaf617LowerChecked

private noncomputable def leaf618Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf618Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108999/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178689536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (138178183/134217728) }, upper := { exponent := 1, mantissa := (17/16) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358067199/34357379072) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf618InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf618LocalValidity :
    LeafFacts leaf618Box leaf618Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf618Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178689536) }) = true
      norm_num [leaf618Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf618CertificateValid :
    WideCertificateValid leaf618Box leaf618Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi85ValidityFacts
    leaf618LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf618CoverageChecked :
    coverageCheck (innerAD leaf618Box) leaf618InnerLog = true := by
  rfl'

private theorem leaf618InnerLogValid :
    leaf618InnerLog.Valid 8 (innerAD leaf618Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf618CoverageChecked

private noncomputable def leaf618InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf618InputLogOnePlusV_eq :
    leaf618InputLogOnePlusV = outerEnclosure 24
      (leaf618Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf618RoundedFacts : LeafRoundedFacts 8
    leaf618Certificate.logOnePlusV leaf618InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf618InputLogOnePlusV_eq }

private noncomputable def leaf618Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi85InputQChi innerPair117Input
    leaf618InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf618LowerChecked :
    lowerCheck 24 leaf618Box leaf618Inputs = true := by
  rfl'

private theorem leaf618CoversExact : CoversExact 8
    leaf618Box leaf618Certificate leaf618InnerLog leaf618Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi85RoundedFacts
    innerPair117RoundedFacts leaf618RoundedFacts (by rfl)

private theorem leaf618FlatSound : Sound leaf618Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf618CertificateValid
    leaf618InnerLogValid leaf618CoversExact leaf618LowerChecked

private noncomputable def leaf619Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf619Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554527/33554432) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726246912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (66549699/33554432) }, upper := { exponent := 1, mantissa := (1063/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452706133/11452493824) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf619InnerLog : WideLogData :=
  innerPair318Data

set_option maxRecDepth 1000000 in
private theorem leaf619LocalValidity :
    LeafFacts leaf619Box leaf619Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf619Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726246912) }) = true
      norm_num [leaf619Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf619CertificateValid :
    WideCertificateValid leaf619Box leaf619Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi72ValidityFacts
    leaf619LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf619CoverageChecked :
    coverageCheck (innerAD leaf619Box) leaf619InnerLog = true := by
  rfl'

private theorem leaf619InnerLogValid :
    leaf619InnerLog.Valid 8 (innerAD leaf619Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint86PositiveFacts.valid leaf619CoverageChecked

private noncomputable def leaf619InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf619InputLogOnePlusV_eq :
    leaf619InputLogOnePlusV = outerEnclosure 24
      (leaf619Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf619RoundedFacts : LeafRoundedFacts 8
    leaf619Certificate.logOnePlusV leaf619InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf619InputLogOnePlusV_eq }

private noncomputable def leaf619Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi72InputQChi innerPair318Input
    leaf619InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf619LowerChecked :
    lowerCheck 24 leaf619Box leaf619Inputs = true := by
  rfl'

private theorem leaf619CoversExact : CoversExact 8
    leaf619Box leaf619Certificate leaf619InnerLog leaf619Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi72RoundedFacts
    innerPair318RoundedFacts leaf619RoundedFacts (by rfl)

private theorem leaf619FlatSound : Sound leaf619Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf619CertificateValid
    leaf619InnerLogValid leaf619CoversExact leaf619LowerChecked

private noncomputable def leaf620Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf620Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554529/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178701824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (67729273/67108864) }, upper := { exponent := 1, mantissa := (541/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358079487/34357403648) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf620InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf620LocalValidity :
    LeafFacts leaf620Box leaf620Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf620Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178701824) }) = true
      norm_num [leaf620Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf620CertificateValid :
    WideCertificateValid leaf620Box leaf620Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi72ValidityFacts
    leaf620LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf620CoverageChecked :
    coverageCheck (innerAD leaf620Box) leaf620InnerLog = true := by
  rfl'

private theorem leaf620InnerLogValid :
    leaf620InnerLog.Valid 8 (innerAD leaf620Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf620CoverageChecked

private noncomputable def leaf620InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf620InputLogOnePlusV_eq :
    leaf620InputLogOnePlusV = outerEnclosure 24
      (leaf620Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf620RoundedFacts : LeafRoundedFacts 8
    leaf620Certificate.logOnePlusV leaf620InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf620InputLogOnePlusV_eq }

private noncomputable def leaf620Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi72InputQChi innerPair117Input
    leaf620InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf620LowerChecked :
    lowerCheck 24 leaf620Box leaf620Inputs = true := by
  rfl'

private theorem leaf620CoversExact : CoversExact 8
    leaf620Box leaf620Certificate leaf620InnerLog leaf620Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi72RoundedFacts
    innerPair117RoundedFacts leaf620RoundedFacts (by rfl)

private theorem leaf620FlatSound : Sound leaf620Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf620CertificateValid
    leaf620InnerLogValid leaf620CoversExact leaf620LowerChecked

private noncomputable def leaf621Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf621Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554529/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178681344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (68384593/67108864) }, upper := { exponent := 1, mantissa := (273/256) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358059007/34357362688) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf621InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf621LocalValidity :
    LeafFacts leaf621Box leaf621Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf621Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178681344) }) = true
      norm_num [leaf621Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf621CertificateValid :
    WideCertificateValid leaf621Box leaf621Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi73ValidityFacts
    leaf621LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf621CoverageChecked :
    coverageCheck (innerAD leaf621Box) leaf621InnerLog = true := by
  rfl'

private theorem leaf621InnerLogValid :
    leaf621InnerLog.Valid 8 (innerAD leaf621Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf621CoverageChecked

private noncomputable def leaf621InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf621InputLogOnePlusV_eq :
    leaf621InputLogOnePlusV = outerEnclosure 24
      (leaf621Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf621RoundedFacts : LeafRoundedFacts 8
    leaf621Certificate.logOnePlusV leaf621InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf621InputLogOnePlusV_eq }

private noncomputable def leaf621Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi73InputQChi innerPair118Input
    leaf621InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf621LowerChecked :
    lowerCheck 24 leaf621Box leaf621Inputs = true := by
  rfl'

private theorem leaf621CoversExact : CoversExact 8
    leaf621Box leaf621Certificate leaf621InnerLog leaf621Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi73RoundedFacts
    innerPair118RoundedFacts leaf621RoundedFacts (by rfl)

private theorem leaf621FlatSound : Sound leaf621Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf621CertificateValid
    leaf621InnerLogValid leaf621CoversExact leaf621LowerChecked

private noncomputable def leaf622Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf622Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554531/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178640384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (69629699/67108864) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358018047/34357280768) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf622InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf622LocalValidity :
    LeafFacts leaf622Box leaf622Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf622Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178640384) }) = true
      norm_num [leaf622Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf622CertificateValid :
    WideCertificateValid leaf622Box leaf622Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi73ValidityFacts
    leaf622LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf622CoverageChecked :
    coverageCheck (innerAD leaf622Box) leaf622InnerLog = true := by
  rfl'

private theorem leaf622InnerLogValid :
    leaf622InnerLog.Valid 8 (innerAD leaf622Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf622CoverageChecked

private noncomputable def leaf622InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf622InputLogOnePlusV_eq :
    leaf622InputLogOnePlusV = outerEnclosure 24
      (leaf622Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf622RoundedFacts : LeafRoundedFacts 8
    leaf622Certificate.logOnePlusV leaf622InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf622InputLogOnePlusV_eq }

private noncomputable def leaf622Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi73InputQChi innerPair243Input
    leaf622InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf622LowerChecked :
    lowerCheck 24 leaf622Box leaf622Inputs = true := by
  rfl'

private theorem leaf622CoversExact : CoversExact 8
    leaf622Box leaf622Certificate leaf622InnerLog leaf622Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi73RoundedFacts
    innerPair243RoundedFacts leaf622RoundedFacts (by rfl)

private theorem leaf622FlatSound : Sound leaf622Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf622CertificateValid
    leaf622InnerLogValid leaf622CoversExact leaf622LowerChecked

private noncomputable def leaf623Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf623Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554531/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178662912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (68908847/67108864) }, upper := { exponent := 1, mantissa := (1101/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358040575/34357325824) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf623InnerLog : WideLogData :=
  innerPair328Data

set_option maxRecDepth 1000000 in
private theorem leaf623LocalValidity :
    LeafFacts leaf623Box leaf623Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf623Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178662912) }) = true
      norm_num [leaf623Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf623CertificateValid :
    WideCertificateValid leaf623Box leaf623Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi72ValidityFacts
    leaf623LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf623CoverageChecked :
    coverageCheck (innerAD leaf623Box) leaf623InnerLog = true := by
  rfl'

private theorem leaf623InnerLogValid :
    leaf623InnerLog.Valid 8 (innerAD leaf623Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint88PositiveFacts.valid leaf623CoverageChecked

private noncomputable def leaf623InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf623InputLogOnePlusV_eq :
    leaf623InputLogOnePlusV = outerEnclosure 24
      (leaf623Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf623RoundedFacts : LeafRoundedFacts 8
    leaf623Certificate.logOnePlusV leaf623InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf623InputLogOnePlusV_eq }

private noncomputable def leaf623Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi72InputQChi innerPair328Input
    leaf623InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf623LowerChecked :
    lowerCheck 24 leaf623Box leaf623Inputs = true := by
  rfl'

private theorem leaf623CoversExact : CoversExact 8
    leaf623Box leaf623Certificate leaf623InnerLog leaf623Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi72RoundedFacts
    innerPair328RoundedFacts leaf623RoundedFacts (by rfl)

private theorem leaf623FlatSound : Sound leaf623Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf623CertificateValid
    leaf623InnerLogValid leaf623CoversExact leaf623LowerChecked

private noncomputable def leaf624Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf624Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109001/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454093824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (140209673/134217728) }, upper := { exponent := 1, mantissa := (69/64) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908290633/4908187648) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf624InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf624LocalValidity :
    LeafFacts leaf624Box leaf624Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf624Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454093824) }) = true
      norm_num [leaf624Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf624CertificateValid :
    WideCertificateValid leaf624Box leaf624Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi86ValidityFacts
    leaf624LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf624CoverageChecked :
    coverageCheck (innerAD leaf624Box) leaf624InnerLog = true := by
  rfl'

private theorem leaf624InnerLogValid :
    leaf624InnerLog.Valid 8 (innerAD leaf624Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf624CoverageChecked

private noncomputable def leaf624InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf624InputLogOnePlusV_eq :
    leaf624InputLogOnePlusV = outerEnclosure 24
      (leaf624Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf624RoundedFacts : LeafRoundedFacts 8
    leaf624Certificate.logOnePlusV leaf624InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf624InputLogOnePlusV_eq }

private noncomputable def leaf624Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi86InputQChi innerPair243Input
    leaf624InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf624LowerChecked :
    lowerCheck 24 leaf624Box leaf624Inputs = true := by
  rfl'

private theorem leaf624CoversExact : CoversExact 8
    leaf624Box leaf624Certificate leaf624InnerLog leaf624Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi86RoundedFacts
    innerPair243RoundedFacts leaf624RoundedFacts (by rfl)

private theorem leaf624FlatSound : Sound leaf624Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf624CertificateValid
    leaf624InnerLogValid leaf624CoversExact leaf624LowerChecked

private noncomputable def leaf625Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf625Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109003/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726208000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (142241163/134217728) }, upper := { exponent := 1, mantissa := (35/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452667221/11452416000) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf625InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf625LocalValidity :
    LeafFacts leaf625Box leaf625Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf625Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726208000) }) = true
      norm_num [leaf625Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf625CertificateValid :
    WideCertificateValid leaf625Box leaf625Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi87ValidityFacts
    leaf625LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf625CoverageChecked :
    coverageCheck (innerAD leaf625Box) leaf625InnerLog = true := by
  rfl'

private theorem leaf625InnerLogValid :
    leaf625InnerLog.Valid 8 (innerAD leaf625Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf625CoverageChecked

private noncomputable def leaf625InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf625InputLogOnePlusV_eq :
    leaf625InputLogOnePlusV = outerEnclosure 24
      (leaf625Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf625RoundedFacts : LeafRoundedFacts 8
    leaf625Certificate.logOnePlusV leaf625InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf625InputLogOnePlusV_eq }

private noncomputable def leaf625Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi87InputQChi innerPair243Input
    leaf625InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf625LowerChecked :
    lowerCheck 24 leaf625Box leaf625Inputs = true := by
  rfl'

private theorem leaf625CoversExact : CoversExact 8
    leaf625Box leaf625Certificate leaf625InnerLog leaf625Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi87RoundedFacts
    innerPair243RoundedFacts leaf625RoundedFacts (by rfl)

private theorem leaf625FlatSound : Sound leaf625Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf625CertificateValid
    leaf625InnerLogValid leaf625CoversExact leaf625LowerChecked

private noncomputable def leaf626Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf626Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554533/33554432) }, vSqrt := { lower := (16383/16384), upper := (818065603/818028544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (70874805/67108864) }, upper := { exponent := 1, mantissa := (283/256) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1636094147/1636057088) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf626InnerLog : WideLogData :=
  innerPair334Data

set_option maxRecDepth 1000000 in
private theorem leaf626LocalValidity :
    LeafFacts leaf626Box leaf626Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf626Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (818065603/818028544) }) = true
      norm_num [leaf626Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf626CertificateValid :
    WideCertificateValid leaf626Box leaf626Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi73ValidityFacts
    leaf626LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf626CoverageChecked :
    coverageCheck (innerAD leaf626Box) leaf626InnerLog = true := by
  rfl'

private theorem leaf626InnerLogValid :
    leaf626InnerLog.Valid 8 (innerAD leaf626Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint80PositiveFacts.valid leaf626CoverageChecked

private noncomputable def leaf626InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf626InputLogOnePlusV_eq :
    leaf626InputLogOnePlusV = outerEnclosure 24
      (leaf626Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf626RoundedFacts : LeafRoundedFacts 8
    leaf626Certificate.logOnePlusV leaf626InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf626InputLogOnePlusV_eq }

private noncomputable def leaf626Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi73InputQChi innerPair334Input
    leaf626InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf626LowerChecked :
    lowerCheck 24 leaf626Box leaf626Inputs = true := by
  rfl'

private theorem leaf626CoversExact : CoversExact 8
    leaf626Box leaf626Certificate leaf626InnerLog leaf626Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi73RoundedFacts
    innerPair334RoundedFacts leaf626RoundedFacts (by rfl)

private theorem leaf626FlatSound : Sound leaf626Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf626CertificateValid
    leaf626InnerLogValid leaf626CoversExact leaf626LowerChecked

private noncomputable def leaf627Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf627Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554535/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178558464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (72119911/67108864) }, upper := { exponent := 1, mantissa := (9/8) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357936127/34357116928) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf627InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf627LocalValidity :
    LeafFacts leaf627Box leaf627Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf627Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178558464) }) = true
      norm_num [leaf627Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf627CertificateValid :
    WideCertificateValid leaf627Box leaf627Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi73ValidityFacts
    leaf627LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf627CoverageChecked :
    coverageCheck (innerAD leaf627Box) leaf627InnerLog = true := by
  rfl'

private theorem leaf627InnerLogValid :
    leaf627InnerLog.Valid 8 (innerAD leaf627Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf627CoverageChecked

private noncomputable def leaf627InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf627InputLogOnePlusV_eq :
    leaf627InputLogOnePlusV = outerEnclosure 24
      (leaf627Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf627RoundedFacts : LeafRoundedFacts 8
    leaf627Certificate.logOnePlusV leaf627InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf627InputLogOnePlusV_eq }

private noncomputable def leaf627Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi73InputQChi innerPair250Input
    leaf627InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf627LowerChecked :
    lowerCheck 24 leaf627Box leaf627Inputs = true := by
  rfl'

private theorem leaf627CoversExact : CoversExact 8
    leaf627Box leaf627Certificate leaf627InnerLog leaf627Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi73RoundedFacts
    innerPair250RoundedFacts leaf627RoundedFacts (by rfl)

private theorem leaf627FlatSound : Sound leaf627Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf627CertificateValid
    leaf627InnerLogValid leaf627CoversExact leaf627LowerChecked

private noncomputable def leaf628Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf628Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554531/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178621952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (70219487/67108864) }, upper := { exponent := 1, mantissa := (1121/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357999615/34357243904) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf628InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf628LocalValidity :
    LeafFacts leaf628Box leaf628Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf628Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178621952) }) = true
      norm_num [leaf628Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf628CertificateValid :
    WideCertificateValid leaf628Box leaf628Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi74ValidityFacts
    leaf628LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf628CoverageChecked :
    coverageCheck (innerAD leaf628Box) leaf628InnerLog = true := by
  rfl'

private theorem leaf628InnerLogValid :
    leaf628InnerLog.Valid 8 (innerAD leaf628Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf628CoverageChecked

private noncomputable def leaf628InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf628InputLogOnePlusV_eq :
    leaf628InputLogOnePlusV = outerEnclosure 24
      (leaf628Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf628RoundedFacts : LeafRoundedFacts 8
    leaf628Certificate.logOnePlusV leaf628InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf628InputLogOnePlusV_eq }

private noncomputable def leaf628Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi74InputQChi innerPair244Input
    leaf628InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf628LowerChecked :
    lowerCheck 24 leaf628Box leaf628Inputs = true := by
  rfl'

private theorem leaf628CoversExact : CoversExact 8
    leaf628Box leaf628Certificate leaf628InnerLog leaf628Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi74RoundedFacts
    innerPair244RoundedFacts leaf628RoundedFacts (by rfl)

private theorem leaf628FlatSound : Sound leaf628Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf628CertificateValid
    leaf628InnerLogValid leaf628CoversExact leaf628LowerChecked

private noncomputable def leaf629Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf629Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554533/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178578944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (71530125/67108864) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357956607/34357157888) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf629InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf629LocalValidity :
    LeafFacts leaf629Box leaf629Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf629Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178578944) }) = true
      norm_num [leaf629Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf629CertificateValid :
    WideCertificateValid leaf629Box leaf629Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi74ValidityFacts
    leaf629LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf629CoverageChecked :
    coverageCheck (innerAD leaf629Box) leaf629InnerLog = true := by
  rfl'

private theorem leaf629InnerLogValid :
    leaf629InnerLog.Valid 8 (innerAD leaf629Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf629CoverageChecked

private noncomputable def leaf629InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf629InputLogOnePlusV_eq :
    leaf629InputLogOnePlusV = outerEnclosure 24
      (leaf629Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf629RoundedFacts : LeafRoundedFacts 8
    leaf629Certificate.logOnePlusV leaf629InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf629InputLogOnePlusV_eq }

private noncomputable def leaf629Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi74InputQChi innerPair250Input
    leaf629InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf629LowerChecked :
    lowerCheck 24 leaf629Box leaf629Inputs = true := by
  rfl'

private theorem leaf629CoversExact : CoversExact 8
    leaf629Box leaf629Certificate leaf629InnerLog leaf629Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi74RoundedFacts
    innerPair250RoundedFacts leaf629RoundedFacts (by rfl)

private theorem leaf629FlatSound : Sound leaf629Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf629CertificateValid
    leaf629InnerLogValid leaf629CoversExact leaf629LowerChecked

private noncomputable def leaf630Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf630Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554533/33554432) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726187520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (72054381/67108864) }, upper := { exponent := 1, mantissa := (575/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452646741/11452375040) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf630InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf630LocalValidity :
    LeafFacts leaf630Box leaf630Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf630Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726187520) }) = true
      norm_num [leaf630Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf630CertificateValid :
    WideCertificateValid leaf630Box leaf630Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi75ValidityFacts
    leaf630LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf630CoverageChecked :
    coverageCheck (innerAD leaf630Box) leaf630InnerLog = true := by
  rfl'

private theorem leaf630InnerLogValid :
    leaf630InnerLog.Valid 8 (innerAD leaf630Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf630CoverageChecked

private noncomputable def leaf630InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629479/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf630InputLogOnePlusV_eq :
    leaf630InputLogOnePlusV = outerEnclosure 24
      (leaf630Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf630RoundedFacts : LeafRoundedFacts 8
    leaf630Certificate.logOnePlusV leaf630InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf630InputLogOnePlusV_eq }

private noncomputable def leaf630Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi75InputQChi innerPair250Input
    leaf630InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf630LowerChecked :
    lowerCheck 24 leaf630Box leaf630Inputs = true := by
  rfl'

private theorem leaf630CoversExact : CoversExact 8
    leaf630Box leaf630Certificate leaf630InnerLog leaf630Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi75RoundedFacts
    innerPair250RoundedFacts leaf630RoundedFacts (by rfl)

private theorem leaf630FlatSound : Sound leaf630Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf630CertificateValid
    leaf630InnerLogValid leaf630CoversExact leaf630LowerChecked

private noncomputable def leaf631Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf631Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554535/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178517504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (73430551/67108864) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357895167/34357035008) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf631InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf631LocalValidity :
    LeafFacts leaf631Box leaf631Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf631Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178517504) }) = true
      norm_num [leaf631Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf631CertificateValid :
    WideCertificateValid leaf631Box leaf631Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi75ValidityFacts
    leaf631LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf631CoverageChecked :
    coverageCheck (innerAD leaf631Box) leaf631InnerLog = true := by
  rfl'

private theorem leaf631InnerLogValid :
    leaf631InnerLog.Valid 8 (innerAD leaf631Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf631CoverageChecked

private noncomputable def leaf631InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf631InputLogOnePlusV_eq :
    leaf631InputLogOnePlusV = outerEnclosure 24
      (leaf631Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf631RoundedFacts : LeafRoundedFacts 8
    leaf631Certificate.logOnePlusV leaf631InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf631InputLogOnePlusV_eq }

private noncomputable def leaf631Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi75InputQChi innerPair257Input
    leaf631InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf631LowerChecked :
    lowerCheck 24 leaf631Box leaf631Inputs = true := by
  rfl'

private theorem leaf631CoversExact : CoversExact 8
    leaf631Box leaf631Certificate leaf631InnerLog leaf631Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi75RoundedFacts
    innerPair257RoundedFacts leaf631RoundedFacts (by rfl)

private theorem leaf631FlatSound : Sound leaf631Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf631CertificateValid
    leaf631InnerLogValid leaf631CoversExact leaf631LowerChecked

private noncomputable def leaf632Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf632Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554535/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178503168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (73889275/67108864) }, upper := { exponent := 1, mantissa := (1179/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357880831/34357006336) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf632InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf632LocalValidity :
    LeafFacts leaf632Box leaf632Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf632Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178503168) }) = true
      norm_num [leaf632Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf632CertificateValid :
    WideCertificateValid leaf632Box leaf632Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi80ValidityFacts
    leaf632LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf632CoverageChecked :
    coverageCheck (innerAD leaf632Box) leaf632InnerLog = true := by
  rfl'

private theorem leaf632InnerLogValid :
    leaf632InnerLog.Valid 8 (innerAD leaf632Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf632CoverageChecked

private noncomputable def leaf632InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907377/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf632InputLogOnePlusV_eq :
    leaf632InputLogOnePlusV = outerEnclosure 24
      (leaf632Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf632RoundedFacts : LeafRoundedFacts 8
    leaf632Certificate.logOnePlusV leaf632InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf632InputLogOnePlusV_eq }

private noncomputable def leaf632Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi80InputQChi innerPair257Input
    leaf632InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf632LowerChecked :
    lowerCheck 24 leaf632Box leaf632Inputs = true := by
  rfl'

private theorem leaf632CoversExact : CoversExact 8
    leaf632Box leaf632Certificate leaf632InnerLog leaf632Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi80RoundedFacts
    innerPair257RoundedFacts leaf632RoundedFacts (by rfl)

private theorem leaf632FlatSound : Sound leaf632Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf632CertificateValid
    leaf632InnerLogValid leaf632CoversExact leaf632LowerChecked

private noncomputable def leaf633Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf633Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554537/33554432) }, vSqrt := { lower := (16383/16384), upper := (79167639/79163392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (75330977/67108864) }, upper := { exponent := 1, mantissa := (601/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (158331031/158326784) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf633InnerLog : WideLogData :=
  innerPair258Data

set_option maxRecDepth 1000000 in
private theorem leaf633LocalValidity :
    LeafFacts leaf633Box leaf633Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf633Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (79167639/79163392) }) = true
      norm_num [leaf633Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf633CertificateValid :
    WideCertificateValid leaf633Box leaf633Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi80ValidityFacts
    leaf633LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf633CoverageChecked :
    coverageCheck (innerAD leaf633Box) leaf633InnerLog = true := by
  rfl'

private theorem leaf633InnerLogValid :
    leaf633InnerLog.Valid 8 (innerAD leaf633Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint77PositiveFacts.valid leaf633CoverageChecked

private noncomputable def leaf633InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf633InputLogOnePlusV_eq :
    leaf633InputLogOnePlusV = outerEnclosure 24
      (leaf633Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf633RoundedFacts : LeafRoundedFacts 8
    leaf633Certificate.logOnePlusV leaf633InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf633InputLogOnePlusV_eq }

private noncomputable def leaf633Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi80InputQChi innerPair258Input
    leaf633InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf633LowerChecked :
    lowerCheck 24 leaf633Box leaf633Inputs = true := by
  rfl'

private theorem leaf633CoversExact : CoversExact 8
    leaf633Box leaf633Certificate leaf633InnerLog leaf633Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi80RoundedFacts
    innerPair258RoundedFacts leaf633RoundedFacts (by rfl)

private theorem leaf633FlatSound : Sound leaf633Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf633CertificateValid
    leaf633InnerLogValid leaf633CoversExact leaf633LowerChecked

private noncomputable def leaf634Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf634Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554537/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178443776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (75724169/67108864) }, upper := { exponent := 1, mantissa := (151/128) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357821439/34356887552) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf634InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf634LocalValidity :
    LeafFacts leaf634Box leaf634Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf634Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178443776) }) = true
      norm_num [leaf634Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf634CertificateValid :
    WideCertificateValid leaf634Box leaf634Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi81ValidityFacts
    leaf634LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf634CoverageChecked :
    coverageCheck (innerAD leaf634Box) leaf634InnerLog = true := by
  rfl'

private theorem leaf634InnerLogValid :
    leaf634InnerLog.Valid 8 (innerAD leaf634Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf634CoverageChecked

private noncomputable def leaf634InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629537/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf634InputLogOnePlusV_eq :
    leaf634InputLogOnePlusV = outerEnclosure 24
      (leaf634Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf634RoundedFacts : LeafRoundedFacts 8
    leaf634Certificate.logOnePlusV leaf634InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf634InputLogOnePlusV_eq }

private noncomputable def leaf634Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi81InputQChi innerPair265Input
    leaf634InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf634LowerChecked :
    lowerCheck 24 leaf634Box leaf634Inputs = true := by
  rfl'

private theorem leaf634CoversExact : CoversExact 8
    leaf634Box leaf634Certificate leaf634InnerLog leaf634Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi81RoundedFacts
    innerPair265RoundedFacts leaf634RoundedFacts (by rfl)

private theorem leaf634FlatSound : Sound leaf634Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf634CertificateValid
    leaf634InnerLogValid leaf634CoversExact leaf634LowerChecked

private noncomputable def leaf635Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf635Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554539/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178394624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (77231403/67108864) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357772287/34356789248) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf635InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf635LocalValidity :
    LeafFacts leaf635Box leaf635Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf635Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178394624) }) = true
      norm_num [leaf635Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf635CertificateValid :
    WideCertificateValid leaf635Box leaf635Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi81ValidityFacts
    leaf635LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf635CoverageChecked :
    coverageCheck (innerAD leaf635Box) leaf635InnerLog = true := by
  rfl'

private theorem leaf635InnerLogValid :
    leaf635InnerLog.Valid 8 (innerAD leaf635Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf635CoverageChecked

private noncomputable def leaf635InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf635InputLogOnePlusV_eq :
    leaf635InputLogOnePlusV = outerEnclosure 24
      (leaf635Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf635RoundedFacts : LeafRoundedFacts 8
    leaf635Certificate.logOnePlusV leaf635InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf635InputLogOnePlusV_eq }

private noncomputable def leaf635Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi81InputQChi innerPair266Input
    leaf635InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf635LowerChecked :
    lowerCheck 24 leaf635Box leaf635Inputs = true := by
  rfl'

private theorem leaf635CoversExact : CoversExact 8
    leaf635Box leaf635Certificate leaf635InnerLog leaf635Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi81RoundedFacts
    innerPair266RoundedFacts leaf635RoundedFacts (by rfl)

private theorem leaf635FlatSound : Sound leaf635Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf635CertificateValid
    leaf635InnerLogValid leaf635CoversExact leaf635LowerChecked

private noncomputable def leaf636Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf636Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554535/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178535936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (72840763/67108864) }, upper := { exponent := 1, mantissa := (1163/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357913599/34357071872) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf636InnerLog : WideLogData :=
  innerPair251Data

set_option maxRecDepth 1000000 in
private theorem leaf636LocalValidity :
    LeafFacts leaf636Box leaf636Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf636Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178535936) }) = true
      norm_num [leaf636Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf636CertificateValid :
    WideCertificateValid leaf636Box leaf636Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi74ValidityFacts
    leaf636LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf636CoverageChecked :
    coverageCheck (innerAD leaf636Box) leaf636InnerLog = true := by
  rfl'

private theorem leaf636InnerLogValid :
    leaf636InnerLog.Valid 8 (innerAD leaf636Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint76PositiveFacts.valid leaf636CoverageChecked

private noncomputable def leaf636InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907373/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf636InputLogOnePlusV_eq :
    leaf636InputLogOnePlusV = outerEnclosure 24
      (leaf636Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf636RoundedFacts : LeafRoundedFacts 8
    leaf636Certificate.logOnePlusV leaf636InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf636InputLogOnePlusV_eq }

private noncomputable def leaf636Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi74InputQChi innerPair251Input
    leaf636InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf636LowerChecked :
    lowerCheck 24 leaf636Box leaf636Inputs = true := by
  rfl'

private theorem leaf636CoversExact : CoversExact 8
    leaf636Box leaf636Certificate leaf636InnerLog leaf636Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi74RoundedFacts
    innerPair251RoundedFacts leaf636RoundedFacts (by rfl)

private theorem leaf636FlatSound : Sound leaf636Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf636CertificateValid
    leaf636InnerLogValid leaf636CoversExact leaf636LowerChecked

private noncomputable def leaf637Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf637Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554537/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178492928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (74151401/67108864) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357870591/34356985856) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf637InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf637LocalValidity :
    LeafFacts leaf637Box leaf637Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf637Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178492928) }) = true
      norm_num [leaf637Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf637CertificateValid :
    WideCertificateValid leaf637Box leaf637Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi74ValidityFacts
    leaf637LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf637CoverageChecked :
    coverageCheck (innerAD leaf637Box) leaf637InnerLog = true := by
  rfl'

private theorem leaf637InnerLogValid :
    leaf637InnerLog.Valid 8 (innerAD leaf637Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf637CoverageChecked

private noncomputable def leaf637InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf637InputLogOnePlusV_eq :
    leaf637InputLogOnePlusV = outerEnclosure 24
      (leaf637Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf637RoundedFacts : LeafRoundedFacts 8
    leaf637Certificate.logOnePlusV leaf637InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf637InputLogOnePlusV_eq }

private noncomputable def leaf637Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi74InputQChi innerPair257Input
    leaf637InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf637LowerChecked :
    lowerCheck 24 leaf637Box leaf637Inputs = true := by
  rfl'

private theorem leaf637CoversExact : CoversExact 8
    leaf637Box leaf637Certificate leaf637InnerLog leaf637Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi74RoundedFacts
    innerPair257RoundedFacts leaf637RoundedFacts (by rfl)

private theorem leaf637FlatSound : Sound leaf637Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf637CertificateValid
    leaf637InnerLogValid leaf637CoversExact leaf637LowerChecked

private noncomputable def leaf638Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf638Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554537/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178472448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (74806721/67108864) }, upper := { exponent := 1, mantissa := (597/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357850111/34356944896) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf638InnerLog : WideLogData :=
  innerPair258Data

set_option maxRecDepth 1000000 in
private theorem leaf638LocalValidity :
    LeafFacts leaf638Box leaf638Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf638Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178472448) }) = true
      norm_num [leaf638Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf638CertificateValid :
    WideCertificateValid leaf638Box leaf638Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi75ValidityFacts
    leaf638LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf638CoverageChecked :
    coverageCheck (innerAD leaf638Box) leaf638InnerLog = true := by
  rfl'

private theorem leaf638InnerLogValid :
    leaf638InnerLog.Valid 8 (innerAD leaf638Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint77PositiveFacts.valid leaf638CoverageChecked

private noncomputable def leaf638InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf638InputLogOnePlusV_eq :
    leaf638InputLogOnePlusV = outerEnclosure 24
      (leaf638Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf638RoundedFacts : LeafRoundedFacts 8
    leaf638Certificate.logOnePlusV leaf638InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf638InputLogOnePlusV_eq }

private noncomputable def leaf638Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi75InputQChi innerPair258Input
    leaf638InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf638LowerChecked :
    lowerCheck 24 leaf638Box leaf638Inputs = true := by
  rfl'

private theorem leaf638CoversExact : CoversExact 8
    leaf638Box leaf638Certificate leaf638InnerLog leaf638Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi75RoundedFacts
    innerPair258RoundedFacts leaf638RoundedFacts (by rfl)

private theorem leaf638FlatSound : Sound leaf638Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf638CertificateValid
    leaf638InnerLogValid leaf638CoversExact leaf638LowerChecked

private noncomputable def leaf639Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf639Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554539/33554432) }, vSqrt := { lower := (65531/65536), upper := (818065603/818020352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (76182891/67108864) }, upper := { exponent := 1, mantissa := (19/16) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1636085955/1636040704) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf639InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf639LocalValidity :
    LeafFacts leaf639Box leaf639Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf639Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (818065603/818020352) }) = true
      norm_num [leaf639Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf639CertificateValid :
    WideCertificateValid leaf639Box leaf639Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi75ValidityFacts
    leaf639LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf639CoverageChecked :
    coverageCheck (innerAD leaf639Box) leaf639InnerLog = true := by
  rfl'

private theorem leaf639InnerLogValid :
    leaf639InnerLog.Valid 8 (innerAD leaf639Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf639CoverageChecked

private noncomputable def leaf639InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf639InputLogOnePlusV_eq :
    leaf639InputLogOnePlusV = outerEnclosure 24
      (leaf639Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf639RoundedFacts : LeafRoundedFacts 8
    leaf639Certificate.logOnePlusV leaf639InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf639InputLogOnePlusV_eq }

private noncomputable def leaf639Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi75InputQChi innerPair265Input
    leaf639InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf639LowerChecked :
    lowerCheck 24 leaf639Box leaf639Inputs = true := by
  rfl'

private theorem leaf639CoversExact : CoversExact 8
    leaf639Box leaf639Certificate leaf639InnerLog leaf639Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi75RoundedFacts
    innerPair265RoundedFacts leaf639RoundedFacts (by rfl)

private theorem leaf639FlatSound : Sound leaf639Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf639CertificateValid
    leaf639InnerLogValid leaf639CoversExact leaf639LowerChecked

private noncomputable def leaf640Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf640Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554539/33554432) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726136320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (76772679/67108864) }, upper := { exponent := 1, mantissa := (1225/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452595541/11452272640) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf640InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf640LocalValidity :
    LeafFacts leaf640Box leaf640Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf640Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726136320) }) = true
      norm_num [leaf640Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf640CertificateValid :
    WideCertificateValid leaf640Box leaf640Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi80ValidityFacts
    leaf640LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf640CoverageChecked :
    coverageCheck (innerAD leaf640Box) leaf640InnerLog = true := by
  rfl'

private theorem leaf640InnerLogValid :
    leaf640InnerLog.Valid 8 (innerAD leaf640Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf640CoverageChecked

private noncomputable def leaf640InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf640InputLogOnePlusV_eq :
    leaf640InputLogOnePlusV = outerEnclosure 24
      (leaf640Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf640RoundedFacts : LeafRoundedFacts 8
    leaf640Certificate.logOnePlusV leaf640InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf640InputLogOnePlusV_eq }

private noncomputable def leaf640Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi80InputQChi innerPair266Input
    leaf640InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf640LowerChecked :
    lowerCheck 24 leaf640Box leaf640Inputs = true := by
  rfl'

private theorem leaf640CoversExact : CoversExact 8
    leaf640Box leaf640Certificate leaf640InnerLog leaf640Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi80RoundedFacts
    innerPair266RoundedFacts leaf640RoundedFacts (by rfl)

private theorem leaf640FlatSound : Sound leaf640Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf640CertificateValid
    leaf640InnerLogValid leaf640CoversExact leaf640LowerChecked

private noncomputable def leaf641Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf641Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554541/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178361856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (78214381/67108864) }, upper := { exponent := 1, mantissa := (39/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357739519/34356723712) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf641InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf641LocalValidity :
    LeafFacts leaf641Box leaf641Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf641Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178361856) }) = true
      norm_num [leaf641Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf641CertificateValid :
    WideCertificateValid leaf641Box leaf641Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi80ValidityFacts
    leaf641LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf641CoverageChecked :
    coverageCheck (innerAD leaf641Box) leaf641InnerLog = true := by
  rfl'

private theorem leaf641InnerLogValid :
    leaf641InnerLog.Valid 8 (innerAD leaf641Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf641CoverageChecked

private noncomputable def leaf641InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf641InputLogOnePlusV_eq :
    leaf641InputLogOnePlusV = outerEnclosure 24
      (leaf641Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf641RoundedFacts : LeafRoundedFacts 8
    leaf641Certificate.logOnePlusV leaf641InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf641InputLogOnePlusV_eq }

private noncomputable def leaf641Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi80InputQChi innerPair273Input
    leaf641InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf641LowerChecked :
    lowerCheck 24 leaf641Box leaf641Inputs = true := by
  rfl'

private theorem leaf641CoversExact : CoversExact 8
    leaf641Box leaf641Certificate leaf641InnerLog leaf641Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi80RoundedFacts
    innerPair273RoundedFacts leaf641RoundedFacts (by rfl)

private theorem leaf641FlatSound : Sound leaf641Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf641CertificateValid
    leaf641InnerLogValid leaf641CoversExact leaf641LowerChecked

private noncomputable def leaf642Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf642Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554541/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178345472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (78738637/67108864) }, upper := { exponent := 1, mantissa := (157/128) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34357723135/34356690944) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf642InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf642LocalValidity :
    LeafFacts leaf642Box leaf642Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf642Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178345472) }) = true
      norm_num [leaf642Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf642CertificateValid :
    WideCertificateValid leaf642Box leaf642Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi81ValidityFacts
    leaf642LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf642CoverageChecked :
    coverageCheck (innerAD leaf642Box) leaf642InnerLog = true := by
  rfl'

private theorem leaf642InnerLogValid :
    leaf642InnerLog.Valid 8 (innerAD leaf642Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf642CoverageChecked

private noncomputable def leaf642InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf642InputLogOnePlusV_eq :
    leaf642InputLogOnePlusV = outerEnclosure 24
      (leaf642Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf642RoundedFacts : LeafRoundedFacts 8
    leaf642Certificate.logOnePlusV leaf642InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf642InputLogOnePlusV_eq }

private noncomputable def leaf642Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi81InputQChi innerPair274Input
    leaf642InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf642LowerChecked :
    lowerCheck 24 leaf642Box leaf642Inputs = true := by
  rfl'

private theorem leaf642CoversExact : CoversExact 8
    leaf642Box leaf642Certificate leaf642InnerLog leaf642Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi81RoundedFacts
    innerPair274RoundedFacts leaf642RoundedFacts (by rfl)

private theorem leaf642FlatSound : Sound leaf642Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf642CertificateValid
    leaf642InnerLogValid leaf642CoversExact leaf642LowerChecked

private noncomputable def leaf643Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf643Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554543/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356592640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (80245871/67108864) }, upper := { exponent := 1, mantissa := (5/4) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714823677/68713185280) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf643InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf643LocalValidity :
    LeafFacts leaf643Box leaf643Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf643Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356592640) }) = true
      norm_num [leaf643Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf643CertificateValid :
    WideCertificateValid leaf643Box leaf643Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi81ValidityFacts
    leaf643LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf643CoverageChecked :
    coverageCheck (innerAD leaf643Box) leaf643InnerLog = true := by
  rfl'

private theorem leaf643InnerLogValid :
    leaf643InnerLog.Valid 8 (innerAD leaf643Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf643CoverageChecked

private noncomputable def leaf643InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf643InputLogOnePlusV_eq :
    leaf643InputLogOnePlusV = outerEnclosure 24
      (leaf643Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf643RoundedFacts : LeafRoundedFacts 8
    leaf643Certificate.logOnePlusV leaf643InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf643InputLogOnePlusV_eq }

private noncomputable def leaf643Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi81InputQChi innerPair279Input
    leaf643InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf643LowerChecked :
    lowerCheck 24 leaf643Box leaf643Inputs = true := by
  rfl'

private theorem leaf643CoversExact : CoversExact 8
    leaf643Box leaf643Certificate leaf643InnerLog leaf643Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi81RoundedFacts
    innerPair279RoundedFacts leaf643RoundedFacts (by rfl)

private theorem leaf643FlatSound : Sound leaf643Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf643CertificateValid
    leaf643InnerLogValid leaf643CoversExact leaf643LowerChecked

private noncomputable def component15Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node0_sound : Sound component15Node0Box :=
  sound_of_literal_split component15Node0Box leaf605Box leaf606Box
    .chi (33/64) (by rfl) (by rfl)
    leaf605FlatSound leaf606FlatSound

private noncomputable def component15Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node1_sound : Sound component15Node1Box :=
  sound_of_literal_split component15Node1Box leaf607Box leaf608Box
    .chi (33/64) (by rfl) (by rfl)
    leaf607FlatSound leaf608FlatSound

private noncomputable def component15Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node2_sound : Sound component15Node2Box :=
  sound_of_literal_split component15Node2Box component15Node0Box component15Node1Box
    .k (29/16) (by rfl) (by rfl)
    component15Node0_sound component15Node1_sound

private noncomputable def component15Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node3_sound : Sound component15Node3Box :=
  sound_of_literal_split component15Node3Box leaf609Box leaf610Box
    .k (29/16) (by rfl) (by rfl)
    leaf609FlatSound leaf610FlatSound

private noncomputable def component15Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node4_sound : Sound component15Node4Box :=
  sound_of_literal_split component15Node4Box component15Node2Box component15Node3Box
    .chi (17/32) (by rfl) (by rfl)
    component15Node2_sound component15Node3_sound

private noncomputable def component15Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node5_sound : Sound component15Node5Box :=
  sound_of_literal_split component15Node5Box leaf611Box leaf612Box
    .chi (33/64) (by rfl) (by rfl)
    leaf611FlatSound leaf612FlatSound

private noncomputable def component15Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node6_sound : Sound component15Node6Box :=
  sound_of_literal_split component15Node6Box leaf613Box leaf614Box
    .chi (33/64) (by rfl) (by rfl)
    leaf613FlatSound leaf614FlatSound

private noncomputable def component15Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node7_sound : Sound component15Node7Box :=
  sound_of_literal_split component15Node7Box component15Node5Box component15Node6Box
    .k (31/16) (by rfl) (by rfl)
    component15Node5_sound component15Node6_sound

private noncomputable def component15Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node8_sound : Sound component15Node8Box :=
  sound_of_literal_split component15Node8Box leaf615Box leaf616Box
    .chi (35/64) (by rfl) (by rfl)
    leaf615FlatSound leaf616FlatSound

private noncomputable def component15Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node9_sound : Sound component15Node9Box :=
  sound_of_literal_split component15Node9Box leaf617Box leaf618Box
    .chi (35/64) (by rfl) (by rfl)
    leaf617FlatSound leaf618FlatSound

private noncomputable def component15Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node10_sound : Sound component15Node10Box :=
  sound_of_literal_split component15Node10Box component15Node8Box component15Node9Box
    .k (31/16) (by rfl) (by rfl)
    component15Node8_sound component15Node9_sound

private noncomputable def component15Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node11_sound : Sound component15Node11Box :=
  sound_of_literal_split component15Node11Box component15Node7Box component15Node10Box
    .chi (17/32) (by rfl) (by rfl)
    component15Node7_sound component15Node10_sound

private noncomputable def component15Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node12_sound : Sound component15Node12Box :=
  sound_of_literal_split component15Node12Box component15Node4Box component15Node11Box
    .k (15/8) (by rfl) (by rfl)
    component15Node4_sound component15Node11_sound

private noncomputable def component15Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node13_sound : Sound component15Node13Box :=
  sound_of_literal_split component15Node13Box leaf619Box leaf620Box
    .k (29/16) (by rfl) (by rfl)
    leaf619FlatSound leaf620FlatSound

private noncomputable def component15Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component15Node14_sound : Sound component15Node14Box :=
  sound_of_literal_split component15Node14Box leaf621Box leaf622Box
    .k (29/16) (by rfl) (by rfl)
    leaf621FlatSound leaf622FlatSound

private noncomputable def component15Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component15Node15_sound : Sound component15Node15Box :=
  sound_of_literal_split component15Node15Box component15Node13Box component15Node14Box
    .chi (19/32) (by rfl) (by rfl)
    component15Node13_sound component15Node14_sound

private noncomputable def component15Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node16_sound : Sound component15Node16Box :=
  sound_of_literal_split component15Node16Box leaf624Box leaf625Box
    .chi (37/64) (by rfl) (by rfl)
    leaf624FlatSound leaf625FlatSound

private noncomputable def component15Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node17_sound : Sound component15Node17Box :=
  sound_of_literal_split component15Node17Box leaf623Box component15Node16Box
    .k (31/16) (by rfl) (by rfl)
    leaf623FlatSound component15Node16_sound

private noncomputable def component15Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component15Node18_sound : Sound component15Node18Box :=
  sound_of_literal_split component15Node18Box leaf626Box leaf627Box
    .k (31/16) (by rfl) (by rfl)
    leaf626FlatSound leaf627FlatSound

private noncomputable def component15Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component15Node19_sound : Sound component15Node19Box :=
  sound_of_literal_split component15Node19Box component15Node17Box component15Node18Box
    .chi (19/32) (by rfl) (by rfl)
    component15Node17_sound component15Node18_sound

private noncomputable def component15Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component15Node20_sound : Sound component15Node20Box :=
  sound_of_literal_split component15Node20Box component15Node15Box component15Node19Box
    .k (15/8) (by rfl) (by rfl)
    component15Node15_sound component15Node19_sound

private noncomputable def component15Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component15Node21_sound : Sound component15Node21Box :=
  sound_of_literal_split component15Node21Box component15Node12Box component15Node20Box
    .chi (9/16) (by rfl) (by rfl)
    component15Node12_sound component15Node20_sound

private noncomputable def component15Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node22_sound : Sound component15Node22Box :=
  sound_of_literal_split component15Node22Box leaf628Box leaf629Box
    .k (29/16) (by rfl) (by rfl)
    leaf628FlatSound leaf629FlatSound

private noncomputable def component15Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node23_sound : Sound component15Node23Box :=
  sound_of_literal_split component15Node23Box leaf630Box leaf631Box
    .k (29/16) (by rfl) (by rfl)
    leaf630FlatSound leaf631FlatSound

private noncomputable def component15Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node24_sound : Sound component15Node24Box :=
  sound_of_literal_split component15Node24Box component15Node22Box component15Node23Box
    .chi (21/32) (by rfl) (by rfl)
    component15Node22_sound component15Node23_sound

private noncomputable def component15Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node25_sound : Sound component15Node25Box :=
  sound_of_literal_split component15Node25Box leaf632Box leaf633Box
    .k (29/16) (by rfl) (by rfl)
    leaf632FlatSound leaf633FlatSound

private noncomputable def component15Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component15Node26_sound : Sound component15Node26Box :=
  sound_of_literal_split component15Node26Box leaf634Box leaf635Box
    .k (29/16) (by rfl) (by rfl)
    leaf634FlatSound leaf635FlatSound

private noncomputable def component15Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component15Node27_sound : Sound component15Node27Box :=
  sound_of_literal_split component15Node27Box component15Node25Box component15Node26Box
    .chi (23/32) (by rfl) (by rfl)
    component15Node25_sound component15Node26_sound

private noncomputable def component15Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component15Node28_sound : Sound component15Node28Box :=
  sound_of_literal_split component15Node28Box component15Node24Box component15Node27Box
    .chi (11/16) (by rfl) (by rfl)
    component15Node24_sound component15Node27_sound

private noncomputable def component15Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node29_sound : Sound component15Node29Box :=
  sound_of_literal_split component15Node29Box leaf636Box leaf637Box
    .k (31/16) (by rfl) (by rfl)
    leaf636FlatSound leaf637FlatSound

private noncomputable def component15Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node30_sound : Sound component15Node30Box :=
  sound_of_literal_split component15Node30Box leaf638Box leaf639Box
    .k (31/16) (by rfl) (by rfl)
    leaf638FlatSound leaf639FlatSound

private noncomputable def component15Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component15Node31_sound : Sound component15Node31Box :=
  sound_of_literal_split component15Node31Box component15Node29Box component15Node30Box
    .chi (21/32) (by rfl) (by rfl)
    component15Node29_sound component15Node30_sound

private noncomputable def component15Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component15Node32_sound : Sound component15Node32Box :=
  sound_of_literal_split component15Node32Box leaf640Box leaf641Box
    .k (31/16) (by rfl) (by rfl)
    leaf640FlatSound leaf641FlatSound

private noncomputable def component15Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component15Node33_sound : Sound component15Node33Box :=
  sound_of_literal_split component15Node33Box leaf642Box leaf643Box
    .k (31/16) (by rfl) (by rfl)
    leaf642FlatSound leaf643FlatSound

private noncomputable def component15Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component15Node34_sound : Sound component15Node34Box :=
  sound_of_literal_split component15Node34Box component15Node32Box component15Node33Box
    .chi (23/32) (by rfl) (by rfl)
    component15Node32_sound component15Node33_sound

private noncomputable def component15Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component15Node35_sound : Sound component15Node35Box :=
  sound_of_literal_split component15Node35Box component15Node31Box component15Node34Box
    .chi (11/16) (by rfl) (by rfl)
    component15Node31_sound component15Node34_sound

private noncomputable def component15Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component15Node36_sound : Sound component15Node36Box :=
  sound_of_literal_split component15Node36Box component15Node28Box component15Node35Box
    .k (15/8) (by rfl) (by rfl)
    component15Node28_sound component15Node35_sound

noncomputable def component15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component15_sound : Sound component15Box :=
  sound_of_literal_split component15Box component15Node21Box component15Node36Box
    .chi (5/8) (by rfl) (by rfl)
    component15Node21_sound component15Node36_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
