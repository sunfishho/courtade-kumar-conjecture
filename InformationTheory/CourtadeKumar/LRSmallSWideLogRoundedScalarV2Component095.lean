import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2

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

private noncomputable def leaf4603Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4603Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908214784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (545209575/536870912) }, upper := { exponent := 1, mantissa := (8461/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816603721/9816429568) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4603InnerLog : WideLogData :=
  innerPair547Data

set_option maxRecDepth 1000000 in
private theorem leaf4603LocalValidity :
    LeafFacts leaf4603Box leaf4603Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4603Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908214784) }) = true
      norm_num [leaf4603Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4603CertificateValid :
    WideCertificateValid leaf4603Box leaf4603Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi253ValidityFacts
    leaf4603LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4603CoverageChecked :
    coverageCheck (innerAD leaf4603Box) leaf4603InnerLog = true := by
  rfl'

private theorem leaf4603InnerLogValid :
    leaf4603InnerLog.Valid 8 (innerAD leaf4603Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint86PositiveFacts.valid leaf4603CoverageChecked

private noncomputable def leaf4603InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4603InputLogOnePlusV_eq :
    leaf4603InputLogOnePlusV = outerEnclosure 24
      (leaf4603Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4603RoundedFacts : LeafRoundedFacts 8
    leaf4603Certificate.logOnePlusV leaf4603InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4603InputLogOnePlusV_eq }

private noncomputable def leaf4603Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi253InputQChi innerPair547Input
    leaf4603InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4603LowerChecked :
    lowerCheck 24 leaf4603Box leaf4603Inputs = true := by
  rfl'

private theorem leaf4603CoversExact : CoversExact 8
    leaf4603Box leaf4603Certificate leaf4603InnerLog leaf4603Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi253RoundedFacts
    innerPair547RoundedFacts leaf4603RoundedFacts (by rfl)

private theorem leaf4603FlatSound : Sound leaf4603Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4603CertificateValid
    leaf4603InnerLogValid leaf4603CoversExact leaf4603LowerChecked

private noncomputable def leaf4604Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4604Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357480448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (548092981/536870912) }, upper := { exponent := 1, mantissa := (4253/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716203007/68714960896) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4604InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4604LocalValidity :
    LeafFacts leaf4604Box leaf4604Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4604Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357480448) }) = true
      norm_num [leaf4604Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4604CertificateValid :
    WideCertificateValid leaf4604Box leaf4604Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi253ValidityFacts
    leaf4604LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4604CoverageChecked :
    coverageCheck (innerAD leaf4604Box) leaf4604InnerLog = true := by
  rfl'

private theorem leaf4604InnerLogValid :
    leaf4604InnerLog.Valid 8 (innerAD leaf4604Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4604CoverageChecked

private noncomputable def leaf4604InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4604InputLogOnePlusV_eq :
    leaf4604InputLogOnePlusV = outerEnclosure 24
      (leaf4604Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4604RoundedFacts : LeafRoundedFacts 8
    leaf4604Certificate.logOnePlusV leaf4604InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4604InputLogOnePlusV_eq }

private noncomputable def leaf4604Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi253InputQChi innerPair311Input
    leaf4604InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4604LowerChecked :
    lowerCheck 24 leaf4604Box leaf4604Inputs = true := by
  rfl'

private theorem leaf4604CoversExact : CoversExact 8
    leaf4604Box leaf4604Certificate leaf4604InnerLog leaf4604Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi253RoundedFacts
    innerPair311RoundedFacts leaf4604RoundedFacts (by rfl)

private theorem leaf4604FlatSound : Sound leaf4604Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4604CertificateValid
    leaf4604InnerLogValid leaf4604CoversExact leaf4604LowerChecked

private noncomputable def leaf4605Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4605Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357453824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (551500645/536870912) }, upper := { exponent := 1, mantissa := (4279/4096) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716176383/68714907648) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4605InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4605LocalValidity :
    LeafFacts leaf4605Box leaf4605Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4605Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357453824) }) = true
      norm_num [leaf4605Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4605CertificateValid :
    WideCertificateValid leaf4605Box leaf4605Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi254ValidityFacts
    leaf4605LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4605CoverageChecked :
    coverageCheck (innerAD leaf4605Box) leaf4605InnerLog = true := by
  rfl'

private theorem leaf4605InnerLogValid :
    leaf4605InnerLog.Valid 8 (innerAD leaf4605Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4605CoverageChecked

private noncomputable def leaf4605InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4605InputLogOnePlusV_eq :
    leaf4605InputLogOnePlusV = outerEnclosure 24
      (leaf4605Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4605RoundedFacts : LeafRoundedFacts 8
    leaf4605Certificate.logOnePlusV leaf4605InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4605InputLogOnePlusV_eq }

private noncomputable def leaf4605Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi254InputQChi innerPair117Input
    leaf4605InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4605LowerChecked :
    lowerCheck 24 leaf4605Box leaf4605Inputs = true := by
  rfl'

private theorem leaf4605CoversExact : CoversExact 8
    leaf4605Box leaf4605Certificate leaf4605InnerLog leaf4605Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi254RoundedFacts
    innerPair117RoundedFacts leaf4605RoundedFacts (by rfl)

private theorem leaf4605FlatSound : Sound leaf4605Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4605CertificateValid
    leaf4605InnerLogValid leaf4605CoversExact leaf4605LowerChecked

private noncomputable def leaf4606Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4606Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357430272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (554449583/536870912) }, upper := { exponent := 1, mantissa := (2151/2048) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716152831/68714860544) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4606InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4606LocalValidity :
    LeafFacts leaf4606Box leaf4606Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4606Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357430272) }) = true
      norm_num [leaf4606Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4606CertificateValid :
    WideCertificateValid leaf4606Box leaf4606Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi254ValidityFacts
    leaf4606LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4606CoverageChecked :
    coverageCheck (innerAD leaf4606Box) leaf4606InnerLog = true := by
  rfl'

private theorem leaf4606InnerLogValid :
    leaf4606InnerLog.Valid 8 (innerAD leaf4606Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4606CoverageChecked

private noncomputable def leaf4606InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4606InputLogOnePlusV_eq :
    leaf4606InputLogOnePlusV = outerEnclosure 24
      (leaf4606Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4606RoundedFacts : LeafRoundedFacts 8
    leaf4606Certificate.logOnePlusV leaf4606InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4606InputLogOnePlusV_eq }

private noncomputable def leaf4606Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi254InputQChi innerPair242Input
    leaf4606InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4606LowerChecked :
    lowerCheck 24 leaf4606Box leaf4606Inputs = true := by
  rfl'

private theorem leaf4606CoversExact : CoversExact 8
    leaf4606Box leaf4606Certificate leaf4606InnerLog leaf4606Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi254RoundedFacts
    innerPair242RoundedFacts leaf4606RoundedFacts (by rfl)

private theorem leaf4606FlatSound : Sound leaf4606Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4606CertificateValid
    leaf4606InnerLogValid leaf4606CoversExact leaf4606LowerChecked

private noncomputable def leaf4607Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4607Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357457408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (550976387/536870912) }, upper := { exponent := 1, mantissa := (8551/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716179967/68714914816) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4607InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf4607LocalValidity :
    LeafFacts leaf4607Box leaf4607Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4607Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357457408) }) = true
      norm_num [leaf4607Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4607CertificateValid :
    WideCertificateValid leaf4607Box leaf4607Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi253ValidityFacts
    leaf4607LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4607CoverageChecked :
    coverageCheck (innerAD leaf4607Box) leaf4607InnerLog = true := by
  rfl'

private theorem leaf4607InnerLogValid :
    leaf4607InnerLog.Valid 8 (innerAD leaf4607Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf4607CoverageChecked

private noncomputable def leaf4607InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4607InputLogOnePlusV_eq :
    leaf4607InputLogOnePlusV = outerEnclosure 24
      (leaf4607Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4607RoundedFacts : LeafRoundedFacts 8
    leaf4607Certificate.logOnePlusV leaf4607InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4607InputLogOnePlusV_eq }

private noncomputable def leaf4607Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi253InputQChi innerPair329Input
    leaf4607InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4607LowerChecked :
    lowerCheck 24 leaf4607Box leaf4607Inputs = true := by
  rfl'

private theorem leaf4607CoversExact : CoversExact 8
    leaf4607Box leaf4607Certificate leaf4607InnerLog leaf4607Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi253RoundedFacts
    innerPair329RoundedFacts leaf4607RoundedFacts (by rfl)

private theorem leaf4607FlatSound : Sound leaf4607Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4607CertificateValid
    leaf4607InnerLogValid leaf4607CoversExact leaf4607LowerChecked

private noncomputable def leaf4608Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4608Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357434368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (553859793/536870912) }, upper := { exponent := 1, mantissa := (2149/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716156927/68714868736) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4608InnerLog : WideLogData :=
  innerPair247Data

set_option maxRecDepth 1000000 in
private theorem leaf4608LocalValidity :
    LeafFacts leaf4608Box leaf4608Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4608Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357434368) }) = true
      norm_num [leaf4608Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4608CertificateValid :
    WideCertificateValid leaf4608Box leaf4608Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi253ValidityFacts
    leaf4608LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4608CoverageChecked :
    coverageCheck (innerAD leaf4608Box) leaf4608InnerLog = true := by
  rfl'

private theorem leaf4608InnerLogValid :
    leaf4608InnerLog.Valid 8 (innerAD leaf4608Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint89PositiveFacts.valid leaf4608CoverageChecked

private noncomputable def leaf4608InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4608InputLogOnePlusV_eq :
    leaf4608InputLogOnePlusV = outerEnclosure 24
      (leaf4608Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4608RoundedFacts : LeafRoundedFacts 8
    leaf4608Certificate.logOnePlusV leaf4608InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4608InputLogOnePlusV_eq }

private noncomputable def leaf4608Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi253InputQChi innerPair247Input
    leaf4608InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4608LowerChecked :
    lowerCheck 24 leaf4608Box leaf4608Inputs = true := by
  rfl'

private theorem leaf4608CoversExact : CoversExact 8
    leaf4608Box leaf4608Certificate leaf4608InnerLog leaf4608Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi253RoundedFacts
    innerPair247RoundedFacts leaf4608RoundedFacts (by rfl)

private theorem leaf4608FlatSound : Sound leaf4608Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4608CertificateValid
    leaf4608InnerLogValid leaf4608CoversExact leaf4608LowerChecked

private noncomputable def leaf4609Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4609Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908200960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (557398521/536870912) }, upper := { exponent := 1, mantissa := (4325/4096) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816589897/9816401920) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4609InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4609LocalValidity :
    LeafFacts leaf4609Box leaf4609Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4609Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908200960) }) = true
      norm_num [leaf4609Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4609CertificateValid :
    WideCertificateValid leaf4609Box leaf4609Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi254ValidityFacts
    leaf4609LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4609CoverageChecked :
    coverageCheck (innerAD leaf4609Box) leaf4609InnerLog = true := by
  rfl'

private theorem leaf4609InnerLogValid :
    leaf4609InnerLog.Valid 8 (innerAD leaf4609Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4609CoverageChecked

private noncomputable def leaf4609InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4609InputLogOnePlusV_eq :
    leaf4609InputLogOnePlusV = outerEnclosure 24
      (leaf4609Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4609RoundedFacts : LeafRoundedFacts 8
    leaf4609Certificate.logOnePlusV leaf4609InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4609InputLogOnePlusV_eq }

private noncomputable def leaf4609Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi254InputQChi innerPair242Input
    leaf4609InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4609LowerChecked :
    lowerCheck 24 leaf4609Box leaf4609Inputs = true := by
  rfl'

private theorem leaf4609CoversExact : CoversExact 8
    leaf4609Box leaf4609Certificate leaf4609InnerLog leaf4609Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi254RoundedFacts
    innerPair242RoundedFacts leaf4609RoundedFacts (by rfl)

private theorem leaf4609FlatSound : Sound leaf4609Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4609CertificateValid
    leaf4609InnerLogValid leaf4609CoversExact leaf4609LowerChecked

private noncomputable def leaf4610Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4610Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357383168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (560347459/536870912) }, upper := { exponent := 1, mantissa := (1087/1024) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716105727/68714766336) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4610InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4610LocalValidity :
    LeafFacts leaf4610Box leaf4610Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4610Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357383168) }) = true
      norm_num [leaf4610Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4610CertificateValid :
    WideCertificateValid leaf4610Box leaf4610Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi254ValidityFacts
    leaf4610LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4610CoverageChecked :
    coverageCheck (innerAD leaf4610Box) leaf4610InnerLog = true := by
  rfl'

private theorem leaf4610InnerLogValid :
    leaf4610InnerLog.Valid 8 (innerAD leaf4610Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4610CoverageChecked

private noncomputable def leaf4610InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4610InputLogOnePlusV_eq :
    leaf4610InputLogOnePlusV = outerEnclosure 24
      (leaf4610Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4610RoundedFacts : LeafRoundedFacts 8
    leaf4610Certificate.logOnePlusV leaf4610InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4610InputLogOnePlusV_eq }

private noncomputable def leaf4610Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi254InputQChi innerPair242Input
    leaf4610InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4610LowerChecked :
    lowerCheck 24 leaf4610Box leaf4610Inputs = true := by
  rfl'

private theorem leaf4610CoversExact : CoversExact 8
    leaf4610Box leaf4610Certificate leaf4610InnerLog leaf4610Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi254RoundedFacts
    innerPair242RoundedFacts leaf4610RoundedFacts (by rfl)

private theorem leaf4610FlatSound : Sound leaf4610Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4610CertificateValid
    leaf4610InnerLogValid leaf4610CoversExact leaf4610LowerChecked

private noncomputable def leaf4611Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4611Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108303360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (557791715/536870912) }, upper := { exponent := 1, mantissa := (8655/8192) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216649249/2216606720) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4611InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4611LocalValidity :
    LeafFacts leaf4611Box leaf4611Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4611Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108303360) }) = true
      norm_num [leaf4611Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4611CertificateValid :
    WideCertificateValid leaf4611Box leaf4611Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi255ValidityFacts
    leaf4611LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4611CoverageChecked :
    coverageCheck (innerAD leaf4611Box) leaf4611InnerLog = true := by
  rfl'

private theorem leaf4611InnerLogValid :
    leaf4611InnerLog.Valid 8 (innerAD leaf4611Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4611CoverageChecked

private noncomputable def leaf4611InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4611InputLogOnePlusV_eq :
    leaf4611InputLogOnePlusV = outerEnclosure 24
      (leaf4611Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4611RoundedFacts : LeafRoundedFacts 8
    leaf4611Certificate.logOnePlusV leaf4611InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4611InputLogOnePlusV_eq }

private noncomputable def leaf4611Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi255InputQChi innerPair242Input
    leaf4611InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4611LowerChecked :
    lowerCheck 24 leaf4611Box leaf4611Inputs = true := by
  rfl'

private theorem leaf4611CoversExact : CoversExact 8
    leaf4611Box leaf4611Certificate leaf4611InnerLog leaf4611Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi255RoundedFacts
    innerPair242RoundedFacts leaf4611RoundedFacts (by rfl)

private theorem leaf4611FlatSound : Sound leaf4611Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4611CertificateValid
    leaf4611InnerLogValid leaf4611CoversExact leaf4611LowerChecked

private noncomputable def leaf4612Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4612Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357380096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (560806185/536870912) }, upper := { exponent := 1, mantissa := (4351/4096) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716102655/68714760192) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4612InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4612LocalValidity :
    LeafFacts leaf4612Box leaf4612Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4612Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357380096) }) = true
      norm_num [leaf4612Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4612CertificateValid :
    WideCertificateValid leaf4612Box leaf4612Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi255ValidityFacts
    leaf4612LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4612CoverageChecked :
    coverageCheck (innerAD leaf4612Box) leaf4612InnerLog = true := by
  rfl'

private theorem leaf4612InnerLogValid :
    leaf4612InnerLog.Valid 8 (innerAD leaf4612Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4612CoverageChecked

private noncomputable def leaf4612InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4612InputLogOnePlusV_eq :
    leaf4612InputLogOnePlusV = outerEnclosure 24
      (leaf4612Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4612RoundedFacts : LeafRoundedFacts 8
    leaf4612Certificate.logOnePlusV leaf4612InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4612InputLogOnePlusV_eq }

private noncomputable def leaf4612Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi255InputQChi innerPair242Input
    leaf4612InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4612LowerChecked :
    lowerCheck 24 leaf4612Box leaf4612Inputs = true := by
  rfl'

private theorem leaf4612CoversExact : CoversExact 8
    leaf4612Box leaf4612Certificate leaf4612InnerLog leaf4612Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi255RoundedFacts
    innerPair242RoundedFacts leaf4612RoundedFacts (by rfl)

private theorem leaf4612FlatSound : Sound leaf4612Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4612CertificateValid
    leaf4612InnerLogValid leaf4612CoversExact leaf4612LowerChecked

private noncomputable def leaf4613Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4613Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357354496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (564082785/536870912) }, upper := { exponent := 1, mantissa := (547/512) } }, logOuter := sk133LogOuterCertificate, logK := sk133LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716077055/68714708992) } }, logDArg := sk133LogDArgCertificate }

private noncomputable def leaf4613InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4613LocalValidity :
    LeafFacts leaf4613Box leaf4613Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4613Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357354496) }) = true
      norm_num [leaf4613Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4613CertificateValid :
    WideCertificateValid leaf4613Box leaf4613Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk133ValidityFacts chi256ValidityFacts
    leaf4613LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4613CoverageChecked :
    coverageCheck (innerAD leaf4613Box) leaf4613InnerLog = true := by
  rfl'

private theorem leaf4613InnerLogValid :
    leaf4613InnerLog.Valid 8 (innerAD leaf4613Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4613CoverageChecked

private noncomputable def leaf4613InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4613InputLogOnePlusV_eq :
    leaf4613InputLogOnePlusV = outerEnclosure 24
      (leaf4613Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4613RoundedFacts : LeafRoundedFacts 8
    leaf4613Certificate.logOnePlusV leaf4613InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4613InputLogOnePlusV_eq }

private noncomputable def leaf4613Inputs : Inputs :=
  inputsOfCaches globalInput sk133RoundedInputs
    chi256InputQChi innerPair243Input
    leaf4613InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4613LowerChecked :
    lowerCheck 24 leaf4613Box leaf4613Inputs = true := by
  rfl'

private theorem leaf4613CoversExact : CoversExact 8
    leaf4613Box leaf4613Certificate leaf4613InnerLog leaf4613Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk133RoundedFacts chi256RoundedFacts
    innerPair243RoundedFacts leaf4613RoundedFacts (by rfl)

private theorem leaf4613FlatSound : Sound leaf4613Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4613CertificateValid
    leaf4613InnerLogValid leaf4613CoversExact leaf4613LowerChecked

private noncomputable def leaf4614Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4614Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357329920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (567162787/536870912) }, upper := { exponent := 1, mantissa := (275/256) } }, logOuter := sk134LogOuterCertificate, logK := sk134LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716052479/68714659840) } }, logDArg := sk134LogDArgCertificate }

private noncomputable def leaf4614InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4614LocalValidity :
    LeafFacts leaf4614Box leaf4614Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4614Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357329920) }) = true
      norm_num [leaf4614Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4614CertificateValid :
    WideCertificateValid leaf4614Box leaf4614Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk134ValidityFacts chi256ValidityFacts
    leaf4614LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4614CoverageChecked :
    coverageCheck (innerAD leaf4614Box) leaf4614InnerLog = true := by
  rfl'

private theorem leaf4614InnerLogValid :
    leaf4614InnerLog.Valid 8 (innerAD leaf4614Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4614CoverageChecked

private noncomputable def leaf4614InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4614InputLogOnePlusV_eq :
    leaf4614InputLogOnePlusV = outerEnclosure 24
      (leaf4614Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4614RoundedFacts : LeafRoundedFacts 8
    leaf4614Certificate.logOnePlusV leaf4614InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4614InputLogOnePlusV_eq }

private noncomputable def leaf4614Inputs : Inputs :=
  inputsOfCaches globalInput sk134RoundedInputs
    chi256InputQChi innerPair243Input
    leaf4614InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4614LowerChecked :
    lowerCheck 24 leaf4614Box leaf4614Inputs = true := by
  rfl'

private theorem leaf4614CoversExact : CoversExact 8
    leaf4614Box leaf4614Certificate leaf4614InnerLog leaf4614Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk134RoundedFacts chi256RoundedFacts
    innerPair243RoundedFacts leaf4614RoundedFacts (by rfl)

private theorem leaf4614FlatSound : Sound leaf4614Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4614CertificateValid
    leaf4614InnerLogValid leaf4614CoversExact leaf4614LowerChecked

private noncomputable def leaf4615Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4615Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357356032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (563820655/536870912) }, upper := { exponent := 1, mantissa := (8749/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716078591/68714712064) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4615InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4615LocalValidity :
    LeafFacts leaf4615Box leaf4615Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4615Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357356032) }) = true
      norm_num [leaf4615Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4615CertificateValid :
    WideCertificateValid leaf4615Box leaf4615Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi255ValidityFacts
    leaf4615LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4615CoverageChecked :
    coverageCheck (innerAD leaf4615Box) leaf4615InnerLog = true := by
  rfl'

private theorem leaf4615InnerLogValid :
    leaf4615InnerLog.Valid 8 (innerAD leaf4615Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4615CoverageChecked

private noncomputable def leaf4615InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4615InputLogOnePlusV_eq :
    leaf4615InputLogOnePlusV = outerEnclosure 24
      (leaf4615Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4615RoundedFacts : LeafRoundedFacts 8
    leaf4615Certificate.logOnePlusV leaf4615InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4615InputLogOnePlusV_eq }

private noncomputable def leaf4615Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi255InputQChi innerPair551Input
    leaf4615InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4615LowerChecked :
    lowerCheck 24 leaf4615Box leaf4615Inputs = true := by
  rfl'

private theorem leaf4615CoversExact : CoversExact 8
    leaf4615Box leaf4615Certificate leaf4615InnerLog leaf4615Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi255RoundedFacts
    innerPair551RoundedFacts leaf4615RoundedFacts (by rfl)

private theorem leaf4615FlatSound : Sound leaf4615Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4615CertificateValid
    leaf4615InnerLogValid leaf4615CoversExact leaf4615LowerChecked

private noncomputable def leaf4616Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4616Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357331968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (566835125/536870912) }, upper := { exponent := 1, mantissa := (2199/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716054527/68714663936) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4616InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf4616LocalValidity :
    LeafFacts leaf4616Box leaf4616Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4616Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357331968) }) = true
      norm_num [leaf4616Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4616CertificateValid :
    WideCertificateValid leaf4616Box leaf4616Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi255ValidityFacts
    leaf4616LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4616CoverageChecked :
    coverageCheck (innerAD leaf4616Box) leaf4616InnerLog = true := by
  rfl'

private theorem leaf4616InnerLogValid :
    leaf4616InnerLog.Valid 8 (innerAD leaf4616Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf4616CoverageChecked

private noncomputable def leaf4616InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4616InputLogOnePlusV_eq :
    leaf4616InputLogOnePlusV = outerEnclosure 24
      (leaf4616Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4616RoundedFacts : LeafRoundedFacts 8
    leaf4616Certificate.logOnePlusV leaf4616InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4616InputLogOnePlusV_eq }

private noncomputable def leaf4616Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi255InputQChi innerPair335Input
    leaf4616InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4616LowerChecked :
    lowerCheck 24 leaf4616Box leaf4616Inputs = true := by
  rfl'

private theorem leaf4616CoversExact : CoversExact 8
    leaf4616Box leaf4616Certificate leaf4616InnerLog leaf4616Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi255RoundedFacts
    innerPair335RoundedFacts leaf4616RoundedFacts (by rfl)

private theorem leaf4616FlatSound : Sound leaf4616Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4616CertificateValid
    leaf4616InnerLogValid leaf4616CoversExact leaf4616LowerChecked

private noncomputable def leaf4617Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4617Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357305344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (570242789/536870912) }, upper := { exponent := 1, mantissa := (553/512) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716027903/68714610688) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf4617InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4617LocalValidity :
    LeafFacts leaf4617Box leaf4617Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4617Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357305344) }) = true
      norm_num [leaf4617Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4617CertificateValid :
    WideCertificateValid leaf4617Box leaf4617Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi256ValidityFacts
    leaf4617LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4617CoverageChecked :
    coverageCheck (innerAD leaf4617Box) leaf4617InnerLog = true := by
  rfl'

private theorem leaf4617InnerLogValid :
    leaf4617InnerLog.Valid 8 (innerAD leaf4617Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4617CoverageChecked

private noncomputable def leaf4617InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4617InputLogOnePlusV_eq :
    leaf4617InputLogOnePlusV = outerEnclosure 24
      (leaf4617Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4617RoundedFacts : LeafRoundedFacts 8
    leaf4617Certificate.logOnePlusV leaf4617InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4617InputLogOnePlusV_eq }

private noncomputable def leaf4617Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi256InputQChi innerPair243Input
    leaf4617InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4617LowerChecked :
    lowerCheck 24 leaf4617Box leaf4617Inputs = true := by
  rfl'

private theorem leaf4617CoversExact : CoversExact 8
    leaf4617Box leaf4617Certificate leaf4617InnerLog leaf4617Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi256RoundedFacts
    innerPair243RoundedFacts leaf4617RoundedFacts (by rfl)

private theorem leaf4617FlatSound : Sound leaf4617Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4617CertificateValid
    leaf4617InnerLogValid leaf4617CoversExact leaf4617LowerChecked

private noncomputable def leaf4618Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4618Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357280768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (573322791/536870912) }, upper := { exponent := 1, mantissa := (139/128) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716003327/68714561536) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf4618InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4618LocalValidity :
    LeafFacts leaf4618Box leaf4618Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4618Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357280768) }) = true
      norm_num [leaf4618Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4618CertificateValid :
    WideCertificateValid leaf4618Box leaf4618Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi256ValidityFacts
    leaf4618LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4618CoverageChecked :
    coverageCheck (innerAD leaf4618Box) leaf4618InnerLog = true := by
  rfl'

private theorem leaf4618InnerLogValid :
    leaf4618InnerLog.Valid 8 (innerAD leaf4618Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4618CoverageChecked

private noncomputable def leaf4618InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4618InputLogOnePlusV_eq :
    leaf4618InputLogOnePlusV = outerEnclosure 24
      (leaf4618Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4618RoundedFacts : LeafRoundedFacts 8
    leaf4618Certificate.logOnePlusV leaf4618InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4618InputLogOnePlusV_eq }

private noncomputable def leaf4618Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi256InputQChi innerPair249Input
    leaf4618InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4618LowerChecked :
    lowerCheck 24 leaf4618Box leaf4618Inputs = true := by
  rfl'

private theorem leaf4618CoversExact : CoversExact 8
    leaf4618Box leaf4618Certificate leaf4618InnerLog leaf4618Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi256RoundedFacts
    innerPair249RoundedFacts leaf4618RoundedFacts (by rfl)

private theorem leaf4618FlatSound : Sound leaf4618Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4618CertificateValid
    leaf4618InnerLogValid leaf4618CoversExact leaf4618LowerChecked

private noncomputable def leaf4619Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4619Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357411328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (556743199/536870912) }, upper := { exponent := 1, mantissa := (8641/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716133887/68714822656) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4619InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4619LocalValidity :
    LeafFacts leaf4619Box leaf4619Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4619Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357411328) }) = true
      norm_num [leaf4619Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4619CertificateValid :
    WideCertificateValid leaf4619Box leaf4619Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi253ValidityFacts
    leaf4619LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4619CoverageChecked :
    coverageCheck (innerAD leaf4619Box) leaf4619InnerLog = true := by
  rfl'

private theorem leaf4619InnerLogValid :
    leaf4619InnerLog.Valid 8 (innerAD leaf4619Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4619CoverageChecked

private noncomputable def leaf4619InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4619InputLogOnePlusV_eq :
    leaf4619InputLogOnePlusV = outerEnclosure 24
      (leaf4619Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4619RoundedFacts : LeafRoundedFacts 8
    leaf4619Certificate.logOnePlusV leaf4619InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4619InputLogOnePlusV_eq }

private noncomputable def leaf4619Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi253InputQChi innerPair242Input
    leaf4619InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4619LowerChecked :
    lowerCheck 24 leaf4619Box leaf4619Inputs = true := by
  rfl'

private theorem leaf4619CoversExact : CoversExact 8
    leaf4619Box leaf4619Certificate leaf4619InnerLog leaf4619Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi253RoundedFacts
    innerPair242RoundedFacts leaf4619RoundedFacts (by rfl)

private theorem leaf4619FlatSound : Sound leaf4619Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4619CertificateValid
    leaf4619InnerLogValid leaf4619CoversExact leaf4619LowerChecked

private noncomputable def leaf4620Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4620Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108302848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (559626605/536870912) }, upper := { exponent := 1, mantissa := (4343/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216648737/2216605696) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4620InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4620LocalValidity :
    LeafFacts leaf4620Box leaf4620Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4620Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108302848) }) = true
      norm_num [leaf4620Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4620CertificateValid :
    WideCertificateValid leaf4620Box leaf4620Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi253ValidityFacts
    leaf4620LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4620CoverageChecked :
    coverageCheck (innerAD leaf4620Box) leaf4620InnerLog = true := by
  rfl'

private theorem leaf4620InnerLogValid :
    leaf4620InnerLog.Valid 8 (innerAD leaf4620Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4620CoverageChecked

private noncomputable def leaf4620InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4620InputLogOnePlusV_eq :
    leaf4620InputLogOnePlusV = outerEnclosure 24
      (leaf4620Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4620RoundedFacts : LeafRoundedFacts 8
    leaf4620Certificate.logOnePlusV leaf4620InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4620InputLogOnePlusV_eq }

private noncomputable def leaf4620Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi253InputQChi innerPair242Input
    leaf4620InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4620LowerChecked :
    lowerCheck 24 leaf4620Box leaf4620Inputs = true := by
  rfl'

private theorem leaf4620CoversExact : CoversExact 8
    leaf4620Box leaf4620Certificate leaf4620InnerLog leaf4620Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi253RoundedFacts
    innerPair242RoundedFacts leaf4620RoundedFacts (by rfl)

private theorem leaf4620FlatSound : Sound leaf4620Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4620CertificateValid
    leaf4620InnerLogValid leaf4620CoversExact leaf4620LowerChecked

private noncomputable def leaf4621Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4621Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357359616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (563296397/536870912) }, upper := { exponent := 1, mantissa := (4371/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716082175/68714719232) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4621InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4621LocalValidity :
    LeafFacts leaf4621Box leaf4621Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4621Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357359616) }) = true
      norm_num [leaf4621Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4621CertificateValid :
    WideCertificateValid leaf4621Box leaf4621Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi254ValidityFacts
    leaf4621LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4621CoverageChecked :
    coverageCheck (innerAD leaf4621Box) leaf4621InnerLog = true := by
  rfl'

private theorem leaf4621InnerLogValid :
    leaf4621InnerLog.Valid 8 (innerAD leaf4621Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4621CoverageChecked

private noncomputable def leaf4621InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4621InputLogOnePlusV_eq :
    leaf4621InputLogOnePlusV = outerEnclosure 24
      (leaf4621Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4621RoundedFacts : LeafRoundedFacts 8
    leaf4621Certificate.logOnePlusV leaf4621InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4621InputLogOnePlusV_eq }

private noncomputable def leaf4621Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi254InputQChi innerPair551Input
    leaf4621InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4621LowerChecked :
    lowerCheck 24 leaf4621Box leaf4621Inputs = true := by
  rfl'

private theorem leaf4621CoversExact : CoversExact 8
    leaf4621Box leaf4621Certificate leaf4621InnerLog leaf4621Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi254RoundedFacts
    innerPair551RoundedFacts leaf4621RoundedFacts (by rfl)

private theorem leaf4621FlatSound : Sound leaf4621Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4621CertificateValid
    leaf4621InnerLogValid leaf4621CoversExact leaf4621LowerChecked

private noncomputable def leaf4622Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4622Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357336064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (566245335/536870912) }, upper := { exponent := 1, mantissa := (2197/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716058623/68714672128) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4622InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf4622LocalValidity :
    LeafFacts leaf4622Box leaf4622Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4622Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357336064) }) = true
      norm_num [leaf4622Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4622CertificateValid :
    WideCertificateValid leaf4622Box leaf4622Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi254ValidityFacts
    leaf4622LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4622CoverageChecked :
    coverageCheck (innerAD leaf4622Box) leaf4622InnerLog = true := by
  rfl'

private theorem leaf4622InnerLogValid :
    leaf4622InnerLog.Valid 8 (innerAD leaf4622Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf4622CoverageChecked

private noncomputable def leaf4622InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4622InputLogOnePlusV_eq :
    leaf4622InputLogOnePlusV = outerEnclosure 24
      (leaf4622Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4622RoundedFacts : LeafRoundedFacts 8
    leaf4622Certificate.logOnePlusV leaf4622InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4622InputLogOnePlusV_eq }

private noncomputable def leaf4622Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi254InputQChi innerPair335Input
    leaf4622InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4622LowerChecked :
    lowerCheck 24 leaf4622Box leaf4622Inputs = true := by
  rfl'

private theorem leaf4622CoversExact : CoversExact 8
    leaf4622Box leaf4622Certificate leaf4622InnerLog leaf4622Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi254RoundedFacts
    innerPair335RoundedFacts leaf4622RoundedFacts (by rfl)

private theorem leaf4622FlatSound : Sound leaf4622Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4622CertificateValid
    leaf4622InnerLogValid leaf4622CoversExact leaf4622LowerChecked

private noncomputable def leaf4623Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4623Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357365248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (562510011/536870912) }, upper := { exponent := 1, mantissa := (8731/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716087807/68714730496) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4623InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4623LocalValidity :
    LeafFacts leaf4623Box leaf4623Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4623Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357365248) }) = true
      norm_num [leaf4623Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4623CertificateValid :
    WideCertificateValid leaf4623Box leaf4623Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi253ValidityFacts
    leaf4623LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4623CoverageChecked :
    coverageCheck (innerAD leaf4623Box) leaf4623InnerLog = true := by
  rfl'

private theorem leaf4623InnerLogValid :
    leaf4623InnerLog.Valid 8 (innerAD leaf4623Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4623CoverageChecked

private noncomputable def leaf4623InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4623InputLogOnePlusV_eq :
    leaf4623InputLogOnePlusV = outerEnclosure 24
      (leaf4623Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4623RoundedFacts : LeafRoundedFacts 8
    leaf4623Certificate.logOnePlusV leaf4623InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4623InputLogOnePlusV_eq }

private noncomputable def leaf4623Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi253InputQChi innerPair551Input
    leaf4623InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4623LowerChecked :
    lowerCheck 24 leaf4623Box leaf4623Inputs = true := by
  rfl'

private theorem leaf4623CoversExact : CoversExact 8
    leaf4623Box leaf4623Certificate leaf4623InnerLog leaf4623Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi253RoundedFacts
    innerPair551RoundedFacts leaf4623RoundedFacts (by rfl)

private theorem leaf4623FlatSound : Sound leaf4623Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4623CertificateValid
    leaf4623InnerLogValid leaf4623CoversExact leaf4623LowerChecked

private noncomputable def leaf4624Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf4624Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908191744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (565393417/536870912) }, upper := { exponent := 1, mantissa := (1097/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816580681/9816383488) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4624InnerLog : WideLogData :=
  innerPair609Data

set_option maxRecDepth 1000000 in
private theorem leaf4624LocalValidity :
    LeafFacts leaf4624Box leaf4624Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4624Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908191744) }) = true
      norm_num [leaf4624Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4624CertificateValid :
    WideCertificateValid leaf4624Box leaf4624Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi253ValidityFacts
    leaf4624LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4624CoverageChecked :
    coverageCheck (innerAD leaf4624Box) leaf4624InnerLog = true := by
  rfl'

private theorem leaf4624InnerLogValid :
    leaf4624InnerLog.Valid 8 (innerAD leaf4624Box) :=
  wideLogDataValid_of_cachedCheck endpoint335PositiveFacts
    endpoint336PositiveFacts.valid leaf4624CoverageChecked

private noncomputable def leaf4624InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4624InputLogOnePlusV_eq :
    leaf4624InputLogOnePlusV = outerEnclosure 24
      (leaf4624Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4624RoundedFacts : LeafRoundedFacts 8
    leaf4624Certificate.logOnePlusV leaf4624InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4624InputLogOnePlusV_eq }

private noncomputable def leaf4624Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi253InputQChi innerPair609Input
    leaf4624InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4624LowerChecked :
    lowerCheck 24 leaf4624Box leaf4624Inputs = true := by
  rfl'

private theorem leaf4624CoversExact : CoversExact 8
    leaf4624Box leaf4624Certificate leaf4624InnerLog leaf4624Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi253RoundedFacts
    innerPair609RoundedFacts leaf4624RoundedFacts (by rfl)

private theorem leaf4624FlatSound : Sound leaf4624Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4624CertificateValid
    leaf4624InnerLogValid leaf4624CoversExact leaf4624LowerChecked

private noncomputable def leaf4625Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4625Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357312512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (569194273/536870912) }, upper := { exponent := 1, mantissa := (4417/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716035071/68714625024) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4625InnerLog : WideLogData :=
  innerPair338Data

set_option maxRecDepth 1000000 in
private theorem leaf4625LocalValidity :
    LeafFacts leaf4625Box leaf4625Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4625Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357312512) }) = true
      norm_num [leaf4625Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4625CertificateValid :
    WideCertificateValid leaf4625Box leaf4625Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi254ValidityFacts
    leaf4625LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4625CoverageChecked :
    coverageCheck (innerAD leaf4625Box) leaf4625InnerLog = true := by
  rfl'

private theorem leaf4625InnerLogValid :
    leaf4625InnerLog.Valid 8 (innerAD leaf4625Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint337PositiveFacts.valid leaf4625CoverageChecked

private noncomputable def leaf4625InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4625InputLogOnePlusV_eq :
    leaf4625InputLogOnePlusV = outerEnclosure 24
      (leaf4625Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4625RoundedFacts : LeafRoundedFacts 8
    leaf4625Certificate.logOnePlusV leaf4625InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4625InputLogOnePlusV_eq }

private noncomputable def leaf4625Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi254InputQChi innerPair338Input
    leaf4625InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4625LowerChecked :
    lowerCheck 24 leaf4625Box leaf4625Inputs = true := by
  rfl'

private theorem leaf4625CoversExact : CoversExact 8
    leaf4625Box leaf4625Certificate leaf4625InnerLog leaf4625Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi254RoundedFacts
    innerPair338RoundedFacts leaf4625RoundedFacts (by rfl)

private theorem leaf4625FlatSound : Sound leaf4625Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4625CertificateValid
    leaf4625InnerLogValid leaf4625CoversExact leaf4625LowerChecked

private noncomputable def leaf4626Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf4626Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357288960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (572143211/536870912) }, upper := { exponent := 1, mantissa := (555/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716011519/68714577920) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4626InnerLog : WideLogData :=
  innerPair255Data

set_option maxRecDepth 1000000 in
private theorem leaf4626LocalValidity :
    LeafFacts leaf4626Box leaf4626Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4626Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357288960) }) = true
      norm_num [leaf4626Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4626CertificateValid :
    WideCertificateValid leaf4626Box leaf4626Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi254ValidityFacts
    leaf4626LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4626CoverageChecked :
    coverageCheck (innerAD leaf4626Box) leaf4626InnerLog = true := by
  rfl'

private theorem leaf4626InnerLogValid :
    leaf4626InnerLog.Valid 8 (innerAD leaf4626Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint337PositiveFacts.valid leaf4626CoverageChecked

private noncomputable def leaf4626InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4626InputLogOnePlusV_eq :
    leaf4626InputLogOnePlusV = outerEnclosure 24
      (leaf4626Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4626RoundedFacts : LeafRoundedFacts 8
    leaf4626Certificate.logOnePlusV leaf4626InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4626InputLogOnePlusV_eq }

private noncomputable def leaf4626Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi254InputQChi innerPair255Input
    leaf4626InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4626LowerChecked :
    lowerCheck 24 leaf4626Box leaf4626Inputs = true := by
  rfl'

private theorem leaf4626CoversExact : CoversExact 8
    leaf4626Box leaf4626Certificate leaf4626InnerLog leaf4626Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi254RoundedFacts
    innerPair255RoundedFacts leaf4626RoundedFacts (by rfl)

private theorem leaf4626FlatSound : Sound leaf4626Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4626CertificateValid
    leaf4626InnerLogValid leaf4626CoversExact leaf4626LowerChecked

private noncomputable def leaf4627Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4627Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435751/268435456) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021018112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (569849595/536870912) }, upper := { exponent := 1, mantissa := (8843/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042119439/4042036224) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4627InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4627LocalValidity :
    LeafFacts leaf4627Box leaf4627Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4627Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021018112) }) = true
      norm_num [leaf4627Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4627CertificateValid :
    WideCertificateValid leaf4627Box leaf4627Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi255ValidityFacts
    leaf4627LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4627CoverageChecked :
    coverageCheck (innerAD leaf4627Box) leaf4627InnerLog = true := by
  rfl'

private theorem leaf4627InnerLogValid :
    leaf4627InnerLog.Valid 8 (innerAD leaf4627Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4627CoverageChecked

private noncomputable def leaf4627InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4627InputLogOnePlusV_eq :
    leaf4627InputLogOnePlusV = outerEnclosure 24
      (leaf4627Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4627RoundedFacts : LeafRoundedFacts 8
    leaf4627Certificate.logOnePlusV leaf4627InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4627InputLogOnePlusV_eq }

private noncomputable def leaf4627Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi255InputQChi innerPair243Input
    leaf4627InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4627LowerChecked :
    lowerCheck 24 leaf4627Box leaf4627Inputs = true := by
  rfl'

private theorem leaf4627CoversExact : CoversExact 8
    leaf4627Box leaf4627Certificate leaf4627InnerLog leaf4627Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi255RoundedFacts
    innerPair243RoundedFacts leaf4627RoundedFacts (by rfl)

private theorem leaf4627FlatSound : Sound leaf4627Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4627CertificateValid
    leaf4627InnerLogValid leaf4627CoversExact leaf4627LowerChecked

private noncomputable def leaf4628Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4628Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357283840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (572864065/536870912) }, upper := { exponent := 1, mantissa := (4445/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716006399/68714567680) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4628InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4628LocalValidity :
    LeafFacts leaf4628Box leaf4628Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4628Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357283840) }) = true
      norm_num [leaf4628Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4628CertificateValid :
    WideCertificateValid leaf4628Box leaf4628Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi255ValidityFacts
    leaf4628LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4628CoverageChecked :
    coverageCheck (innerAD leaf4628Box) leaf4628InnerLog = true := by
  rfl'

private theorem leaf4628InnerLogValid :
    leaf4628InnerLog.Valid 8 (innerAD leaf4628Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4628CoverageChecked

private noncomputable def leaf4628InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4628InputLogOnePlusV_eq :
    leaf4628InputLogOnePlusV = outerEnclosure 24
      (leaf4628Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4628RoundedFacts : LeafRoundedFacts 8
    leaf4628Certificate.logOnePlusV leaf4628InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4628InputLogOnePlusV_eq }

private noncomputable def leaf4628Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi255InputQChi innerPair249Input
    leaf4628InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4628LowerChecked :
    lowerCheck 24 leaf4628Box leaf4628Inputs = true := by
  rfl'

private theorem leaf4628CoversExact : CoversExact 8
    leaf4628Box leaf4628Certificate leaf4628InnerLog leaf4628Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi255RoundedFacts
    innerPair249RoundedFacts leaf4628RoundedFacts (by rfl)

private theorem leaf4628FlatSound : Sound leaf4628Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4628CertificateValid
    leaf4628InnerLogValid leaf4628CoversExact leaf4628LowerChecked

private noncomputable def leaf4629Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4629Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435753/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908179456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (576402793/536870912) }, upper := { exponent := 1, mantissa := (559/512) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816568393/9816358912) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf4629InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4629LocalValidity :
    LeafFacts leaf4629Box leaf4629Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4629Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908179456) }) = true
      norm_num [leaf4629Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4629CertificateValid :
    WideCertificateValid leaf4629Box leaf4629Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi256ValidityFacts
    leaf4629LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4629CoverageChecked :
    coverageCheck (innerAD leaf4629Box) leaf4629InnerLog = true := by
  rfl'

private theorem leaf4629InnerLogValid :
    leaf4629InnerLog.Valid 8 (innerAD leaf4629Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4629CoverageChecked

private noncomputable def leaf4629InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4629InputLogOnePlusV_eq :
    leaf4629InputLogOnePlusV = outerEnclosure 24
      (leaf4629Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4629RoundedFacts : LeafRoundedFacts 8
    leaf4629Certificate.logOnePlusV leaf4629InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4629InputLogOnePlusV_eq }

private noncomputable def leaf4629Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi256InputQChi innerPair249Input
    leaf4629InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4629LowerChecked :
    lowerCheck 24 leaf4629Box leaf4629Inputs = true := by
  rfl'

private theorem leaf4629CoversExact : CoversExact 8
    leaf4629Box leaf4629Certificate leaf4629InnerLog leaf4629Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi256RoundedFacts
    innerPair249RoundedFacts leaf4629RoundedFacts (by rfl)

private theorem leaf4629FlatSound : Sound leaf4629Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4629CertificateValid
    leaf4629InnerLogValid leaf4629CoversExact leaf4629LowerChecked

private noncomputable def leaf4630Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4630Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357231616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (579482795/536870912) }, upper := { exponent := 1, mantissa := (281/256) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715954175/68714463232) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf4630InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf4630LocalValidity :
    LeafFacts leaf4630Box leaf4630Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4630Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357231616) }) = true
      norm_num [leaf4630Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4630CertificateValid :
    WideCertificateValid leaf4630Box leaf4630Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi256ValidityFacts
    leaf4630LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4630CoverageChecked :
    coverageCheck (innerAD leaf4630Box) leaf4630InnerLog = true := by
  rfl'

private theorem leaf4630InnerLogValid :
    leaf4630InnerLog.Valid 8 (innerAD leaf4630Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf4630CoverageChecked

private noncomputable def leaf4630InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4630InputLogOnePlusV_eq :
    leaf4630InputLogOnePlusV = outerEnclosure 24
      (leaf4630Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4630RoundedFacts : LeafRoundedFacts 8
    leaf4630Certificate.logOnePlusV leaf4630InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4630InputLogOnePlusV_eq }

private noncomputable def leaf4630Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi256InputQChi innerPair332Input
    leaf4630InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4630LowerChecked :
    lowerCheck 24 leaf4630Box leaf4630Inputs = true := by
  rfl'

private theorem leaf4630CoversExact : CoversExact 8
    leaf4630Box leaf4630Certificate leaf4630InnerLog leaf4630Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi256RoundedFacts
    innerPair332RoundedFacts leaf4630RoundedFacts (by rfl)

private theorem leaf4630FlatSound : Sound leaf4630Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4630CertificateValid
    leaf4630InnerLogValid leaf4630CoversExact leaf4630LowerChecked

private noncomputable def leaf4631Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4631Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435755/268435456) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908179968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (575878535/536870912) }, upper := { exponent := 1, mantissa := (8937/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816568905/9816359936) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4631InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4631LocalValidity :
    LeafFacts leaf4631Box leaf4631Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4631Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908179968) }) = true
      norm_num [leaf4631Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4631CertificateValid :
    WideCertificateValid leaf4631Box leaf4631Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi255ValidityFacts
    leaf4631LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4631CoverageChecked :
    coverageCheck (innerAD leaf4631Box) leaf4631InnerLog = true := by
  rfl'

private theorem leaf4631InnerLogValid :
    leaf4631InnerLog.Valid 8 (innerAD leaf4631Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4631CoverageChecked

private noncomputable def leaf4631InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4631InputLogOnePlusV_eq :
    leaf4631InputLogOnePlusV = outerEnclosure 24
      (leaf4631Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4631RoundedFacts : LeafRoundedFacts 8
    leaf4631Certificate.logOnePlusV leaf4631InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4631InputLogOnePlusV_eq }

private noncomputable def leaf4631Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi255InputQChi innerPair249Input
    leaf4631InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4631LowerChecked :
    lowerCheck 24 leaf4631Box leaf4631Inputs = true := by
  rfl'

private theorem leaf4631CoversExact : CoversExact 8
    leaf4631Box leaf4631Certificate leaf4631InnerLog leaf4631Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi255RoundedFacts
    innerPair249RoundedFacts leaf4631RoundedFacts (by rfl)

private theorem leaf4631FlatSound : Sound leaf4631Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4631CertificateValid
    leaf4631InnerLogValid leaf4631CoversExact leaf4631LowerChecked

private noncomputable def leaf4632Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf4632Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357235712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (578893005/536870912) }, upper := { exponent := 1, mantissa := (1123/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715958271/68714471424) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4632InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf4632LocalValidity :
    LeafFacts leaf4632Box leaf4632Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4632Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357235712) }) = true
      norm_num [leaf4632Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4632CertificateValid :
    WideCertificateValid leaf4632Box leaf4632Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi255ValidityFacts
    leaf4632LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4632CoverageChecked :
    coverageCheck (innerAD leaf4632Box) leaf4632InnerLog = true := by
  rfl'

private theorem leaf4632InnerLogValid :
    leaf4632InnerLog.Valid 8 (innerAD leaf4632Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf4632CoverageChecked

private noncomputable def leaf4632InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4632InputLogOnePlusV_eq :
    leaf4632InputLogOnePlusV = outerEnclosure 24
      (leaf4632Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4632RoundedFacts : LeafRoundedFacts 8
    leaf4632Certificate.logOnePlusV leaf4632InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4632InputLogOnePlusV_eq }

private noncomputable def leaf4632Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi255InputQChi innerPair332Input
    leaf4632InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4632LowerChecked :
    lowerCheck 24 leaf4632Box leaf4632Inputs = true := by
  rfl'

private theorem leaf4632CoversExact : CoversExact 8
    leaf4632Box leaf4632Certificate leaf4632InnerLog leaf4632Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi255RoundedFacts
    innerPair332RoundedFacts leaf4632RoundedFacts (by rfl)

private theorem leaf4632FlatSound : Sound leaf4632Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4632CertificateValid
    leaf4632InnerLogValid leaf4632CoversExact leaf4632LowerChecked

private noncomputable def leaf4633Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4633Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435757/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357207040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (582562797/536870912) }, upper := { exponent := 1, mantissa := (565/512) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715929599/68714414080) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf4633InnerLog : WideLogData :=
  innerPair331Data

set_option maxRecDepth 1000000 in
private theorem leaf4633LocalValidity :
    LeafFacts leaf4633Box leaf4633Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4633Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357207040) }) = true
      norm_num [leaf4633Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4633CertificateValid :
    WideCertificateValid leaf4633Box leaf4633Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi256ValidityFacts
    leaf4633LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4633CoverageChecked :
    coverageCheck (innerAD leaf4633Box) leaf4633InnerLog = true := by
  rfl'

private theorem leaf4633InnerLogValid :
    leaf4633InnerLog.Valid 8 (innerAD leaf4633Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint80PositiveFacts.valid leaf4633CoverageChecked

private noncomputable def leaf4633InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4633InputLogOnePlusV_eq :
    leaf4633InputLogOnePlusV = outerEnclosure 24
      (leaf4633Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4633RoundedFacts : LeafRoundedFacts 8
    leaf4633Certificate.logOnePlusV leaf4633InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4633InputLogOnePlusV_eq }

private noncomputable def leaf4633Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi256InputQChi innerPair331Input
    leaf4633InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4633LowerChecked :
    lowerCheck 24 leaf4633Box leaf4633Inputs = true := by
  rfl'

private theorem leaf4633CoversExact : CoversExact 8
    leaf4633Box leaf4633Certificate leaf4633InnerLog leaf4633Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi256RoundedFacts
    innerPair331RoundedFacts leaf4633RoundedFacts (by rfl)

private theorem leaf4633FlatSound : Sound leaf4633Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4633CertificateValid
    leaf4633InnerLogValid leaf4633CoversExact leaf4633LowerChecked

private noncomputable def leaf4634Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf4634Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435759/268435456) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357182464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (585642799/536870912) }, upper := { exponent := 1, mantissa := (71/64) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715905023/68714364928) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf4634InnerLog : WideLogData :=
  innerPair611Data

set_option maxRecDepth 1000000 in
private theorem leaf4634LocalValidity :
    LeafFacts leaf4634Box leaf4634Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4634Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357182464) }) = true
      norm_num [leaf4634Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4634CertificateValid :
    WideCertificateValid leaf4634Box leaf4634Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi256ValidityFacts
    leaf4634LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4634CoverageChecked :
    coverageCheck (innerAD leaf4634Box) leaf4634InnerLog = true := by
  rfl'

private theorem leaf4634InnerLogValid :
    leaf4634InnerLog.Valid 8 (innerAD leaf4634Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint80PositiveFacts.valid leaf4634CoverageChecked

private noncomputable def leaf4634InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4634InputLogOnePlusV_eq :
    leaf4634InputLogOnePlusV = outerEnclosure 24
      (leaf4634Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4634RoundedFacts : LeafRoundedFacts 8
    leaf4634Certificate.logOnePlusV leaf4634InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4634InputLogOnePlusV_eq }

private noncomputable def leaf4634Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi256InputQChi innerPair611Input
    leaf4634InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4634LowerChecked :
    lowerCheck 24 leaf4634Box leaf4634Inputs = true := by
  rfl'

private theorem leaf4634CoversExact : CoversExact 8
    leaf4634Box leaf4634Certificate leaf4634InnerLog leaf4634Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi256RoundedFacts
    innerPair611RoundedFacts leaf4634RoundedFacts (by rfl)

private theorem leaf4634FlatSound : Sound leaf4634Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4634CertificateValid
    leaf4634InnerLogValid leaf4634CoversExact leaf4634LowerChecked

private noncomputable def component95Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node0_sound : Sound component95Node0Box :=
  sound_of_literal_split component95Node0Box leaf4603Box leaf4604Box
    .k (97/32) (by rfl) (by rfl)
    leaf4603FlatSound leaf4604FlatSound

private noncomputable def component95Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node1_sound : Sound component95Node1Box :=
  sound_of_literal_split component95Node1Box leaf4605Box leaf4606Box
    .k (97/32) (by rfl) (by rfl)
    leaf4605FlatSound leaf4606FlatSound

private noncomputable def component95Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node2_sound : Sound component95Node2Box :=
  sound_of_literal_split component95Node2Box component95Node0Box component95Node1Box
    .chi (45/128) (by rfl) (by rfl)
    component95Node0_sound component95Node1_sound

private noncomputable def component95Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node3_sound : Sound component95Node3Box :=
  sound_of_literal_split component95Node3Box leaf4607Box leaf4608Box
    .k (99/32) (by rfl) (by rfl)
    leaf4607FlatSound leaf4608FlatSound

private noncomputable def component95Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node4_sound : Sound component95Node4Box :=
  sound_of_literal_split component95Node4Box leaf4609Box leaf4610Box
    .k (99/32) (by rfl) (by rfl)
    leaf4609FlatSound leaf4610FlatSound

private noncomputable def component95Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node5_sound : Sound component95Node5Box :=
  sound_of_literal_split component95Node5Box component95Node3Box component95Node4Box
    .chi (45/128) (by rfl) (by rfl)
    component95Node3_sound component95Node4_sound

private noncomputable def component95Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node6_sound : Sound component95Node6Box :=
  sound_of_literal_split component95Node6Box component95Node2Box component95Node5Box
    .k (49/16) (by rfl) (by rfl)
    component95Node2_sound component95Node5_sound

private noncomputable def component95Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node7_sound : Sound component95Node7Box :=
  sound_of_literal_split component95Node7Box leaf4611Box leaf4612Box
    .k (97/32) (by rfl) (by rfl)
    leaf4611FlatSound leaf4612FlatSound

private noncomputable def component95Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node8_sound : Sound component95Node8Box :=
  sound_of_literal_split component95Node8Box leaf4613Box leaf4614Box
    .k (97/32) (by rfl) (by rfl)
    leaf4613FlatSound leaf4614FlatSound

private noncomputable def component95Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node9_sound : Sound component95Node9Box :=
  sound_of_literal_split component95Node9Box component95Node7Box component95Node8Box
    .chi (47/128) (by rfl) (by rfl)
    component95Node7_sound component95Node8_sound

private noncomputable def component95Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node10_sound : Sound component95Node10Box :=
  sound_of_literal_split component95Node10Box leaf4615Box leaf4616Box
    .k (99/32) (by rfl) (by rfl)
    leaf4615FlatSound leaf4616FlatSound

private noncomputable def component95Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node11_sound : Sound component95Node11Box :=
  sound_of_literal_split component95Node11Box leaf4617Box leaf4618Box
    .k (99/32) (by rfl) (by rfl)
    leaf4617FlatSound leaf4618FlatSound

private noncomputable def component95Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node12_sound : Sound component95Node12Box :=
  sound_of_literal_split component95Node12Box component95Node10Box component95Node11Box
    .chi (47/128) (by rfl) (by rfl)
    component95Node10_sound component95Node11_sound

private noncomputable def component95Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node13_sound : Sound component95Node13Box :=
  sound_of_literal_split component95Node13Box component95Node9Box component95Node12Box
    .k (49/16) (by rfl) (by rfl)
    component95Node9_sound component95Node12_sound

private noncomputable def component95Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node14_sound : Sound component95Node14Box :=
  sound_of_literal_split component95Node14Box component95Node6Box component95Node13Box
    .chi (23/64) (by rfl) (by rfl)
    component95Node6_sound component95Node13_sound

private noncomputable def component95Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node15_sound : Sound component95Node15Box :=
  sound_of_literal_split component95Node15Box leaf4619Box leaf4620Box
    .k (101/32) (by rfl) (by rfl)
    leaf4619FlatSound leaf4620FlatSound

private noncomputable def component95Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node16_sound : Sound component95Node16Box :=
  sound_of_literal_split component95Node16Box leaf4621Box leaf4622Box
    .k (101/32) (by rfl) (by rfl)
    leaf4621FlatSound leaf4622FlatSound

private noncomputable def component95Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node17_sound : Sound component95Node17Box :=
  sound_of_literal_split component95Node17Box component95Node15Box component95Node16Box
    .chi (45/128) (by rfl) (by rfl)
    component95Node15_sound component95Node16_sound

private noncomputable def component95Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/32), chiHi := (45/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node18_sound : Sound component95Node18Box :=
  sound_of_literal_split component95Node18Box leaf4623Box leaf4624Box
    .k (103/32) (by rfl) (by rfl)
    leaf4623FlatSound leaf4624FlatSound

private noncomputable def component95Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (45/128), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node19_sound : Sound component95Node19Box :=
  sound_of_literal_split component95Node19Box leaf4625Box leaf4626Box
    .k (103/32) (by rfl) (by rfl)
    leaf4625FlatSound leaf4626FlatSound

private noncomputable def component95Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node20_sound : Sound component95Node20Box :=
  sound_of_literal_split component95Node20Box component95Node18Box component95Node19Box
    .chi (45/128) (by rfl) (by rfl)
    component95Node18_sound component95Node19_sound

private noncomputable def component95Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component95Node21_sound : Sound component95Node21Box :=
  sound_of_literal_split component95Node21Box component95Node17Box component95Node20Box
    .k (51/16) (by rfl) (by rfl)
    component95Node17_sound component95Node20_sound

private noncomputable def component95Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node22_sound : Sound component95Node22Box :=
  sound_of_literal_split component95Node22Box leaf4627Box leaf4628Box
    .k (101/32) (by rfl) (by rfl)
    leaf4627FlatSound leaf4628FlatSound

private noncomputable def component95Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node23_sound : Sound component95Node23Box :=
  sound_of_literal_split component95Node23Box leaf4629Box leaf4630Box
    .k (101/32) (by rfl) (by rfl)
    leaf4629FlatSound leaf4630FlatSound

private noncomputable def component95Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node24_sound : Sound component95Node24Box :=
  sound_of_literal_split component95Node24Box component95Node22Box component95Node23Box
    .chi (47/128) (by rfl) (by rfl)
    component95Node22_sound component95Node23_sound

private noncomputable def component95Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (23/64), chiHi := (47/128) }

set_option maxRecDepth 1000000 in
private theorem component95Node25_sound : Sound component95Node25Box :=
  sound_of_literal_split component95Node25Box leaf4631Box leaf4632Box
    .k (103/32) (by rfl) (by rfl)
    leaf4631FlatSound leaf4632FlatSound

private noncomputable def component95Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (47/128), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node26_sound : Sound component95Node26Box :=
  sound_of_literal_split component95Node26Box leaf4633Box leaf4634Box
    .k (103/32) (by rfl) (by rfl)
    leaf4633FlatSound leaf4634FlatSound

private noncomputable def component95Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node27_sound : Sound component95Node27Box :=
  sound_of_literal_split component95Node27Box component95Node25Box component95Node26Box
    .chi (47/128) (by rfl) (by rfl)
    component95Node25_sound component95Node26_sound

private noncomputable def component95Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node28_sound : Sound component95Node28Box :=
  sound_of_literal_split component95Node28Box component95Node24Box component95Node27Box
    .k (51/16) (by rfl) (by rfl)
    component95Node24_sound component95Node27_sound

private noncomputable def component95Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component95Node29_sound : Sound component95Node29Box :=
  sound_of_literal_split component95Node29Box component95Node21Box component95Node28Box
    .chi (23/64) (by rfl) (by rfl)
    component95Node21_sound component95Node28_sound

noncomputable def component95Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component95_sound : Sound component95Box :=
  sound_of_literal_split component95Box component95Node14Box component95Node29Box
    .k (25/8) (by rfl) (by rfl)
    component95Node14_sound component95Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
