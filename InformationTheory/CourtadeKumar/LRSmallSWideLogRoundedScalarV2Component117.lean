import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
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

private noncomputable def leaf5825Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5825Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356932352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1241437791/1073741824) }, upper := { exponent := 1, mantissa := (19153/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715654911/68713864704) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5825InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5825LocalValidity :
    LeafFacts leaf5825Box leaf5825Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5825Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356932352) }) = true
      norm_num [leaf5825Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5825CertificateValid :
    WideCertificateValid leaf5825Box leaf5825Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi305ValidityFacts
    leaf5825LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5825CoverageChecked :
    coverageCheck (innerAD leaf5825Box) leaf5825InnerLog = true := by
  rfl'

private theorem leaf5825InnerLogValid :
    leaf5825InnerLog.Valid 8 (innerAD leaf5825Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5825CoverageChecked

private noncomputable def leaf5825InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814759/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5825InputLogOnePlusV_eq :
    leaf5825InputLogOnePlusV = outerEnclosure 24
      (leaf5825Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5825RoundedFacts : LeafRoundedFacts 8
    leaf5825Certificate.logOnePlusV leaf5825InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5825InputLogOnePlusV_eq }

private noncomputable def leaf5825Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi305InputQChi innerPair265Input
    leaf5825InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5825LowerChecked :
    lowerCheck 24 leaf5825Box leaf5825Inputs = true := by
  rfl'

private theorem leaf5825CoversExact : CoversExact 8
    leaf5825Box leaf5825Certificate leaf5825InnerLog leaf5825Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi305RoundedFacts
    innerPair265RoundedFacts leaf5825RoundedFacts (by rfl)

private theorem leaf5825FlatSound : Sound leaf5825Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5825CertificateValid
    leaf5825InnerLogValid leaf5825CoversExact leaf5825LowerChecked

private noncomputable def leaf5826Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5826Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356903424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1248777373/1073741824) }, upper := { exponent := 1, mantissa := (9633/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715625983/68713806848) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5826InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5826LocalValidity :
    LeafFacts leaf5826Box leaf5826Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5826Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356903424) }) = true
      norm_num [leaf5826Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5826CertificateValid :
    WideCertificateValid leaf5826Box leaf5826Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi306ValidityFacts
    leaf5826LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5826CoverageChecked :
    coverageCheck (innerAD leaf5826Box) leaf5826InnerLog = true := by
  rfl'

private theorem leaf5826InnerLogValid :
    leaf5826InnerLog.Valid 8 (innerAD leaf5826Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5826CoverageChecked

private noncomputable def leaf5826InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5826InputLogOnePlusV_eq :
    leaf5826InputLogOnePlusV = outerEnclosure 24
      (leaf5826Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5826RoundedFacts : LeafRoundedFacts 8
    leaf5826Certificate.logOnePlusV leaf5826InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5826InputLogOnePlusV_eq }

private noncomputable def leaf5826Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi306InputQChi innerPair272Input
    leaf5826InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5826LowerChecked :
    lowerCheck 24 leaf5826Box leaf5826Inputs = true := by
  rfl'

private theorem leaf5826CoversExact : CoversExact 8
    leaf5826Box leaf5826Certificate leaf5826InnerLog leaf5826Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi306RoundedFacts
    innerPair272RoundedFacts leaf5826RoundedFacts (by rfl)

private theorem leaf5826FlatSound : Sound leaf5826Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5826CertificateValid
    leaf5826InnerLogValid leaf5826CoversExact leaf5826LowerChecked

private noncomputable def leaf5827Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5827Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020994560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1247728861/1073741824) }, upper := { exponent := 1, mantissa := (9625/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042095887/4041989120) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5827InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5827LocalValidity :
    LeafFacts leaf5827Box leaf5827Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5827Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020994560) }) = true
      norm_num [leaf5827Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5827CertificateValid :
    WideCertificateValid leaf5827Box leaf5827Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi305ValidityFacts
    leaf5827LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5827CoverageChecked :
    coverageCheck (innerAD leaf5827Box) leaf5827InnerLog = true := by
  rfl'

private theorem leaf5827InnerLogValid :
    leaf5827InnerLog.Valid 8 (innerAD leaf5827Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5827CoverageChecked

private noncomputable def leaf5827InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5827InputLogOnePlusV_eq :
    leaf5827InputLogOnePlusV = outerEnclosure 24
      (leaf5827Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5827RoundedFacts : LeafRoundedFacts 8
    leaf5827Certificate.logOnePlusV leaf5827InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5827InputLogOnePlusV_eq }

private noncomputable def leaf5827Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi305InputQChi innerPair272Input
    leaf5827InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5827LowerChecked :
    lowerCheck 24 leaf5827Box leaf5827Inputs = true := by
  rfl'

private theorem leaf5827CoversExact : CoversExact 8
    leaf5827Box leaf5827Certificate leaf5827InnerLog leaf5827Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi305RoundedFacts
    innerPair272RoundedFacts leaf5827RoundedFacts (by rfl)

private theorem leaf5827FlatSound : Sound leaf5827Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5827CertificateValid
    leaf5827InnerLogValid leaf5827CoversExact leaf5827LowerChecked

private noncomputable def leaf5828Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5828Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356878336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1255133975/1073741824) }, upper := { exponent := 1, mantissa := (4841/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715600895/68713756672) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5828InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5828LocalValidity :
    LeafFacts leaf5828Box leaf5828Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5828Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356878336) }) = true
      norm_num [leaf5828Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5828CertificateValid :
    WideCertificateValid leaf5828Box leaf5828Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi306ValidityFacts
    leaf5828LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5828CoverageChecked :
    coverageCheck (innerAD leaf5828Box) leaf5828InnerLog = true := by
  rfl'

private theorem leaf5828InnerLogValid :
    leaf5828InnerLog.Valid 8 (innerAD leaf5828Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5828CoverageChecked

private noncomputable def leaf5828InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5828InputLogOnePlusV_eq :
    leaf5828InputLogOnePlusV = outerEnclosure 24
      (leaf5828Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5828RoundedFacts : LeafRoundedFacts 8
    leaf5828Certificate.logOnePlusV leaf5828InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5828InputLogOnePlusV_eq }

private noncomputable def leaf5828Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi306InputQChi innerPair272Input
    leaf5828InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5828LowerChecked :
    lowerCheck 24 leaf5828Box leaf5828Inputs = true := by
  rfl'

private theorem leaf5828CoversExact : CoversExact 8
    leaf5828Box leaf5828Certificate leaf5828InnerLog leaf5828Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi306RoundedFacts
    innerPair272RoundedFacts leaf5828RoundedFacts (by rfl)

private theorem leaf5828FlatSound : Sound leaf5828Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5828CertificateValid
    leaf5828InnerLogValid leaf5828CoversExact leaf5828LowerChecked

private noncomputable def leaf5829Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5829Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435781/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356845568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (628041981/536870912) }, upper := { exponent := 1, mantissa := (4873/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715568127/68713691136) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5829InnerLog : WideLogData :=
  innerPair675Data

set_option maxRecDepth 1000000 in
private theorem leaf5829LocalValidity :
    LeafFacts leaf5829Box leaf5829Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5829Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356845568) }) = true
      norm_num [leaf5829Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5829CertificateValid :
    WideCertificateValid leaf5829Box leaf5829Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi260ValidityFacts
    leaf5829LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5829CoverageChecked :
    coverageCheck (innerAD leaf5829Box) leaf5829InnerLog = true := by
  rfl'

private theorem leaf5829InnerLogValid :
    leaf5829InnerLog.Valid 8 (innerAD leaf5829Box) :=
  wideLogDataValid_of_cachedCheck endpoint420PositiveFacts
    endpoint421PositiveFacts.valid leaf5829CoverageChecked

private noncomputable def leaf5829InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629539/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5829InputLogOnePlusV_eq :
    leaf5829InputLogOnePlusV = outerEnclosure 24
      (leaf5829Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5829RoundedFacts : LeafRoundedFacts 8
    leaf5829Certificate.logOnePlusV leaf5829InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5829InputLogOnePlusV_eq }

private noncomputable def leaf5829Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi260InputQChi innerPair675Input
    leaf5829InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5829LowerChecked :
    lowerCheck 24 leaf5829Box leaf5829Inputs = true := by
  rfl'

private theorem leaf5829CoversExact : CoversExact 8
    leaf5829Box leaf5829Certificate leaf5829InnerLog leaf5829Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi260RoundedFacts
    innerPair675RoundedFacts leaf5829RoundedFacts (by rfl)

private theorem leaf5829FlatSound : Sound leaf5829Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5829CertificateValid
    leaf5829InnerLogValid leaf5829CoversExact leaf5829LowerChecked

private noncomputable def leaf5830Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (49/128), chiHi := (25/64) }

private noncomputable def leaf5830Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356819968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (631253047/536870912) }, upper := { exponent := 1, mantissa := (2449/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi260LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715542527/68713639936) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5830InnerLog : WideLogData :=
  innerPair676Data

set_option maxRecDepth 1000000 in
private theorem leaf5830LocalValidity :
    LeafFacts leaf5830Box leaf5830Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5830Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356819968) }) = true
      norm_num [leaf5830Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5830CertificateValid :
    WideCertificateValid leaf5830Box leaf5830Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi260ValidityFacts
    leaf5830LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5830CoverageChecked :
    coverageCheck (innerAD leaf5830Box) leaf5830InnerLog = true := by
  rfl'

private theorem leaf5830InnerLogValid :
    leaf5830InnerLog.Valid 8 (innerAD leaf5830Box) :=
  wideLogDataValid_of_cachedCheck endpoint422PositiveFacts
    endpoint309PositiveFacts.valid leaf5830CoverageChecked

private noncomputable def leaf5830InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5830InputLogOnePlusV_eq :
    leaf5830InputLogOnePlusV = outerEnclosure 24
      (leaf5830Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5830RoundedFacts : LeafRoundedFacts 8
    leaf5830Certificate.logOnePlusV leaf5830InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5830InputLogOnePlusV_eq }

private noncomputable def leaf5830Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi260InputQChi innerPair676Input
    leaf5830InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5830LowerChecked :
    lowerCheck 24 leaf5830Box leaf5830Inputs = true := by
  rfl'

private theorem leaf5830CoversExact : CoversExact 8
    leaf5830Box leaf5830Certificate leaf5830InnerLog leaf5830Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi260RoundedFacts
    innerPair676RoundedFacts leaf5830RoundedFacts (by rfl)

private theorem leaf5830FlatSound : Sound leaf5830Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5830CertificateValid
    leaf5830InnerLogValid leaf5830CoversExact leaf5830LowerChecked

private noncomputable def leaf5831Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5831Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356882688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1254019931/1073741824) }, upper := { exponent := 1, mantissa := (19347/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715605247/68713765376) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5831InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5831LocalValidity :
    LeafFacts leaf5831Box leaf5831Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5831Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356882688) }) = true
      norm_num [leaf5831Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5831CertificateValid :
    WideCertificateValid leaf5831Box leaf5831Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi305ValidityFacts
    leaf5831LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5831CoverageChecked :
    coverageCheck (innerAD leaf5831Box) leaf5831InnerLog = true := by
  rfl'

private theorem leaf5831InnerLogValid :
    leaf5831InnerLog.Valid 8 (innerAD leaf5831Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5831CoverageChecked

private noncomputable def leaf5831InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814765/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5831InputLogOnePlusV_eq :
    leaf5831InputLogOnePlusV = outerEnclosure 24
      (leaf5831Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5831RoundedFacts : LeafRoundedFacts 8
    leaf5831Certificate.logOnePlusV leaf5831InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5831InputLogOnePlusV_eq }

private noncomputable def leaf5831Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi305InputQChi innerPair272Input
    leaf5831InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5831LowerChecked :
    lowerCheck 24 leaf5831Box leaf5831Inputs = true := by
  rfl'

private theorem leaf5831CoversExact : CoversExact 8
    leaf5831Box leaf5831Certificate leaf5831InnerLog leaf5831Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi305RoundedFacts
    innerPair272RoundedFacts leaf5831RoundedFacts (by rfl)

private theorem leaf5831FlatSound : Sound leaf5831Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5831CertificateValid
    leaf5831InnerLogValid leaf5831CoversExact leaf5831LowerChecked

private noncomputable def leaf5832Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5832Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356853248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1261490577/1073741824) }, upper := { exponent := 1, mantissa := (9731/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715575807/68713706496) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5832InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5832LocalValidity :
    LeafFacts leaf5832Box leaf5832Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5832Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356853248) }) = true
      norm_num [leaf5832Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5832CertificateValid :
    WideCertificateValid leaf5832Box leaf5832Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi306ValidityFacts
    leaf5832LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5832CoverageChecked :
    coverageCheck (innerAD leaf5832Box) leaf5832InnerLog = true := by
  rfl'

private theorem leaf5832InnerLogValid :
    leaf5832InnerLog.Valid 8 (innerAD leaf5832Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5832CoverageChecked

private noncomputable def leaf5832InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629537/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5832InputLogOnePlusV_eq :
    leaf5832InputLogOnePlusV = outerEnclosure 24
      (leaf5832Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5832RoundedFacts : LeafRoundedFacts 8
    leaf5832Certificate.logOnePlusV leaf5832InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5832InputLogOnePlusV_eq }

private noncomputable def leaf5832Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi306InputQChi innerPair569Input
    leaf5832InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5832LowerChecked :
    lowerCheck 24 leaf5832Box leaf5832Inputs = true := by
  rfl'

private theorem leaf5832CoversExact : CoversExact 8
    leaf5832Box leaf5832Certificate leaf5832InnerLog leaf5832Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi306RoundedFacts
    innerPair569RoundedFacts leaf5832RoundedFacts (by rfl)

private theorem leaf5832FlatSound : Sound leaf5832Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5832CertificateValid
    leaf5832InnerLogValid leaf5832CoversExact leaf5832LowerChecked

private noncomputable def leaf5833Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5833Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871337/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356857856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1260311001/1073741824) }, upper := { exponent := 1, mantissa := (4861/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715580415/68713715712) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5833InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf5833LocalValidity :
    LeafFacts leaf5833Box leaf5833Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5833Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356857856) }) = true
      norm_num [leaf5833Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5833CertificateValid :
    WideCertificateValid leaf5833Box leaf5833Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi305ValidityFacts
    leaf5833LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5833CoverageChecked :
    coverageCheck (innerAD leaf5833Box) leaf5833InnerLog = true := by
  rfl'

private theorem leaf5833InnerLogValid :
    leaf5833InnerLog.Valid 8 (innerAD leaf5833Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf5833CoverageChecked

private noncomputable def leaf5833InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363423/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5833InputLogOnePlusV_eq :
    leaf5833InputLogOnePlusV = outerEnclosure 24
      (leaf5833Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5833RoundedFacts : LeafRoundedFacts 8
    leaf5833Certificate.logOnePlusV leaf5833InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5833InputLogOnePlusV_eq }

private noncomputable def leaf5833Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi305InputQChi innerPair272Input
    leaf5833InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5833LowerChecked :
    lowerCheck 24 leaf5833Box leaf5833Inputs = true := by
  rfl'

private theorem leaf5833CoversExact : CoversExact 8
    leaf5833Box leaf5833Certificate leaf5833InnerLog leaf5833Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi305RoundedFacts
    innerPair272RoundedFacts leaf5833RoundedFacts (by rfl)

private theorem leaf5833FlatSound : Sound leaf5833Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5833CertificateValid
    leaf5833InnerLogValid leaf5833CoversExact leaf5833LowerChecked

private noncomputable def leaf5834Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5834Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356828160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1267847179/1073741824) }, upper := { exponent := 1, mantissa := (2445/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715550719/68713656320) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5834InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5834LocalValidity :
    LeafFacts leaf5834Box leaf5834Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5834Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356828160) }) = true
      norm_num [leaf5834Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5834CertificateValid :
    WideCertificateValid leaf5834Box leaf5834Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi306ValidityFacts
    leaf5834LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5834CoverageChecked :
    coverageCheck (innerAD leaf5834Box) leaf5834InnerLog = true := by
  rfl'

private theorem leaf5834InnerLogValid :
    leaf5834InnerLog.Valid 8 (innerAD leaf5834Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5834CoverageChecked

private noncomputable def leaf5834InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629543/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5834InputLogOnePlusV_eq :
    leaf5834InputLogOnePlusV = outerEnclosure 24
      (leaf5834Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5834RoundedFacts : LeafRoundedFacts 8
    leaf5834Certificate.logOnePlusV leaf5834InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5834InputLogOnePlusV_eq }

private noncomputable def leaf5834Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi306InputQChi innerPair273Input
    leaf5834InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5834LowerChecked :
    lowerCheck 24 leaf5834Box leaf5834Inputs = true := by
  rfl'

private theorem leaf5834CoversExact : CoversExact 8
    leaf5834Box leaf5834Certificate leaf5834InnerLog leaf5834Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi306RoundedFacts
    innerPair273RoundedFacts leaf5834RoundedFacts (by rfl)

private theorem leaf5834FlatSound : Sound leaf5834Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5834CertificateValid
    leaf5834InnerLogValid leaf5834CoversExact leaf5834LowerChecked

private noncomputable def leaf5835Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5835Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356823808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1268961223/1073741824) }, upper := { exponent := 1, mantissa := (19577/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715546367/68713647616) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5835InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5835LocalValidity :
    LeafFacts leaf5835Box leaf5835Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5835Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356823808) }) = true
      norm_num [leaf5835Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5835CertificateValid :
    WideCertificateValid leaf5835Box leaf5835Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi307ValidityFacts
    leaf5835LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5835CoverageChecked :
    coverageCheck (innerAD leaf5835Box) leaf5835InnerLog = true := by
  rfl'

private theorem leaf5835InnerLogValid :
    leaf5835InnerLog.Valid 8 (innerAD leaf5835Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5835CoverageChecked

private noncomputable def leaf5835InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453693/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5835InputLogOnePlusV_eq :
    leaf5835InputLogOnePlusV = outerEnclosure 24
      (leaf5835Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5835RoundedFacts : LeafRoundedFacts 8
    leaf5835Certificate.logOnePlusV leaf5835InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5835InputLogOnePlusV_eq }

private noncomputable def leaf5835Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi307InputQChi innerPair273Input
    leaf5835InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5835LowerChecked :
    lowerCheck 24 leaf5835Box leaf5835Inputs = true := by
  rfl'

private theorem leaf5835CoversExact : CoversExact 8
    leaf5835Box leaf5835Certificate leaf5835InnerLog leaf5835Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi307RoundedFacts
    innerPair273RoundedFacts leaf5835RoundedFacts (by rfl)

private theorem leaf5835FlatSound : Sound leaf5835Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5835CertificateValid
    leaf5835InnerLogValid leaf5835CoversExact leaf5835LowerChecked

private noncomputable def leaf5836Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5836Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020987904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1276431869/1073741824) }, upper := { exponent := 1, mantissa := (4923/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042089231/4041975808) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5836InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5836LocalValidity :
    LeafFacts leaf5836Box leaf5836Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5836Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020987904) }) = true
      norm_num [leaf5836Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5836CertificateValid :
    WideCertificateValid leaf5836Box leaf5836Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi308ValidityFacts
    leaf5836LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5836CoverageChecked :
    coverageCheck (innerAD leaf5836Box) leaf5836InnerLog = true := by
  rfl'

private theorem leaf5836InnerLogValid :
    leaf5836InnerLog.Valid 8 (innerAD leaf5836Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5836CoverageChecked

private noncomputable def leaf5836InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726847/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5836InputLogOnePlusV_eq :
    leaf5836InputLogOnePlusV = outerEnclosure 24
      (leaf5836Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5836RoundedFacts : LeafRoundedFacts 8
    leaf5836Certificate.logOnePlusV leaf5836InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5836InputLogOnePlusV_eq }

private noncomputable def leaf5836Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi308InputQChi innerPair278Input
    leaf5836InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5836LowerChecked :
    lowerCheck 24 leaf5836Box leaf5836Inputs = true := by
  rfl'

private theorem leaf5836CoversExact : CoversExact 8
    leaf5836Box leaf5836Certificate leaf5836InnerLog leaf5836Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi308RoundedFacts
    innerPair278RoundedFacts leaf5836RoundedFacts (by rfl)

private theorem leaf5836FlatSound : Sound leaf5836Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5836CertificateValid
    leaf5836InnerLogValid leaf5836CoversExact leaf5836LowerChecked

private noncomputable def leaf5837Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5837Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356798464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1275383357/1073741824) }, upper := { exponent := 1, mantissa := (4919/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715521023/68713596928) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5837InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5837LocalValidity :
    LeafFacts leaf5837Box leaf5837Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5837Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356798464) }) = true
      norm_num [leaf5837Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5837CertificateValid :
    WideCertificateValid leaf5837Box leaf5837Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi307ValidityFacts
    leaf5837LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5837CoverageChecked :
    coverageCheck (innerAD leaf5837Box) leaf5837InnerLog = true := by
  rfl'

private theorem leaf5837InnerLogValid :
    leaf5837InnerLog.Valid 8 (innerAD leaf5837Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5837CoverageChecked

private noncomputable def leaf5837InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629551/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5837InputLogOnePlusV_eq :
    leaf5837InputLogOnePlusV = outerEnclosure 24
      (leaf5837Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5837RoundedFacts : LeafRoundedFacts 8
    leaf5837Certificate.logOnePlusV leaf5837InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5837InputLogOnePlusV_eq }

private noncomputable def leaf5837Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi307InputQChi innerPair278Input
    leaf5837InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5837LowerChecked :
    lowerCheck 24 leaf5837Box leaf5837Inputs = true := by
  rfl'

private theorem leaf5837CoversExact : CoversExact 8
    leaf5837Box leaf5837Certificate leaf5837InnerLog leaf5837Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi307RoundedFacts
    innerPair278RoundedFacts leaf5837RoundedFacts (by rfl)

private theorem leaf5837FlatSound : Sound leaf5837Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5837CertificateValid
    leaf5837InnerLogValid leaf5837CoversExact leaf5837LowerChecked

private noncomputable def leaf5838Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5838Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908109824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1282919535/1073741824) }, upper := { exponent := 1, mantissa := (1237/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816498761/9816219648) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5838InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5838LocalValidity :
    LeafFacts leaf5838Box leaf5838Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5838Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908109824) }) = true
      norm_num [leaf5838Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5838CertificateValid :
    WideCertificateValid leaf5838Box leaf5838Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi308ValidityFacts
    leaf5838LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5838CoverageChecked :
    coverageCheck (innerAD leaf5838Box) leaf5838InnerLog = true := by
  rfl'

private theorem leaf5838InnerLogValid :
    leaf5838InnerLog.Valid 8 (innerAD leaf5838Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5838CoverageChecked

private noncomputable def leaf5838InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814779/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5838InputLogOnePlusV_eq :
    leaf5838InputLogOnePlusV = outerEnclosure 24
      (leaf5838Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5838RoundedFacts : LeafRoundedFacts 8
    leaf5838Certificate.logOnePlusV leaf5838InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5838InputLogOnePlusV_eq }

private noncomputable def leaf5838Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi308InputQChi innerPair278Input
    leaf5838InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5838LowerChecked :
    lowerCheck 24 leaf5838Box leaf5838Inputs = true := by
  rfl'

private theorem leaf5838CoversExact : CoversExact 8
    leaf5838Box leaf5838Certificate leaf5838InnerLog leaf5838Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi308RoundedFacts
    innerPair278RoundedFacts leaf5838RoundedFacts (by rfl)

private theorem leaf5838FlatSound : Sound leaf5838Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5838CertificateValid
    leaf5838InnerLogValid leaf5838CoversExact leaf5838LowerChecked

private noncomputable def leaf5839Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5839Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435783/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356787712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (635381563/536870912) }, upper := { exponent := 1, mantissa := (9859/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715510271/68713575424) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5839InnerLog : WideLogData :=
  innerPair583Data

set_option maxRecDepth 1000000 in
private theorem leaf5839LocalValidity :
    LeafFacts leaf5839Box leaf5839Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5839Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356787712) }) = true
      norm_num [leaf5839Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5839CertificateValid :
    WideCertificateValid leaf5839Box leaf5839Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi261ValidityFacts
    leaf5839LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5839CoverageChecked :
    coverageCheck (innerAD leaf5839Box) leaf5839InnerLog = true := by
  rfl'

private theorem leaf5839InnerLogValid :
    leaf5839InnerLog.Valid 8 (innerAD leaf5839Box) :=
  wideLogDataValid_of_cachedCheck endpoint303PositiveFacts
    endpoint423PositiveFacts.valid leaf5839CoverageChecked

private noncomputable def leaf5839InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5839InputLogOnePlusV_eq :
    leaf5839InputLogOnePlusV = outerEnclosure 24
      (leaf5839Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5839RoundedFacts : LeafRoundedFacts 8
    leaf5839Certificate.logOnePlusV leaf5839InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5839InputLogOnePlusV_eq }

private noncomputable def leaf5839Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi261InputQChi innerPair583Input
    leaf5839InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5839LowerChecked :
    lowerCheck 24 leaf5839Box leaf5839Inputs = true := by
  rfl'

private theorem leaf5839CoversExact : CoversExact 8
    leaf5839Box leaf5839Certificate leaf5839InnerLog leaf5839Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi261RoundedFacts
    innerPair583RoundedFacts leaf5839RoundedFacts (by rfl)

private theorem leaf5839FlatSound : Sound leaf5839Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5839CertificateValid
    leaf5839InnerLogValid leaf5839CoversExact leaf5839LowerChecked

private noncomputable def leaf5840Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5840Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435785/268435456) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908108800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (638658161/536870912) }, upper := { exponent := 1, mantissa := (4955/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816497737/9816217600) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5840InnerLog : WideLogData :=
  innerPair283Data

set_option maxRecDepth 1000000 in
private theorem leaf5840LocalValidity :
    LeafFacts leaf5840Box leaf5840Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5840Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908108800) }) = true
      norm_num [leaf5840Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5840CertificateValid :
    WideCertificateValid leaf5840Box leaf5840Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi261ValidityFacts
    leaf5840LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5840CoverageChecked :
    coverageCheck (innerAD leaf5840Box) leaf5840InnerLog = true := by
  rfl'

private theorem leaf5840InnerLogValid :
    leaf5840InnerLog.Valid 8 (innerAD leaf5840Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint308PositiveFacts.valid leaf5840CoverageChecked

private noncomputable def leaf5840InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5840InputLogOnePlusV_eq :
    leaf5840InputLogOnePlusV = outerEnclosure 24
      (leaf5840Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5840RoundedFacts : LeafRoundedFacts 8
    leaf5840Certificate.logOnePlusV leaf5840InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5840InputLogOnePlusV_eq }

private noncomputable def leaf5840Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi261InputQChi innerPair283Input
    leaf5840InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5840LowerChecked :
    lowerCheck 24 leaf5840Box leaf5840Inputs = true := by
  rfl'

private theorem leaf5840CoversExact : CoversExact 8
    leaf5840Box leaf5840Certificate leaf5840InnerLog leaf5840Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi261RoundedFacts
    innerPair283RoundedFacts leaf5840RoundedFacts (by rfl)

private theorem leaf5840FlatSound : Sound leaf5840Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5840CertificateValid
    leaf5840InnerLogValid leaf5840CoversExact leaf5840LowerChecked

private noncomputable def leaf5841Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5841Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435785/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356729856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (642721145/536870912) }, upper := { exponent := 1, mantissa := (2493/2048) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715452415/68713459712) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5841InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5841LocalValidity :
    LeafFacts leaf5841Box leaf5841Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5841Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356729856) }) = true
      norm_num [leaf5841Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5841CertificateValid :
    WideCertificateValid leaf5841Box leaf5841Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi262ValidityFacts
    leaf5841LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5841CoverageChecked :
    coverageCheck (innerAD leaf5841Box) leaf5841InnerLog = true := by
  rfl'

private theorem leaf5841InnerLogValid :
    leaf5841InnerLog.Valid 8 (innerAD leaf5841Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5841CoverageChecked

private noncomputable def leaf5841InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5841InputLogOnePlusV_eq :
    leaf5841InputLogOnePlusV = outerEnclosure 24
      (leaf5841Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5841RoundedFacts : LeafRoundedFacts 8
    leaf5841Certificate.logOnePlusV leaf5841InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5841InputLogOnePlusV_eq }

private noncomputable def leaf5841Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi262InputQChi innerPair278Input
    leaf5841InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5841LowerChecked :
    lowerCheck 24 leaf5841Box leaf5841Inputs = true := by
  rfl'

private theorem leaf5841CoversExact : CoversExact 8
    leaf5841Box leaf5841Certificate leaf5841InnerLog leaf5841Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi262RoundedFacts
    innerPair278RoundedFacts leaf5841RoundedFacts (by rfl)

private theorem leaf5841FlatSound : Sound leaf5841Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5841CertificateValid
    leaf5841InnerLogValid leaf5841CoversExact leaf5841LowerChecked

private noncomputable def leaf5842Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5842Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435787/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356703232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (646063275/536870912) }, upper := { exponent := 1, mantissa := (1253/1024) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715425791/68713406464) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5842InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5842LocalValidity :
    LeafFacts leaf5842Box leaf5842Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5842Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356703232) }) = true
      norm_num [leaf5842Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5842CertificateValid :
    WideCertificateValid leaf5842Box leaf5842Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi262ValidityFacts
    leaf5842LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5842CoverageChecked :
    coverageCheck (innerAD leaf5842Box) leaf5842InnerLog = true := by
  rfl'

private theorem leaf5842InnerLogValid :
    leaf5842InnerLog.Valid 8 (innerAD leaf5842Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5842CoverageChecked

private noncomputable def leaf5842InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5842InputLogOnePlusV_eq :
    leaf5842InputLogOnePlusV = outerEnclosure 24
      (leaf5842Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5842RoundedFacts : LeafRoundedFacts 8
    leaf5842Certificate.logOnePlusV leaf5842InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5842InputLogOnePlusV_eq }

private noncomputable def leaf5842Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi262InputQChi innerPair590Input
    leaf5842InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5842LowerChecked :
    lowerCheck 24 leaf5842Box leaf5842Inputs = true := by
  rfl'

private theorem leaf5842CoversExact : CoversExact 8
    leaf5842Box leaf5842Certificate leaf5842InnerLog leaf5842Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi262RoundedFacts
    innerPair590RoundedFacts leaf5842RoundedFacts (by rfl)

private theorem leaf5842FlatSound : Sound leaf5842Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5842CertificateValid
    leaf5842InnerLogValid leaf5842CoversExact leaf5842LowerChecked

private noncomputable def leaf5843Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5843Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435787/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356735488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (641934759/536870912) }, upper := { exponent := 1, mantissa := (9961/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715458047/68713470976) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5843InnerLog : WideLogData :=
  innerPair588Data

set_option maxRecDepth 1000000 in
private theorem leaf5843LocalValidity :
    LeafFacts leaf5843Box leaf5843Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5843Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356735488) }) = true
      norm_num [leaf5843Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5843CertificateValid :
    WideCertificateValid leaf5843Box leaf5843Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi261ValidityFacts
    leaf5843LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5843CoverageChecked :
    coverageCheck (innerAD leaf5843Box) leaf5843InnerLog = true := by
  rfl'

private theorem leaf5843InnerLogValid :
    leaf5843InnerLog.Valid 8 (innerAD leaf5843Box) :=
  wideLogDataValid_of_cachedCheck endpoint304PositiveFacts
    endpoint424PositiveFacts.valid leaf5843CoverageChecked

private noncomputable def leaf5843InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814783/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5843InputLogOnePlusV_eq :
    leaf5843InputLogOnePlusV = outerEnclosure 24
      (leaf5843Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5843RoundedFacts : LeafRoundedFacts 8
    leaf5843Certificate.logOnePlusV leaf5843InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5843InputLogOnePlusV_eq }

private noncomputable def leaf5843Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi261InputQChi innerPair588Input
    leaf5843InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5843LowerChecked :
    lowerCheck 24 leaf5843Box leaf5843Inputs = true := by
  rfl'

private theorem leaf5843CoversExact : CoversExact 8
    leaf5843Box leaf5843Certificate leaf5843InnerLog leaf5843Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi261RoundedFacts
    innerPair588RoundedFacts leaf5843RoundedFacts (by rfl)

private theorem leaf5843FlatSound : Sound leaf5843Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5843CertificateValid
    leaf5843InnerLogValid leaf5843CoversExact leaf5843LowerChecked

private noncomputable def leaf5844Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (25/64), chiHi := (51/128) }

private noncomputable def leaf5844Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435789/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356709376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (645211357/536870912) }, upper := { exponent := 1, mantissa := (2503/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi261LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715431935/68713418752) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5844InnerLog : WideLogData :=
  innerPair677Data

set_option maxRecDepth 1000000 in
private theorem leaf5844LocalValidity :
    LeafFacts leaf5844Box leaf5844Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5844Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356709376) }) = true
      norm_num [leaf5844Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5844CertificateValid :
    WideCertificateValid leaf5844Box leaf5844Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi261ValidityFacts
    leaf5844LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5844CoverageChecked :
    coverageCheck (innerAD leaf5844Box) leaf5844InnerLog = true := by
  rfl'

private theorem leaf5844InnerLogValid :
    leaf5844InnerLog.Valid 8 (innerAD leaf5844Box) :=
  wideLogDataValid_of_cachedCheck endpoint425PositiveFacts
    endpoint426PositiveFacts.valid leaf5844CoverageChecked

private noncomputable def leaf5844InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907393/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5844InputLogOnePlusV_eq :
    leaf5844InputLogOnePlusV = outerEnclosure 24
      (leaf5844Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5844RoundedFacts : LeafRoundedFacts 8
    leaf5844Certificate.logOnePlusV leaf5844InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5844InputLogOnePlusV_eq }

private noncomputable def leaf5844Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi261InputQChi innerPair677Input
    leaf5844InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5844LowerChecked :
    lowerCheck 24 leaf5844Box leaf5844Inputs = true := by
  rfl'

private theorem leaf5844CoversExact : CoversExact 8
    leaf5844Box leaf5844Certificate leaf5844InnerLog leaf5844Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi261RoundedFacts
    innerPair677RoundedFacts leaf5844RoundedFacts (by rfl)

private theorem leaf5844FlatSound : Sound leaf5844Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5844CertificateValid
    leaf5844InnerLogValid leaf5844CoversExact leaf5844LowerChecked

private noncomputable def leaf5845Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5845Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435789/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356676608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (649405405/536870912) }, upper := { exponent := 1, mantissa := (2519/2048) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715399167/68713353216) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5845InnerLog : WideLogData :=
  innerPair589Data

set_option maxRecDepth 1000000 in
private theorem leaf5845LocalValidity :
    LeafFacts leaf5845Box leaf5845Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5845Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356676608) }) = true
      norm_num [leaf5845Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5845CertificateValid :
    WideCertificateValid leaf5845Box leaf5845Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi262ValidityFacts
    leaf5845LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5845CoverageChecked :
    coverageCheck (innerAD leaf5845Box) leaf5845InnerLog = true := by
  rfl'

private theorem leaf5845InnerLogValid :
    leaf5845InnerLog.Valid 8 (innerAD leaf5845Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint94PositiveFacts.valid leaf5845CoverageChecked

private noncomputable def leaf5845InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907395/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5845InputLogOnePlusV_eq :
    leaf5845InputLogOnePlusV = outerEnclosure 24
      (leaf5845Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5845RoundedFacts : LeafRoundedFacts 8
    leaf5845Certificate.logOnePlusV leaf5845InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5845InputLogOnePlusV_eq }

private noncomputable def leaf5845Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi262InputQChi innerPair589Input
    leaf5845InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5845LowerChecked :
    lowerCheck 24 leaf5845Box leaf5845Inputs = true := by
  rfl'

private theorem leaf5845CoversExact : CoversExact 8
    leaf5845Box leaf5845Certificate leaf5845InnerLog leaf5845Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi262RoundedFacts
    innerPair589RoundedFacts leaf5845RoundedFacts (by rfl)

private theorem leaf5845FlatSound : Sound leaf5845Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5845CertificateValid
    leaf5845InnerLogValid leaf5845CoversExact leaf5845LowerChecked

private noncomputable def leaf5846Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5846Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435791/268435456) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356649984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (652747535/536870912) }, upper := { exponent := 1, mantissa := (633/512) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715372543/68713299968) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5846InnerLog : WideLogData :=
  innerPair666Data

set_option maxRecDepth 1000000 in
private theorem leaf5846LocalValidity :
    LeafFacts leaf5846Box leaf5846Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5846Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356649984) }) = true
      norm_num [leaf5846Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5846CertificateValid :
    WideCertificateValid leaf5846Box leaf5846Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi262ValidityFacts
    leaf5846LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5846CoverageChecked :
    coverageCheck (innerAD leaf5846Box) leaf5846InnerLog = true := by
  rfl'

private theorem leaf5846InnerLogValid :
    leaf5846InnerLog.Valid 8 (innerAD leaf5846Box) :=
  wideLogDataValid_of_cachedCheck endpoint413PositiveFacts
    endpoint427PositiveFacts.valid leaf5846CoverageChecked

private noncomputable def leaf5846InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629587/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5846InputLogOnePlusV_eq :
    leaf5846InputLogOnePlusV = outerEnclosure 24
      (leaf5846Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5846RoundedFacts : LeafRoundedFacts 8
    leaf5846Certificate.logOnePlusV leaf5846InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5846InputLogOnePlusV_eq }

private noncomputable def leaf5846Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi262InputQChi innerPair666Input
    leaf5846InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5846LowerChecked :
    lowerCheck 24 leaf5846Box leaf5846Inputs = true := by
  rfl'

private theorem leaf5846CoversExact : CoversExact 8
    leaf5846Box leaf5846Certificate leaf5846InnerLog leaf5846Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi262RoundedFacts
    innerPair666RoundedFacts leaf5846RoundedFacts (by rfl)

private theorem leaf5846FlatSound : Sound leaf5846Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5846CertificateValid
    leaf5846InnerLogValid leaf5846CoversExact leaf5846LowerChecked

private noncomputable def leaf5847Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5847Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871339/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356833024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1266602071/1073741824) }, upper := { exponent := 1, mantissa := (19541/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715555583/68713666048) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5847InnerLog : WideLogData :=
  innerPair569Data

set_option maxRecDepth 1000000 in
private theorem leaf5847LocalValidity :
    LeafFacts leaf5847Box leaf5847Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5847Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356833024) }) = true
      norm_num [leaf5847Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5847CertificateValid :
    WideCertificateValid leaf5847Box leaf5847Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi305ValidityFacts
    leaf5847LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5847CoverageChecked :
    coverageCheck (innerAD leaf5847Box) leaf5847InnerLog = true := by
  rfl'

private theorem leaf5847InnerLogValid :
    leaf5847InnerLog.Valid 8 (innerAD leaf5847Box) :=
  wideLogDataValid_of_cachedCheck endpoint297PositiveFacts
    endpoint304PositiveFacts.valid leaf5847CoverageChecked

private noncomputable def leaf5847InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5847InputLogOnePlusV_eq :
    leaf5847InputLogOnePlusV = outerEnclosure 24
      (leaf5847Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5847RoundedFacts : LeafRoundedFacts 8
    leaf5847Certificate.logOnePlusV leaf5847InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5847InputLogOnePlusV_eq }

private noncomputable def leaf5847Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi305InputQChi innerPair569Input
    leaf5847InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5847LowerChecked :
    lowerCheck 24 leaf5847Box leaf5847Inputs = true := by
  rfl'

private theorem leaf5847CoversExact : CoversExact 8
    leaf5847Box leaf5847Certificate leaf5847InnerLog leaf5847Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi305RoundedFacts
    innerPair569RoundedFacts leaf5847RoundedFacts (by rfl)

private theorem leaf5847FlatSound : Sound leaf5847Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5847CertificateValid
    leaf5847InnerLogValid leaf5847CoversExact leaf5847LowerChecked

private noncomputable def leaf5848Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5848Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020988416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1274203781/1073741824) }, upper := { exponent := 1, mantissa := (9829/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042089743/4041976832) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5848InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5848LocalValidity :
    LeafFacts leaf5848Box leaf5848Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5848Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020988416) }) = true
      norm_num [leaf5848Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5848CertificateValid :
    WideCertificateValid leaf5848Box leaf5848Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi306ValidityFacts
    leaf5848LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5848CoverageChecked :
    coverageCheck (innerAD leaf5848Box) leaf5848InnerLog = true := by
  rfl'

private theorem leaf5848InnerLogValid :
    leaf5848InnerLog.Valid 8 (innerAD leaf5848Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5848CoverageChecked

private noncomputable def leaf5848InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629549/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5848InputLogOnePlusV_eq :
    leaf5848InputLogOnePlusV = outerEnclosure 24
      (leaf5848Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5848RoundedFacts : LeafRoundedFacts 8
    leaf5848Certificate.logOnePlusV leaf5848InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5848InputLogOnePlusV_eq }

private noncomputable def leaf5848Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi306InputQChi innerPair273Input
    leaf5848InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5848LowerChecked :
    lowerCheck 24 leaf5848Box leaf5848Inputs = true := by
  rfl'

private theorem leaf5848CoversExact : CoversExact 8
    leaf5848Box leaf5848Certificate leaf5848InnerLog leaf5848Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi306RoundedFacts
    innerPair273RoundedFacts leaf5848RoundedFacts (by rfl)

private theorem leaf5848FlatSound : Sound leaf5848Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5848CertificateValid
    leaf5848InnerLogValid leaf5848CoversExact leaf5848LowerChecked

private noncomputable def leaf5849Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5849Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871341/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908115456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1272893141/1073741824) }, upper := { exponent := 1, mantissa := (9819/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816504393/9816230912) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5849InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf5849LocalValidity :
    LeafFacts leaf5849Box leaf5849Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5849Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908115456) }) = true
      norm_num [leaf5849Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5849CertificateValid :
    WideCertificateValid leaf5849Box leaf5849Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi305ValidityFacts
    leaf5849LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5849CoverageChecked :
    coverageCheck (innerAD leaf5849Box) leaf5849InnerLog = true := by
  rfl'

private theorem leaf5849InnerLogValid :
    leaf5849InnerLog.Valid 8 (innerAD leaf5849Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf5849CoverageChecked

private noncomputable def leaf5849InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907387/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5849InputLogOnePlusV_eq :
    leaf5849InputLogOnePlusV = outerEnclosure 24
      (leaf5849Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5849RoundedFacts : LeafRoundedFacts 8
    leaf5849Certificate.logOnePlusV leaf5849InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5849InputLogOnePlusV_eq }

private noncomputable def leaf5849Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi305InputQChi innerPair273Input
    leaf5849InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5849LowerChecked :
    lowerCheck 24 leaf5849Box leaf5849Inputs = true := by
  rfl'

private theorem leaf5849CoversExact : CoversExact 8
    leaf5849Box leaf5849Certificate leaf5849InnerLog leaf5849Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi305RoundedFacts
    innerPair273RoundedFacts leaf5849RoundedFacts (by rfl)

private theorem leaf5849FlatSound : Sound leaf5849Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5849CertificateValid
    leaf5849InnerLogValid leaf5849CoversExact leaf5849LowerChecked

private noncomputable def leaf5850Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5850Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356777984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1280560383/1073741824) }, upper := { exponent := 1, mantissa := (4939/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715500543/68713555968) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5850InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5850LocalValidity :
    LeafFacts leaf5850Box leaf5850Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5850Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356777984) }) = true
      norm_num [leaf5850Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5850CertificateValid :
    WideCertificateValid leaf5850Box leaf5850Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi306ValidityFacts
    leaf5850LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5850CoverageChecked :
    coverageCheck (innerAD leaf5850Box) leaf5850InnerLog = true := by
  rfl'

private theorem leaf5850InnerLogValid :
    leaf5850InnerLog.Valid 8 (innerAD leaf5850Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5850CoverageChecked

private noncomputable def leaf5850InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907389/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5850InputLogOnePlusV_eq :
    leaf5850InputLogOnePlusV = outerEnclosure 24
      (leaf5850Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5850RoundedFacts : LeafRoundedFacts 8
    leaf5850Certificate.logOnePlusV leaf5850InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5850InputLogOnePlusV_eq }

private noncomputable def leaf5850Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi306InputQChi innerPair278Input
    leaf5850InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5850LowerChecked :
    lowerCheck 24 leaf5850Box leaf5850Inputs = true := by
  rfl'

private theorem leaf5850CoversExact : CoversExact 8
    leaf5850Box leaf5850Certificate leaf5850InnerLog leaf5850Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi306RoundedFacts
    innerPair278RoundedFacts leaf5850RoundedFacts (by rfl)

private theorem leaf5850FlatSound : Sound leaf5850Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5850CertificateValid
    leaf5850InnerLogValid leaf5850CoversExact leaf5850LowerChecked

private noncomputable def leaf5851Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5851Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356773120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1281805491/1073741824) }, upper := { exponent := 1, mantissa := (19775/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715495679/68713546240) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5851InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5851LocalValidity :
    LeafFacts leaf5851Box leaf5851Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5851Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356773120) }) = true
      norm_num [leaf5851Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5851CertificateValid :
    WideCertificateValid leaf5851Box leaf5851Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi307ValidityFacts
    leaf5851LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5851CoverageChecked :
    coverageCheck (innerAD leaf5851Box) leaf5851InnerLog = true := by
  rfl'

private theorem leaf5851InnerLogValid :
    leaf5851InnerLog.Valid 8 (innerAD leaf5851Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5851CoverageChecked

private noncomputable def leaf5851InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629557/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5851InputLogOnePlusV_eq :
    leaf5851InputLogOnePlusV = outerEnclosure 24
      (leaf5851Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5851RoundedFacts : LeafRoundedFacts 8
    leaf5851Certificate.logOnePlusV leaf5851InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5851InputLogOnePlusV_eq }

private noncomputable def leaf5851Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi307InputQChi innerPair278Input
    leaf5851InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5851LowerChecked :
    lowerCheck 24 leaf5851Box leaf5851Inputs = true := by
  rfl'

private theorem leaf5851CoversExact : CoversExact 8
    leaf5851Box leaf5851Certificate leaf5851InnerLog leaf5851Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi307RoundedFacts
    innerPair278RoundedFacts leaf5851RoundedFacts (by rfl)

private theorem leaf5851FlatSound : Sound leaf5851Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5851CertificateValid
    leaf5851InnerLogValid leaf5851CoversExact leaf5851LowerChecked

private noncomputable def leaf5852Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5852Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356743168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1289407201/1073741824) }, upper := { exponent := 1, mantissa := (4973/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715465727/68713486336) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5852InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5852LocalValidity :
    LeafFacts leaf5852Box leaf5852Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5852Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356743168) }) = true
      norm_num [leaf5852Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5852CertificateValid :
    WideCertificateValid leaf5852Box leaf5852Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi308ValidityFacts
    leaf5852LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5852CoverageChecked :
    coverageCheck (innerAD leaf5852Box) leaf5852InnerLog = true := by
  rfl'

private theorem leaf5852InnerLogValid :
    leaf5852InnerLog.Valid 8 (innerAD leaf5852Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5852CoverageChecked

private noncomputable def leaf5852InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907391/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5852InputLogOnePlusV_eq :
    leaf5852InputLogOnePlusV = outerEnclosure 24
      (leaf5852Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5852RoundedFacts : LeafRoundedFacts 8
    leaf5852Certificate.logOnePlusV leaf5852InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5852InputLogOnePlusV_eq }

private noncomputable def leaf5852Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi308InputQChi innerPair278Input
    leaf5852InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5852LowerChecked :
    lowerCheck 24 leaf5852Box leaf5852Inputs = true := by
  rfl'

private theorem leaf5852CoversExact : CoversExact 8
    leaf5852Box leaf5852Certificate leaf5852InnerLog leaf5852Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi308RoundedFacts
    innerPair278RoundedFacts leaf5852RoundedFacts (by rfl)

private theorem leaf5852FlatSound : Sound leaf5852Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5852CertificateValid
    leaf5852InnerLogValid leaf5852CoversExact leaf5852LowerChecked

private noncomputable def leaf5853Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5853Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356747776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1288227625/1073741824) }, upper := { exponent := 1, mantissa := (9937/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715470335/68713495552) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5853InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5853LocalValidity :
    LeafFacts leaf5853Box leaf5853Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5853Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356747776) }) = true
      norm_num [leaf5853Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5853CertificateValid :
    WideCertificateValid leaf5853Box leaf5853Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi307ValidityFacts
    leaf5853LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5853CoverageChecked :
    coverageCheck (innerAD leaf5853Box) leaf5853InnerLog = true := by
  rfl'

private theorem leaf5853InnerLogValid :
    leaf5853InnerLog.Valid 8 (innerAD leaf5853Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5853CoverageChecked

private noncomputable def leaf5853InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5853InputLogOnePlusV_eq :
    leaf5853InputLogOnePlusV = outerEnclosure 24
      (leaf5853Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5853RoundedFacts : LeafRoundedFacts 8
    leaf5853Certificate.logOnePlusV leaf5853InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5853InputLogOnePlusV_eq }

private noncomputable def leaf5853Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi307InputQChi innerPair278Input
    leaf5853InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5853LowerChecked :
    lowerCheck 24 leaf5853Box leaf5853Inputs = true := by
  rfl'

private theorem leaf5853CoversExact : CoversExact 8
    leaf5853Box leaf5853Certificate leaf5853InnerLog leaf5853Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi307RoundedFacts
    innerPair278RoundedFacts leaf5853RoundedFacts (by rfl)

private theorem leaf5853FlatSound : Sound leaf5853Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5853CertificateValid
    leaf5853InnerLogValid leaf5853CoversExact leaf5853LowerChecked

private noncomputable def leaf5854Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5854Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356717568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1295894867/1073741824) }, upper := { exponent := 1, mantissa := (2499/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715440127/68713435136) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5854InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5854LocalValidity :
    LeafFacts leaf5854Box leaf5854Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5854Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356717568) }) = true
      norm_num [leaf5854Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5854CertificateValid :
    WideCertificateValid leaf5854Box leaf5854Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi308ValidityFacts
    leaf5854LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5854CoverageChecked :
    coverageCheck (innerAD leaf5854Box) leaf5854InnerLog = true := by
  rfl'

private theorem leaf5854InnerLogValid :
    leaf5854InnerLog.Valid 8 (innerAD leaf5854Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5854CoverageChecked

private noncomputable def leaf5854InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814785/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5854InputLogOnePlusV_eq :
    leaf5854InputLogOnePlusV = outerEnclosure 24
      (leaf5854Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5854RoundedFacts : LeafRoundedFacts 8
    leaf5854Certificate.logOnePlusV leaf5854InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5854InputLogOnePlusV_eq }

private noncomputable def leaf5854Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi308InputQChi innerPair590Input
    leaf5854InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5854LowerChecked :
    lowerCheck 24 leaf5854Box leaf5854Inputs = true := by
  rfl'

private theorem leaf5854CoversExact : CoversExact 8
    leaf5854Box leaf5854Certificate leaf5854InnerLog leaf5854Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi308RoundedFacts
    innerPair590RoundedFacts leaf5854RoundedFacts (by rfl)

private theorem leaf5854FlatSound : Sound leaf5854Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5854CertificateValid
    leaf5854InnerLogValid leaf5854CoversExact leaf5854LowerChecked

private noncomputable def leaf5855Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5855Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871343/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356783360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1279184211/1073741824) }, upper := { exponent := 1, mantissa := (19735/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715505919/68713566720) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5855InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5855LocalValidity :
    LeafFacts leaf5855Box leaf5855Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5855Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356783360) }) = true
      norm_num [leaf5855Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5855CertificateValid :
    WideCertificateValid leaf5855Box leaf5855Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi305ValidityFacts
    leaf5855LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5855CoverageChecked :
    coverageCheck (innerAD leaf5855Box) leaf5855InnerLog = true := by
  rfl'

private theorem leaf5855InnerLogValid :
    leaf5855InnerLog.Valid 8 (innerAD leaf5855Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5855CoverageChecked

private noncomputable def leaf5855InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814777/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5855InputLogOnePlusV_eq :
    leaf5855InputLogOnePlusV = outerEnclosure 24
      (leaf5855Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5855RoundedFacts : LeafRoundedFacts 8
    leaf5855Certificate.logOnePlusV leaf5855InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5855InputLogOnePlusV_eq }

private noncomputable def leaf5855Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi305InputQChi innerPair278Input
    leaf5855InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5855LowerChecked :
    lowerCheck 24 leaf5855Box leaf5855Inputs = true := by
  rfl'

private theorem leaf5855CoversExact : CoversExact 8
    leaf5855Box leaf5855Certificate leaf5855InnerLog leaf5855Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi305RoundedFacts
    innerPair278RoundedFacts leaf5855RoundedFacts (by rfl)

private theorem leaf5855FlatSound : Sound leaf5855Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5855CertificateValid
    leaf5855InnerLogValid leaf5855CoversExact leaf5855LowerChecked

private noncomputable def leaf5856Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5856Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356752896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1286916985/1073741824) }, upper := { exponent := 1, mantissa := (9927/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715475455/68713505792) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5856InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5856LocalValidity :
    LeafFacts leaf5856Box leaf5856Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5856Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356752896) }) = true
      norm_num [leaf5856Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5856CertificateValid :
    WideCertificateValid leaf5856Box leaf5856Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi306ValidityFacts
    leaf5856LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5856CoverageChecked :
    coverageCheck (innerAD leaf5856Box) leaf5856InnerLog = true := by
  rfl'

private theorem leaf5856InnerLogValid :
    leaf5856InnerLog.Valid 8 (innerAD leaf5856Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5856CoverageChecked

private noncomputable def leaf5856InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814781/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5856InputLogOnePlusV_eq :
    leaf5856InputLogOnePlusV = outerEnclosure 24
      (leaf5856Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5856RoundedFacts : LeafRoundedFacts 8
    leaf5856Certificate.logOnePlusV leaf5856InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5856InputLogOnePlusV_eq }

private noncomputable def leaf5856Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi306InputQChi innerPair278Input
    leaf5856InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5856LowerChecked :
    lowerCheck 24 leaf5856Box leaf5856Inputs = true := by
  rfl'

private theorem leaf5856CoversExact : CoversExact 8
    leaf5856Box leaf5856Certificate leaf5856InnerLog leaf5856Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi306RoundedFacts
    innerPair278RoundedFacts leaf5856RoundedFacts (by rfl)

private theorem leaf5856FlatSound : Sound leaf5856Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5856CertificateValid
    leaf5856InnerLogValid leaf5856CoversExact leaf5856LowerChecked

private noncomputable def leaf5857Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (3/8), chiHi := (97/256) }

private noncomputable def leaf5857Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871345/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356758528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1285475281/1073741824) }, upper := { exponent := 1, mantissa := (2479/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi305LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715481087/68713517056) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5857InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5857LocalValidity :
    LeafFacts leaf5857Box leaf5857Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5857Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356758528) }) = true
      norm_num [leaf5857Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5857CertificateValid :
    WideCertificateValid leaf5857Box leaf5857Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi305ValidityFacts
    leaf5857LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5857CoverageChecked :
    coverageCheck (innerAD leaf5857Box) leaf5857InnerLog = true := by
  rfl'

private theorem leaf5857InnerLogValid :
    leaf5857InnerLog.Valid 8 (innerAD leaf5857Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5857CoverageChecked

private noncomputable def leaf5857InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5857InputLogOnePlusV_eq :
    leaf5857InputLogOnePlusV = outerEnclosure 24
      (leaf5857Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5857RoundedFacts : LeafRoundedFacts 8
    leaf5857Certificate.logOnePlusV leaf5857InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5857InputLogOnePlusV_eq }

private noncomputable def leaf5857Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi305InputQChi innerPair278Input
    leaf5857InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5857LowerChecked :
    lowerCheck 24 leaf5857Box leaf5857Inputs = true := by
  rfl'

private theorem leaf5857CoversExact : CoversExact 8
    leaf5857Box leaf5857Certificate leaf5857InnerLog leaf5857Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi305RoundedFacts
    innerPair278RoundedFacts leaf5857RoundedFacts (by rfl)

private theorem leaf5857FlatSound : Sound leaf5857Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5857CertificateValid
    leaf5857InnerLogValid leaf5857CoversExact leaf5857LowerChecked

private noncomputable def leaf5858Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (97/256), chiHi := (49/128) }

private noncomputable def leaf5858Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356727808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1293273587/1073741824) }, upper := { exponent := 1, mantissa := (1247/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi306LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715450367/68713455616) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5858InnerLog : WideLogData :=
  innerPair278Data

set_option maxRecDepth 1000000 in
private theorem leaf5858LocalValidity :
    LeafFacts leaf5858Box leaf5858Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5858Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356727808) }) = true
      norm_num [leaf5858Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5858CertificateValid :
    WideCertificateValid leaf5858Box leaf5858Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi306ValidityFacts
    leaf5858LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5858CoverageChecked :
    coverageCheck (innerAD leaf5858Box) leaf5858InnerLog = true := by
  rfl'

private theorem leaf5858InnerLogValid :
    leaf5858InnerLog.Valid 8 (innerAD leaf5858Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint78PositiveFacts.valid leaf5858CoverageChecked

private noncomputable def leaf5858InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf5858InputLogOnePlusV_eq :
    leaf5858InputLogOnePlusV = outerEnclosure 24
      (leaf5858Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5858RoundedFacts : LeafRoundedFacts 8
    leaf5858Certificate.logOnePlusV leaf5858InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5858InputLogOnePlusV_eq }

private noncomputable def leaf5858Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi306InputQChi innerPair278Input
    leaf5858InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5858LowerChecked :
    lowerCheck 24 leaf5858Box leaf5858Inputs = true := by
  rfl'

private theorem leaf5858CoversExact : CoversExact 8
    leaf5858Box leaf5858Certificate leaf5858InnerLog leaf5858Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi306RoundedFacts
    innerPair278RoundedFacts leaf5858RoundedFacts (by rfl)

private theorem leaf5858FlatSound : Sound leaf5858Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5858CertificateValid
    leaf5858InnerLogValid leaf5858CoversExact leaf5858LowerChecked

private noncomputable def leaf5859Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5859Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356722432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1294649759/1073741824) }, upper := { exponent := 1, mantissa := (19973/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715444991/68713444864) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5859InnerLog : WideLogData :=
  innerPair590Data

set_option maxRecDepth 1000000 in
private theorem leaf5859LocalValidity :
    LeafFacts leaf5859Box leaf5859Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5859Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356722432) }) = true
      norm_num [leaf5859Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5859CertificateValid :
    WideCertificateValid leaf5859Box leaf5859Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi307ValidityFacts
    leaf5859LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5859CoverageChecked :
    coverageCheck (innerAD leaf5859Box) leaf5859InnerLog = true := by
  rfl'

private theorem leaf5859InnerLogValid :
    leaf5859InnerLog.Valid 8 (innerAD leaf5859Box) :=
  wideLogDataValid_of_cachedCheck endpoint305PositiveFacts
    endpoint403PositiveFacts.valid leaf5859CoverageChecked

private noncomputable def leaf5859InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629569/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5859InputLogOnePlusV_eq :
    leaf5859InputLogOnePlusV = outerEnclosure 24
      (leaf5859Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5859RoundedFacts : LeafRoundedFacts 8
    leaf5859Certificate.logOnePlusV leaf5859InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5859InputLogOnePlusV_eq }

private noncomputable def leaf5859Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi307InputQChi innerPair590Input
    leaf5859InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5859LowerChecked :
    lowerCheck 24 leaf5859Box leaf5859Inputs = true := by
  rfl'

private theorem leaf5859CoversExact : CoversExact 8
    leaf5859Box leaf5859Certificate leaf5859InnerLog leaf5859Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi307RoundedFacts
    innerPair590RoundedFacts leaf5859RoundedFacts (by rfl)

private theorem leaf5859FlatSound : Sound leaf5859Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5859CertificateValid
    leaf5859InnerLogValid leaf5859CoversExact leaf5859LowerChecked

private noncomputable def leaf5860Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5860Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356691968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1302382533/1073741824) }, upper := { exponent := 1, mantissa := (5023/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715414527/68713383936) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5860InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5860LocalValidity :
    LeafFacts leaf5860Box leaf5860Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5860Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356691968) }) = true
      norm_num [leaf5860Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5860CertificateValid :
    WideCertificateValid leaf5860Box leaf5860Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi308ValidityFacts
    leaf5860LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5860CoverageChecked :
    coverageCheck (innerAD leaf5860Box) leaf5860InnerLog = true := by
  rfl'

private theorem leaf5860InnerLogValid :
    leaf5860InnerLog.Valid 8 (innerAD leaf5860Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5860CoverageChecked

private noncomputable def leaf5860InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5860InputLogOnePlusV_eq :
    leaf5860InputLogOnePlusV = outerEnclosure 24
      (leaf5860Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5860RoundedFacts : LeafRoundedFacts 8
    leaf5860Certificate.logOnePlusV leaf5860InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5860InputLogOnePlusV_eq }

private noncomputable def leaf5860Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi308InputQChi innerPair279Input
    leaf5860InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5860LowerChecked :
    lowerCheck 24 leaf5860Box leaf5860Inputs = true := by
  rfl'

private theorem leaf5860CoversExact : CoversExact 8
    leaf5860Box leaf5860Certificate leaf5860InnerLog leaf5860Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi308RoundedFacts
    innerPair279RoundedFacts leaf5860RoundedFacts (by rfl)

private theorem leaf5860FlatSound : Sound leaf5860Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5860CertificateValid
    leaf5860InnerLogValid leaf5860CoversExact leaf5860LowerChecked

private noncomputable def leaf5861Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (49/128), chiHi := (99/256) }

private noncomputable def leaf5861Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908099584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1301071893/1073741824) }, upper := { exponent := 1, mantissa := (2509/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi307LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816488521/9816199168) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5861InnerLog : WideLogData :=
  innerPair593Data

set_option maxRecDepth 1000000 in
private theorem leaf5861LocalValidity :
    LeafFacts leaf5861Box leaf5861Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5861Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908099584) }) = true
      norm_num [leaf5861Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5861CertificateValid :
    WideCertificateValid leaf5861Box leaf5861Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi307ValidityFacts
    leaf5861LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5861CoverageChecked :
    coverageCheck (innerAD leaf5861Box) leaf5861InnerLog = true := by
  rfl'

private theorem leaf5861InnerLogValid :
    leaf5861InnerLog.Valid 8 (innerAD leaf5861Box) :=
  wideLogDataValid_of_cachedCheck endpoint308PositiveFacts
    endpoint403PositiveFacts.valid leaf5861CoverageChecked

private noncomputable def leaf5861InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5861InputLogOnePlusV_eq :
    leaf5861InputLogOnePlusV = outerEnclosure 24
      (leaf5861Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5861RoundedFacts : LeafRoundedFacts 8
    leaf5861Certificate.logOnePlusV leaf5861InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5861InputLogOnePlusV_eq }

private noncomputable def leaf5861Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi307InputQChi innerPair593Input
    leaf5861InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5861LowerChecked :
    lowerCheck 24 leaf5861Box leaf5861Inputs = true := by
  rfl'

private theorem leaf5861CoversExact : CoversExact 8
    leaf5861Box leaf5861Certificate leaf5861InnerLog leaf5861Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi307RoundedFacts
    innerPair593RoundedFacts leaf5861RoundedFacts (by rfl)

private theorem leaf5861FlatSound : Sound leaf5861Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5861CertificateValid
    leaf5861InnerLogValid leaf5861CoversExact leaf5861LowerChecked

private noncomputable def leaf5862Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (99/256), chiHi := (25/64) }

private noncomputable def leaf5862Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356666368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1308870199/1073741824) }, upper := { exponent := 1, mantissa := (631/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi308LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715388927/68713332736) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5862InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5862LocalValidity :
    LeafFacts leaf5862Box leaf5862Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5862Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356666368) }) = true
      norm_num [leaf5862Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5862CertificateValid :
    WideCertificateValid leaf5862Box leaf5862Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi308ValidityFacts
    leaf5862LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5862CoverageChecked :
    coverageCheck (innerAD leaf5862Box) leaf5862InnerLog = true := by
  rfl'

private theorem leaf5862InnerLogValid :
    leaf5862InnerLog.Valid 8 (innerAD leaf5862Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5862CoverageChecked

private noncomputable def leaf5862InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629583/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5862InputLogOnePlusV_eq :
    leaf5862InputLogOnePlusV = outerEnclosure 24
      (leaf5862Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5862RoundedFacts : LeafRoundedFacts 8
    leaf5862Certificate.logOnePlusV leaf5862InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5862InputLogOnePlusV_eq }

private noncomputable def leaf5862Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi308InputQChi innerPair285Input
    leaf5862InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5862LowerChecked :
    lowerCheck 24 leaf5862Box leaf5862Inputs = true := by
  rfl'

private theorem leaf5862CoversExact : CoversExact 8
    leaf5862Box leaf5862Certificate leaf5862InnerLog leaf5862Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi308RoundedFacts
    innerPair285RoundedFacts leaf5862RoundedFacts (by rfl)

private theorem leaf5862FlatSound : Sound leaf5862Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5862CertificateValid
    leaf5862InnerLogValid leaf5862CoversExact leaf5862LowerChecked

private noncomputable def leaf5863Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5863Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871347/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908101888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1297008911/1073741824) }, upper := { exponent := 1, mantissa := (20009/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816490825/9816203776) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5863InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5863LocalValidity :
    LeafFacts leaf5863Box leaf5863Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5863Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908101888) }) = true
      norm_num [leaf5863Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5863CertificateValid :
    WideCertificateValid leaf5863Box leaf5863Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi309ValidityFacts
    leaf5863LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5863CoverageChecked :
    coverageCheck (innerAD leaf5863Box) leaf5863InnerLog = true := by
  rfl'

private theorem leaf5863InnerLogValid :
    leaf5863InnerLog.Valid 8 (innerAD leaf5863Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5863CoverageChecked

private noncomputable def leaf5863InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5863InputLogOnePlusV_eq :
    leaf5863InputLogOnePlusV = outerEnclosure 24
      (leaf5863Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5863RoundedFacts : LeafRoundedFacts 8
    leaf5863Certificate.logOnePlusV leaf5863InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5863InputLogOnePlusV_eq }

private noncomputable def leaf5863Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi309InputQChi innerPair279Input
    leaf5863InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5863LowerChecked :
    lowerCheck 24 leaf5863Box leaf5863Inputs = true := by
  rfl'

private theorem leaf5863CoversExact : CoversExact 8
    leaf5863Box leaf5863Certificate leaf5863InnerLog leaf5863Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi309RoundedFacts
    innerPair279RoundedFacts leaf5863RoundedFacts (by rfl)

private theorem leaf5863FlatSound : Sound leaf5863Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5863CertificateValid
    leaf5863InnerLogValid leaf5863CoversExact leaf5863LowerChecked

private noncomputable def leaf5864Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5864Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356683264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1304610621/1073741824) }, upper := { exponent := 1, mantissa := (10063/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715405823/68713366528) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5864InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5864LocalValidity :
    LeafFacts leaf5864Box leaf5864Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5864Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356683264) }) = true
      norm_num [leaf5864Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5864CertificateValid :
    WideCertificateValid leaf5864Box leaf5864Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi310ValidityFacts
    leaf5864LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5864CoverageChecked :
    coverageCheck (innerAD leaf5864Box) leaf5864InnerLog = true := by
  rfl'

private theorem leaf5864InnerLogValid :
    leaf5864InnerLog.Valid 8 (innerAD leaf5864Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5864CoverageChecked

private noncomputable def leaf5864InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629579/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5864InputLogOnePlusV_eq :
    leaf5864InputLogOnePlusV = outerEnclosure 24
      (leaf5864Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5864RoundedFacts : LeafRoundedFacts 8
    leaf5864Certificate.logOnePlusV leaf5864InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5864InputLogOnePlusV_eq }

private noncomputable def leaf5864Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi310InputQChi innerPair279Input
    leaf5864InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5864LowerChecked :
    lowerCheck 24 leaf5864Box leaf5864Inputs = true := by
  rfl'

private theorem leaf5864CoversExact : CoversExact 8
    leaf5864Box leaf5864Certificate leaf5864InnerLog leaf5864Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi310RoundedFacts
    innerPair279RoundedFacts leaf5864RoundedFacts (by rfl)

private theorem leaf5864FlatSound : Sound leaf5864Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5864CertificateValid
    leaf5864InnerLogValid leaf5864CoversExact leaf5864LowerChecked

private noncomputable def leaf5865Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5865Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871349/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356687360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1303562109/1073741824) }, upper := { exponent := 1, mantissa := (10055/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715409919/68713374720) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5865InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf5865LocalValidity :
    LeafFacts leaf5865Box leaf5865Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5865Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356687360) }) = true
      norm_num [leaf5865Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5865CertificateValid :
    WideCertificateValid leaf5865Box leaf5865Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi309ValidityFacts
    leaf5865LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5865CoverageChecked :
    coverageCheck (innerAD leaf5865Box) leaf5865InnerLog = true := by
  rfl'

private theorem leaf5865InnerLogValid :
    leaf5865InnerLog.Valid 8 (innerAD leaf5865Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf5865CoverageChecked

private noncomputable def leaf5865InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814789/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5865InputLogOnePlusV_eq :
    leaf5865InputLogOnePlusV = outerEnclosure 24
      (leaf5865Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5865RoundedFacts : LeafRoundedFacts 8
    leaf5865Certificate.logOnePlusV leaf5865InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5865InputLogOnePlusV_eq }

private noncomputable def leaf5865Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi309InputQChi innerPair279Input
    leaf5865InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5865LowerChecked :
    lowerCheck 24 leaf5865Box leaf5865Inputs = true := by
  rfl'

private theorem leaf5865CoversExact : CoversExact 8
    leaf5865Box leaf5865Certificate leaf5865InnerLog leaf5865Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi309RoundedFacts
    innerPair279RoundedFacts leaf5865RoundedFacts (by rfl)

private theorem leaf5865FlatSound : Sound leaf5865Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5865CertificateValid
    leaf5865InnerLogValid leaf5865CoversExact leaf5865LowerChecked

private noncomputable def leaf5866Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5866Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356657152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1311229351/1073741824) }, upper := { exponent := 1, mantissa := (5057/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715379711/68713314304) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5866InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5866LocalValidity :
    LeafFacts leaf5866Box leaf5866Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5866Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356657152) }) = true
      norm_num [leaf5866Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5866CertificateValid :
    WideCertificateValid leaf5866Box leaf5866Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi310ValidityFacts
    leaf5866LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5866CoverageChecked :
    coverageCheck (innerAD leaf5866Box) leaf5866InnerLog = true := by
  rfl'

private theorem leaf5866InnerLogValid :
    leaf5866InnerLog.Valid 8 (innerAD leaf5866Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5866CoverageChecked

private noncomputable def leaf5866InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629585/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5866InputLogOnePlusV_eq :
    leaf5866InputLogOnePlusV = outerEnclosure 24
      (leaf5866Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5866RoundedFacts : LeafRoundedFacts 8
    leaf5866Certificate.logOnePlusV leaf5866InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5866InputLogOnePlusV_eq }

private noncomputable def leaf5866Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi310InputQChi innerPair285Input
    leaf5866InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5866LowerChecked :
    lowerCheck 24 leaf5866Box leaf5866Inputs = true := by
  rfl'

private theorem leaf5866CoversExact : CoversExact 8
    leaf5866Box leaf5866Certificate leaf5866InnerLog leaf5866Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi310RoundedFacts
    innerPair285RoundedFacts leaf5866RoundedFacts (by rfl)

private theorem leaf5866FlatSound : Sound leaf5866Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5866CertificateValid
    leaf5866InnerLogValid leaf5866CoversExact leaf5866LowerChecked

private noncomputable def leaf5867Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5867Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435793/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713246720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (656089665/536870912) }, upper := { exponent := 1, mantissa := (2545/2048) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429643261/137426493440) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5867InnerLog : WideLogData :=
  innerPair678Data

set_option maxRecDepth 1000000 in
private theorem leaf5867LocalValidity :
    LeafFacts leaf5867Box leaf5867Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5867Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713246720) }) = true
      norm_num [leaf5867Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5867CertificateValid :
    WideCertificateValid leaf5867Box leaf5867Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi262ValidityFacts
    leaf5867LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5867CoverageChecked :
    coverageCheck (innerAD leaf5867Box) leaf5867InnerLog = true := by
  rfl'

private theorem leaf5867InnerLogValid :
    leaf5867InnerLog.Valid 8 (innerAD leaf5867Box) :=
  wideLogDataValid_of_cachedCheck endpoint428PositiveFacts
    endpoint429PositiveFacts.valid leaf5867CoverageChecked

private noncomputable def leaf5867InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5867InputLogOnePlusV_eq :
    leaf5867InputLogOnePlusV = outerEnclosure 24
      (leaf5867Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5867RoundedFacts : LeafRoundedFacts 8
    leaf5867Certificate.logOnePlusV leaf5867InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5867InputLogOnePlusV_eq }

private noncomputable def leaf5867Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi262InputQChi innerPair678Input
    leaf5867InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5867LowerChecked :
    lowerCheck 24 leaf5867Box leaf5867Inputs = true := by
  rfl'

private theorem leaf5867CoversExact : CoversExact 8
    leaf5867Box leaf5867Certificate leaf5867InnerLog leaf5867Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi262RoundedFacts
    innerPair678RoundedFacts leaf5867RoundedFacts (by rfl)

private theorem leaf5867FlatSound : Sound leaf5867Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5867CertificateValid
    leaf5867InnerLogValid leaf5867CoversExact leaf5867LowerChecked

private noncomputable def leaf5868Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (51/128), chiHi := (13/32) }

private noncomputable def leaf5868Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435795/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713193472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (659431795/536870912) }, upper := { exponent := 1, mantissa := (1279/1024) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi262LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429590013/137426386944) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5868InnerLog : WideLogData :=
  innerPair679Data

set_option maxRecDepth 1000000 in
private theorem leaf5868LocalValidity :
    LeafFacts leaf5868Box leaf5868Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5868Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713193472) }) = true
      norm_num [leaf5868Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5868CertificateValid :
    WideCertificateValid leaf5868Box leaf5868Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi262ValidityFacts
    leaf5868LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5868CoverageChecked :
    coverageCheck (innerAD leaf5868Box) leaf5868InnerLog = true := by
  rfl'

private theorem leaf5868InnerLogValid :
    leaf5868InnerLog.Valid 8 (innerAD leaf5868Box) :=
  wideLogDataValid_of_cachedCheck endpoint430PositiveFacts
    endpoint431PositiveFacts.valid leaf5868CoverageChecked

private noncomputable def leaf5868InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5868InputLogOnePlusV_eq :
    leaf5868InputLogOnePlusV = outerEnclosure 24
      (leaf5868Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5868RoundedFacts : LeafRoundedFacts 8
    leaf5868Certificate.logOnePlusV leaf5868InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5868InputLogOnePlusV_eq }

private noncomputable def leaf5868Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi262InputQChi innerPair679Input
    leaf5868InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5868LowerChecked :
    lowerCheck 24 leaf5868Box leaf5868Inputs = true := by
  rfl'

private theorem leaf5868CoversExact : CoversExact 8
    leaf5868Box leaf5868Certificate leaf5868InnerLog leaf5868Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi262RoundedFacts
    innerPair679RoundedFacts leaf5868RoundedFacts (by rfl)

private theorem leaf5868FlatSound : Sound leaf5868Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5868CertificateValid
    leaf5868InnerLogValid leaf5868CoversExact leaf5868LowerChecked

private noncomputable def leaf5869Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5869Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871351/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356661504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1310115307/1073741824) }, upper := { exponent := 1, mantissa := (20211/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715384063/68713323008) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5869InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5869LocalValidity :
    LeafFacts leaf5869Box leaf5869Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5869Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356661504) }) = true
      norm_num [leaf5869Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5869CertificateValid :
    WideCertificateValid leaf5869Box leaf5869Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi309ValidityFacts
    leaf5869LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5869CoverageChecked :
    coverageCheck (innerAD leaf5869Box) leaf5869InnerLog = true := by
  rfl'

private theorem leaf5869InnerLogValid :
    leaf5869InnerLog.Valid 8 (innerAD leaf5869Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5869CoverageChecked

private noncomputable def leaf5869InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726849/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5869InputLogOnePlusV_eq :
    leaf5869InputLogOnePlusV = outerEnclosure 24
      (leaf5869Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5869RoundedFacts : LeafRoundedFacts 8
    leaf5869Certificate.logOnePlusV leaf5869InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5869InputLogOnePlusV_eq }

private noncomputable def leaf5869Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi309InputQChi innerPair285Input
    leaf5869InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5869LowerChecked :
    lowerCheck 24 leaf5869Box leaf5869Inputs = true := by
  rfl'

private theorem leaf5869CoversExact : CoversExact 8
    leaf5869Box leaf5869Certificate leaf5869InnerLog leaf5869Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi309RoundedFacts
    innerPair285RoundedFacts leaf5869RoundedFacts (by rfl)

private theorem leaf5869FlatSound : Sound leaf5869Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5869CertificateValid
    leaf5869InnerLogValid leaf5869CoversExact leaf5869LowerChecked

private noncomputable def leaf5870Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5870Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356631040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1317848081/1073741824) }, upper := { exponent := 1, mantissa := (10165/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715353599/68713262080) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5870InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5870LocalValidity :
    LeafFacts leaf5870Box leaf5870Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5870Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356631040) }) = true
      norm_num [leaf5870Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5870CertificateValid :
    WideCertificateValid leaf5870Box leaf5870Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi310ValidityFacts
    leaf5870LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5870CoverageChecked :
    coverageCheck (innerAD leaf5870Box) leaf5870InnerLog = true := by
  rfl'

private theorem leaf5870InnerLogValid :
    leaf5870InnerLog.Valid 8 (innerAD leaf5870Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5870CoverageChecked

private noncomputable def leaf5870InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629591/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5870InputLogOnePlusV_eq :
    leaf5870InputLogOnePlusV = outerEnclosure 24
      (leaf5870Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5870RoundedFacts : LeafRoundedFacts 8
    leaf5870Certificate.logOnePlusV leaf5870InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5870InputLogOnePlusV_eq }

private noncomputable def leaf5870Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi310InputQChi innerPair285Input
    leaf5870InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5870LowerChecked :
    lowerCheck 24 leaf5870Box leaf5870Inputs = true := by
  rfl'

private theorem leaf5870CoversExact : CoversExact 8
    leaf5870Box leaf5870Certificate leaf5870InnerLog leaf5870Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi310RoundedFacts
    innerPair285RoundedFacts leaf5870RoundedFacts (by rfl)

private theorem leaf5870FlatSound : Sound leaf5870Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5870CertificateValid
    leaf5870InnerLogValid leaf5870CoversExact leaf5870LowerChecked

private noncomputable def leaf5871Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (25/64), chiHi := (101/256) }

private noncomputable def leaf5871Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871353/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356635648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1316668505/1073741824) }, upper := { exponent := 1, mantissa := (2539/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi309LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715358207/68713271296) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5871InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5871LocalValidity :
    LeafFacts leaf5871Box leaf5871Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5871Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356635648) }) = true
      norm_num [leaf5871Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5871CertificateValid :
    WideCertificateValid leaf5871Box leaf5871Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi309ValidityFacts
    leaf5871LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5871CoverageChecked :
    coverageCheck (innerAD leaf5871Box) leaf5871InnerLog = true := by
  rfl'

private theorem leaf5871InnerLogValid :
    leaf5871InnerLog.Valid 8 (innerAD leaf5871Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5871CoverageChecked

private noncomputable def leaf5871InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814795/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5871InputLogOnePlusV_eq :
    leaf5871InputLogOnePlusV = outerEnclosure 24
      (leaf5871Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5871RoundedFacts : LeafRoundedFacts 8
    leaf5871Certificate.logOnePlusV leaf5871InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5871InputLogOnePlusV_eq }

private noncomputable def leaf5871Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi309InputQChi innerPair285Input
    leaf5871InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5871LowerChecked :
    lowerCheck 24 leaf5871Box leaf5871Inputs = true := by
  rfl'

private theorem leaf5871CoversExact : CoversExact 8
    leaf5871Box leaf5871Certificate leaf5871InnerLog leaf5871Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi309RoundedFacts
    innerPair285RoundedFacts leaf5871RoundedFacts (by rfl)

private theorem leaf5871FlatSound : Sound leaf5871Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5871CertificateValid
    leaf5871InnerLogValid leaf5871CoversExact leaf5871LowerChecked

private noncomputable def leaf5872Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (101/256), chiHi := (51/128) }

private noncomputable def leaf5872Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713209856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1324466811/1073741824) }, upper := { exponent := 1, mantissa := (1277/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi310LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429606397/137426419712) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5872InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5872LocalValidity :
    LeafFacts leaf5872Box leaf5872Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5872Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713209856) }) = true
      norm_num [leaf5872Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5872CertificateValid :
    WideCertificateValid leaf5872Box leaf5872Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi310ValidityFacts
    leaf5872LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5872CoverageChecked :
    coverageCheck (innerAD leaf5872Box) leaf5872InnerLog = true := by
  rfl'

private theorem leaf5872InnerLogValid :
    leaf5872InnerLog.Valid 8 (innerAD leaf5872Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5872CoverageChecked

private noncomputable def leaf5872InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5872InputLogOnePlusV_eq :
    leaf5872InputLogOnePlusV = outerEnclosure 24
      (leaf5872Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5872RoundedFacts : LeafRoundedFacts 8
    leaf5872Certificate.logOnePlusV leaf5872InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5872InputLogOnePlusV_eq }

private noncomputable def leaf5872Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi310InputQChi innerPair285Input
    leaf5872InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5872LowerChecked :
    lowerCheck 24 leaf5872Box leaf5872Inputs = true := by
  rfl'

private theorem leaf5872CoversExact : CoversExact 8
    leaf5872Box leaf5872Certificate leaf5872InnerLog leaf5872Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi310RoundedFacts
    innerPair285RoundedFacts leaf5872RoundedFacts (by rfl)

private theorem leaf5872FlatSound : Sound leaf5872Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5872CertificateValid
    leaf5872InnerLogValid leaf5872CoversExact leaf5872LowerChecked

private noncomputable def leaf5873Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5873Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871355/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713201152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1325580855/1073741824) }, upper := { exponent := 1, mantissa := (20449/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429597693/137426402304) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5873InnerLog : WideLogData :=
  innerPair285Data

set_option maxRecDepth 1000000 in
private theorem leaf5873LocalValidity :
    LeafFacts leaf5873Box leaf5873Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5873Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713201152) }) = true
      norm_num [leaf5873Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5873CertificateValid :
    WideCertificateValid leaf5873Box leaf5873Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi311ValidityFacts
    leaf5873LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5873CoverageChecked :
    coverageCheck (innerAD leaf5873Box) leaf5873InnerLog = true := by
  rfl'

private theorem leaf5873InnerLogValid :
    leaf5873InnerLog.Valid 8 (innerAD leaf5873Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint79PositiveFacts.valid leaf5873CoverageChecked

private noncomputable def leaf5873InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5873InputLogOnePlusV_eq :
    leaf5873InputLogOnePlusV = outerEnclosure 24
      (leaf5873Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5873RoundedFacts : LeafRoundedFacts 8
    leaf5873Certificate.logOnePlusV leaf5873InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5873InputLogOnePlusV_eq }

private noncomputable def leaf5873Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi311InputQChi innerPair285Input
    leaf5873InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5873LowerChecked :
    lowerCheck 24 leaf5873Box leaf5873Inputs = true := by
  rfl'

private theorem leaf5873CoversExact : CoversExact 8
    leaf5873Box leaf5873Certificate leaf5873InnerLog leaf5873Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi311RoundedFacts
    innerPair285RoundedFacts leaf5873RoundedFacts (by rfl)

private theorem leaf5873FlatSound : Sound leaf5873Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5873CertificateValid
    leaf5873InnerLogValid leaf5873CoversExact leaf5873LowerChecked

private noncomputable def leaf5874Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5874Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713140224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1333313629/1073741824) }, upper := { exponent := 1, mantissa := (2571/2048) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429536765/137426280448) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5874InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5874LocalValidity :
    LeafFacts leaf5874Box leaf5874Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5874Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713140224) }) = true
      norm_num [leaf5874Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5874CertificateValid :
    WideCertificateValid leaf5874Box leaf5874Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi312ValidityFacts
    leaf5874LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5874CoverageChecked :
    coverageCheck (innerAD leaf5874Box) leaf5874InnerLog = true := by
  rfl'

private theorem leaf5874InnerLogValid :
    leaf5874InnerLog.Valid 8 (innerAD leaf5874Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5874CoverageChecked

private noncomputable def leaf5874InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814739/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5874InputLogOnePlusV_eq :
    leaf5874InputLogOnePlusV = outerEnclosure 24
      (leaf5874Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5874RoundedFacts : LeafRoundedFacts 8
    leaf5874Certificate.logOnePlusV leaf5874InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5874InputLogOnePlusV_eq }

private noncomputable def leaf5874Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi312InputQChi innerPair286Input
    leaf5874InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5874LowerChecked :
    lowerCheck 24 leaf5874Box leaf5874Inputs = true := by
  rfl'

private theorem leaf5874CoversExact : CoversExact 8
    leaf5874Box leaf5874Certificate leaf5874InnerLog leaf5874Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi312RoundedFacts
    innerPair286RoundedFacts leaf5874RoundedFacts (by rfl)

private theorem leaf5874FlatSound : Sound leaf5874Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5874CertificateValid
    leaf5874InnerLogValid leaf5874CoversExact leaf5874LowerChecked

private noncomputable def leaf5875Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (51/128), chiHi := (103/256) }

private noncomputable def leaf5875Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871357/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713148416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1332265117/1073741824) }, upper := { exponent := 1, mantissa := (2569/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi311LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429544957/137426296832) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5875InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5875LocalValidity :
    LeafFacts leaf5875Box leaf5875Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5875Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713148416) }) = true
      norm_num [leaf5875Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5875CertificateValid :
    WideCertificateValid leaf5875Box leaf5875Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi311ValidityFacts
    leaf5875LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5875CoverageChecked :
    coverageCheck (innerAD leaf5875Box) leaf5875InnerLog = true := by
  rfl'

private theorem leaf5875InnerLogValid :
    leaf5875InnerLog.Valid 8 (innerAD leaf5875Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5875CoverageChecked

private noncomputable def leaf5875InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5875InputLogOnePlusV_eq :
    leaf5875InputLogOnePlusV = outerEnclosure 24
      (leaf5875Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5875RoundedFacts : LeafRoundedFacts 8
    leaf5875Certificate.logOnePlusV leaf5875InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5875InputLogOnePlusV_eq }

private noncomputable def leaf5875Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi311InputQChi innerPair286Input
    leaf5875InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5875LowerChecked :
    lowerCheck 24 leaf5875Box leaf5875Inputs = true := by
  rfl'

private theorem leaf5875CoversExact : CoversExact 8
    leaf5875Box leaf5875Certificate leaf5875InnerLog leaf5875Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi311RoundedFacts
    innerPair286RoundedFacts leaf5875RoundedFacts (by rfl)

private theorem leaf5875FlatSound : Sound leaf5875Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5875CertificateValid
    leaf5875InnerLogValid leaf5875CoversExact leaf5875LowerChecked

private noncomputable def leaf5876Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (103/256), chiHi := (13/32) }

private noncomputable def leaf5876Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (536871359/536870912) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68713086976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1340063423/1073741824) }, upper := { exponent := 1, mantissa := (323/256) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi312LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429483517/137426173952) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5876InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf5876LocalValidity :
    LeafFacts leaf5876Box leaf5876Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5876Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68713086976) }) = true
      norm_num [leaf5876Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5876CertificateValid :
    WideCertificateValid leaf5876Box leaf5876Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi312ValidityFacts
    leaf5876LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5876CoverageChecked :
    coverageCheck (innerAD leaf5876Box) leaf5876InnerLog = true := by
  rfl'

private theorem leaf5876InnerLogValid :
    leaf5876InnerLog.Valid 8 (innerAD leaf5876Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf5876CoverageChecked

private noncomputable def leaf5876InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5876InputLogOnePlusV_eq :
    leaf5876InputLogOnePlusV = outerEnclosure 24
      (leaf5876Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5876RoundedFacts : LeafRoundedFacts 8
    leaf5876Certificate.logOnePlusV leaf5876InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5876InputLogOnePlusV_eq }

private noncomputable def leaf5876Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi312InputQChi innerPair286Input
    leaf5876InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5876LowerChecked :
    lowerCheck 24 leaf5876Box leaf5876Inputs = true := by
  rfl'

private theorem leaf5876CoversExact : CoversExact 8
    leaf5876Box leaf5876Certificate leaf5876InnerLog leaf5876Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi312RoundedFacts
    innerPair286RoundedFacts leaf5876RoundedFacts (by rfl)

private theorem leaf5876FlatSound : Sound leaf5876Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5876CertificateValid
    leaf5876InnerLogValid leaf5876CoversExact leaf5876LowerChecked

private noncomputable def component117Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node0_sound : Sound component117Node0Box :=
  sound_of_literal_split component117Node0Box leaf5825Box leaf5826Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5825FlatSound leaf5826FlatSound

private noncomputable def component117Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node1_sound : Sound component117Node1Box :=
  sound_of_literal_split component117Node1Box leaf5827Box leaf5828Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5827FlatSound leaf5828FlatSound

private noncomputable def component117Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node2_sound : Sound component117Node2Box :=
  sound_of_literal_split component117Node2Box component117Node0Box component117Node1Box
    .k (113/32) (by rfl) (by rfl)
    component117Node0_sound component117Node1_sound

private noncomputable def component117Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node3_sound : Sound component117Node3Box :=
  sound_of_literal_split component117Node3Box leaf5829Box leaf5830Box
    .k (113/32) (by rfl) (by rfl)
    leaf5829FlatSound leaf5830FlatSound

private noncomputable def component117Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node4_sound : Sound component117Node4Box :=
  sound_of_literal_split component117Node4Box component117Node2Box component117Node3Box
    .chi (49/128) (by rfl) (by rfl)
    component117Node2_sound component117Node3_sound

private noncomputable def component117Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node5_sound : Sound component117Node5Box :=
  sound_of_literal_split component117Node5Box leaf5831Box leaf5832Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5831FlatSound leaf5832FlatSound

private noncomputable def component117Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node6_sound : Sound component117Node6Box :=
  sound_of_literal_split component117Node6Box leaf5833Box leaf5834Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5833FlatSound leaf5834FlatSound

private noncomputable def component117Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node7_sound : Sound component117Node7Box :=
  sound_of_literal_split component117Node7Box component117Node5Box component117Node6Box
    .k (115/32) (by rfl) (by rfl)
    component117Node5_sound component117Node6_sound

private noncomputable def component117Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node8_sound : Sound component117Node8Box :=
  sound_of_literal_split component117Node8Box leaf5835Box leaf5836Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5835FlatSound leaf5836FlatSound

private noncomputable def component117Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node9_sound : Sound component117Node9Box :=
  sound_of_literal_split component117Node9Box leaf5837Box leaf5838Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5837FlatSound leaf5838FlatSound

private noncomputable def component117Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node10_sound : Sound component117Node10Box :=
  sound_of_literal_split component117Node10Box component117Node8Box component117Node9Box
    .k (115/32) (by rfl) (by rfl)
    component117Node8_sound component117Node9_sound

private noncomputable def component117Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node11_sound : Sound component117Node11Box :=
  sound_of_literal_split component117Node11Box component117Node7Box component117Node10Box
    .chi (49/128) (by rfl) (by rfl)
    component117Node7_sound component117Node10_sound

private noncomputable def component117Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node12_sound : Sound component117Node12Box :=
  sound_of_literal_split component117Node12Box component117Node4Box component117Node11Box
    .k (57/16) (by rfl) (by rfl)
    component117Node4_sound component117Node11_sound

private noncomputable def component117Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node13_sound : Sound component117Node13Box :=
  sound_of_literal_split component117Node13Box leaf5839Box leaf5840Box
    .k (113/32) (by rfl) (by rfl)
    leaf5839FlatSound leaf5840FlatSound

private noncomputable def component117Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node14_sound : Sound component117Node14Box :=
  sound_of_literal_split component117Node14Box leaf5841Box leaf5842Box
    .k (113/32) (by rfl) (by rfl)
    leaf5841FlatSound leaf5842FlatSound

private noncomputable def component117Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node15_sound : Sound component117Node15Box :=
  sound_of_literal_split component117Node15Box component117Node13Box component117Node14Box
    .chi (51/128) (by rfl) (by rfl)
    component117Node13_sound component117Node14_sound

private noncomputable def component117Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node16_sound : Sound component117Node16Box :=
  sound_of_literal_split component117Node16Box leaf5843Box leaf5844Box
    .k (115/32) (by rfl) (by rfl)
    leaf5843FlatSound leaf5844FlatSound

private noncomputable def component117Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node17_sound : Sound component117Node17Box :=
  sound_of_literal_split component117Node17Box leaf5845Box leaf5846Box
    .k (115/32) (by rfl) (by rfl)
    leaf5845FlatSound leaf5846FlatSound

private noncomputable def component117Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node18_sound : Sound component117Node18Box :=
  sound_of_literal_split component117Node18Box component117Node16Box component117Node17Box
    .chi (51/128) (by rfl) (by rfl)
    component117Node16_sound component117Node17_sound

private noncomputable def component117Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node19_sound : Sound component117Node19Box :=
  sound_of_literal_split component117Node19Box component117Node15Box component117Node18Box
    .k (57/16) (by rfl) (by rfl)
    component117Node15_sound component117Node18_sound

private noncomputable def component117Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node20_sound : Sound component117Node20Box :=
  sound_of_literal_split component117Node20Box component117Node12Box component117Node19Box
    .chi (25/64) (by rfl) (by rfl)
    component117Node12_sound component117Node19_sound

private noncomputable def component117Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node21_sound : Sound component117Node21Box :=
  sound_of_literal_split component117Node21Box leaf5847Box leaf5848Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5847FlatSound leaf5848FlatSound

private noncomputable def component117Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node22_sound : Sound component117Node22Box :=
  sound_of_literal_split component117Node22Box leaf5849Box leaf5850Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5849FlatSound leaf5850FlatSound

private noncomputable def component117Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node23_sound : Sound component117Node23Box :=
  sound_of_literal_split component117Node23Box component117Node21Box component117Node22Box
    .k (117/32) (by rfl) (by rfl)
    component117Node21_sound component117Node22_sound

private noncomputable def component117Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node24_sound : Sound component117Node24Box :=
  sound_of_literal_split component117Node24Box leaf5851Box leaf5852Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5851FlatSound leaf5852FlatSound

private noncomputable def component117Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node25_sound : Sound component117Node25Box :=
  sound_of_literal_split component117Node25Box leaf5853Box leaf5854Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5853FlatSound leaf5854FlatSound

private noncomputable def component117Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node26_sound : Sound component117Node26Box :=
  sound_of_literal_split component117Node26Box component117Node24Box component117Node25Box
    .k (117/32) (by rfl) (by rfl)
    component117Node24_sound component117Node25_sound

private noncomputable def component117Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node27_sound : Sound component117Node27Box :=
  sound_of_literal_split component117Node27Box component117Node23Box component117Node26Box
    .chi (49/128) (by rfl) (by rfl)
    component117Node23_sound component117Node26_sound

private noncomputable def component117Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node28_sound : Sound component117Node28Box :=
  sound_of_literal_split component117Node28Box leaf5855Box leaf5856Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5855FlatSound leaf5856FlatSound

private noncomputable def component117Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node29_sound : Sound component117Node29Box :=
  sound_of_literal_split component117Node29Box leaf5857Box leaf5858Box
    .chi (97/256) (by rfl) (by rfl)
    leaf5857FlatSound leaf5858FlatSound

private noncomputable def component117Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/8), chiHi := (49/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node30_sound : Sound component117Node30Box :=
  sound_of_literal_split component117Node30Box component117Node28Box component117Node29Box
    .k (119/32) (by rfl) (by rfl)
    component117Node28_sound component117Node29_sound

private noncomputable def component117Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node31_sound : Sound component117Node31Box :=
  sound_of_literal_split component117Node31Box leaf5859Box leaf5860Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5859FlatSound leaf5860FlatSound

private noncomputable def component117Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node32_sound : Sound component117Node32Box :=
  sound_of_literal_split component117Node32Box leaf5861Box leaf5862Box
    .chi (99/256) (by rfl) (by rfl)
    leaf5861FlatSound leaf5862FlatSound

private noncomputable def component117Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (49/128), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node33_sound : Sound component117Node33Box :=
  sound_of_literal_split component117Node33Box component117Node31Box component117Node32Box
    .k (119/32) (by rfl) (by rfl)
    component117Node31_sound component117Node32_sound

private noncomputable def component117Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node34_sound : Sound component117Node34Box :=
  sound_of_literal_split component117Node34Box component117Node30Box component117Node33Box
    .chi (49/128) (by rfl) (by rfl)
    component117Node30_sound component117Node33_sound

private noncomputable def component117Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component117Node35_sound : Sound component117Node35Box :=
  sound_of_literal_split component117Node35Box component117Node27Box component117Node34Box
    .k (59/16) (by rfl) (by rfl)
    component117Node27_sound component117Node34_sound

private noncomputable def component117Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node36_sound : Sound component117Node36Box :=
  sound_of_literal_split component117Node36Box leaf5863Box leaf5864Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5863FlatSound leaf5864FlatSound

private noncomputable def component117Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node37_sound : Sound component117Node37Box :=
  sound_of_literal_split component117Node37Box leaf5865Box leaf5866Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5865FlatSound leaf5866FlatSound

private noncomputable def component117Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node38_sound : Sound component117Node38Box :=
  sound_of_literal_split component117Node38Box component117Node36Box component117Node37Box
    .k (117/32) (by rfl) (by rfl)
    component117Node36_sound component117Node37_sound

private noncomputable def component117Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node39_sound : Sound component117Node39Box :=
  sound_of_literal_split component117Node39Box leaf5867Box leaf5868Box
    .k (117/32) (by rfl) (by rfl)
    leaf5867FlatSound leaf5868FlatSound

private noncomputable def component117Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node40_sound : Sound component117Node40Box :=
  sound_of_literal_split component117Node40Box component117Node38Box component117Node39Box
    .chi (51/128) (by rfl) (by rfl)
    component117Node38_sound component117Node39_sound

private noncomputable def component117Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node41_sound : Sound component117Node41Box :=
  sound_of_literal_split component117Node41Box leaf5869Box leaf5870Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5869FlatSound leaf5870FlatSound

private noncomputable def component117Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node42_sound : Sound component117Node42Box :=
  sound_of_literal_split component117Node42Box leaf5871Box leaf5872Box
    .chi (101/256) (by rfl) (by rfl)
    leaf5871FlatSound leaf5872FlatSound

private noncomputable def component117Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (25/64), chiHi := (51/128) }

set_option maxRecDepth 1000000 in
private theorem component117Node43_sound : Sound component117Node43Box :=
  sound_of_literal_split component117Node43Box component117Node41Box component117Node42Box
    .k (119/32) (by rfl) (by rfl)
    component117Node41_sound component117Node42_sound

private noncomputable def component117Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node44_sound : Sound component117Node44Box :=
  sound_of_literal_split component117Node44Box leaf5873Box leaf5874Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5873FlatSound leaf5874FlatSound

private noncomputable def component117Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node45_sound : Sound component117Node45Box :=
  sound_of_literal_split component117Node45Box leaf5875Box leaf5876Box
    .chi (103/256) (by rfl) (by rfl)
    leaf5875FlatSound leaf5876FlatSound

private noncomputable def component117Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (51/128), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node46_sound : Sound component117Node46Box :=
  sound_of_literal_split component117Node46Box component117Node44Box component117Node45Box
    .k (119/32) (by rfl) (by rfl)
    component117Node44_sound component117Node45_sound

private noncomputable def component117Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node47_sound : Sound component117Node47Box :=
  sound_of_literal_split component117Node47Box component117Node43Box component117Node46Box
    .chi (51/128) (by rfl) (by rfl)
    component117Node43_sound component117Node46_sound

private noncomputable def component117Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node48_sound : Sound component117Node48Box :=
  sound_of_literal_split component117Node48Box component117Node40Box component117Node47Box
    .k (59/16) (by rfl) (by rfl)
    component117Node40_sound component117Node47_sound

private noncomputable def component117Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component117Node49_sound : Sound component117Node49Box :=
  sound_of_literal_split component117Node49Box component117Node35Box component117Node48Box
    .chi (25/64) (by rfl) (by rfl)
    component117Node35_sound component117Node48_sound

noncomputable def component117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
theorem component117_sound : Sound component117Box :=
  sound_of_literal_split component117Box component117Node20Box component117Node49Box
    .k (29/8) (by rfl) (by rfl)
    component117Node20_sound component117Node49_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
