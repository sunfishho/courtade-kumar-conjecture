import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
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

private noncomputable def leaf6023Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6023Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712881152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (679419055/536870912) }, upper := { exponent := 1, mantissa := (10537/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429277693/137425762304) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6023InnerLog : WideLogData :=
  innerPair671Data

set_option maxRecDepth 1000000 in
private theorem leaf6023LocalValidity :
    LeafFacts leaf6023Box leaf6023Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6023Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712881152) }) = true
      norm_num [leaf6023Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6023CertificateValid :
    WideCertificateValid leaf6023Box leaf6023Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi267ValidityFacts
    leaf6023LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6023CoverageChecked :
    coverageCheck (innerAD leaf6023Box) leaf6023InnerLog = true := by
  rfl'

private theorem leaf6023InnerLogValid :
    leaf6023InnerLog.Valid 8 (innerAD leaf6023Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint435PositiveFacts.valid leaf6023CoverageChecked

private noncomputable def leaf6023InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814755/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6023InputLogOnePlusV_eq :
    leaf6023InputLogOnePlusV = outerEnclosure 24
      (leaf6023Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6023RoundedFacts : LeafRoundedFacts 8
    leaf6023Certificate.logOnePlusV leaf6023InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6023InputLogOnePlusV_eq }

private noncomputable def leaf6023Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi267InputQChi innerPair671Input
    leaf6023InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6023LowerChecked :
    lowerCheck 24 leaf6023Box leaf6023Inputs = true := by
  rfl'

private theorem leaf6023CoversExact : CoversExact 8
    leaf6023Box leaf6023Certificate leaf6023InnerLog leaf6023Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi267RoundedFacts
    innerPair671RoundedFacts leaf6023RoundedFacts (by rfl)

private theorem leaf6023FlatSound : Sound leaf6023Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6023CertificateValid
    leaf6023InnerLogValid leaf6023CoversExact leaf6023LowerChecked

private noncomputable def leaf6024Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6024Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041930752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (683088845/536870912) }, upper := { exponent := 1, mantissa := (5297/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084071725/8083861504) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6024InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6024LocalValidity :
    LeafFacts leaf6024Box leaf6024Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6024Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041930752) }) = true
      norm_num [leaf6024Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6024CertificateValid :
    WideCertificateValid leaf6024Box leaf6024Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi267ValidityFacts
    leaf6024LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6024CoverageChecked :
    coverageCheck (innerAD leaf6024Box) leaf6024InnerLog = true := by
  rfl'

private theorem leaf6024InnerLogValid :
    leaf6024InnerLog.Valid 8 (innerAD leaf6024Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6024CoverageChecked

private noncomputable def leaf6024InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6024InputLogOnePlusV_eq :
    leaf6024InputLogOnePlusV = outerEnclosure 24
      (leaf6024Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6024RoundedFacts : LeafRoundedFacts 8
    leaf6024Certificate.logOnePlusV leaf6024InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6024InputLogOnePlusV_eq }

private noncomputable def leaf6024Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi267InputQChi innerPair294Input
    leaf6024InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6024LowerChecked :
    lowerCheck 24 leaf6024Box leaf6024Inputs = true := by
  rfl'

private theorem leaf6024CoversExact : CoversExact 8
    leaf6024Box leaf6024Certificate leaf6024InnerLog leaf6024Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi267RoundedFacts
    innerPair294RoundedFacts leaf6024RoundedFacts (by rfl)

private theorem leaf6024FlatSound : Sound leaf6024Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6024CertificateValid
    leaf6024InnerLogValid leaf6024CoversExact leaf6024LowerChecked

private noncomputable def leaf6025Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6025Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712765440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (686758637/536870912) }, upper := { exponent := 1, mantissa := (5325/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429161981/137425530880) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6025InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6025LocalValidity :
    LeafFacts leaf6025Box leaf6025Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6025Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712765440) }) = true
      norm_num [leaf6025Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6025CertificateValid :
    WideCertificateValid leaf6025Box leaf6025Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi268ValidityFacts
    leaf6025LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6025CoverageChecked :
    coverageCheck (innerAD leaf6025Box) leaf6025InnerLog = true := by
  rfl'

private theorem leaf6025InnerLogValid :
    leaf6025InnerLog.Valid 8 (innerAD leaf6025Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6025CoverageChecked

private noncomputable def leaf6025InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6025InputLogOnePlusV_eq :
    leaf6025InputLogOnePlusV = outerEnclosure 24
      (leaf6025Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6025RoundedFacts : LeafRoundedFacts 8
    leaf6025Certificate.logOnePlusV leaf6025InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6025InputLogOnePlusV_eq }

private noncomputable def leaf6025Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi268InputQChi innerPair294Input
    leaf6025InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6025LowerChecked :
    lowerCheck 24 leaf6025Box leaf6025Inputs = true := by
  rfl'

private theorem leaf6025CoversExact : CoversExact 8
    leaf6025Box leaf6025Certificate leaf6025InnerLog leaf6025Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi268RoundedFacts
    innerPair294RoundedFacts leaf6025RoundedFacts (by rfl)

private theorem leaf6025FlatSound : Sound leaf6025Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6025CertificateValid
    leaf6025InnerLogValid leaf6025CoversExact leaf6025LowerChecked

private noncomputable def leaf6026Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6026Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712706048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (690493959/536870912) }, upper := { exponent := 1, mantissa := (2677/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429102589/137425412096) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6026InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf6026LocalValidity :
    LeafFacts leaf6026Box leaf6026Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6026Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712706048) }) = true
      norm_num [leaf6026Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6026CertificateValid :
    WideCertificateValid leaf6026Box leaf6026Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi268ValidityFacts
    leaf6026LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6026CoverageChecked :
    coverageCheck (innerAD leaf6026Box) leaf6026InnerLog = true := by
  rfl'

private theorem leaf6026InnerLogValid :
    leaf6026InnerLog.Valid 8 (innerAD leaf6026Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf6026CoverageChecked

private noncomputable def leaf6026InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6026InputLogOnePlusV_eq :
    leaf6026InputLogOnePlusV = outerEnclosure 24
      (leaf6026Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6026RoundedFacts : LeafRoundedFacts 8
    leaf6026Certificate.logOnePlusV leaf6026InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6026InputLogOnePlusV_eq }

private noncomputable def leaf6026Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi268InputQChi innerPair339Input
    leaf6026InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6026LowerChecked :
    lowerCheck 24 leaf6026Box leaf6026Inputs = true := by
  rfl'

private theorem leaf6026CoversExact : CoversExact 8
    leaf6026Box leaf6026Certificate leaf6026InnerLog leaf6026Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi268RoundedFacts
    innerPair339RoundedFacts leaf6026RoundedFacts (by rfl)

private theorem leaf6026FlatSound : Sound leaf6026Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6026CertificateValid
    leaf6026InnerLogValid leaf6026CoversExact leaf6026LowerChecked

private noncomputable def leaf6027Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6027Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712764416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (686758635/536870912) }, upper := { exponent := 1, mantissa := (10651/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429160957/137425528832) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6027InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6027LocalValidity :
    LeafFacts leaf6027Box leaf6027Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6027Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712764416) }) = true
      norm_num [leaf6027Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6027CertificateValid :
    WideCertificateValid leaf6027Box leaf6027Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi267ValidityFacts
    leaf6027LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6027CoverageChecked :
    coverageCheck (innerAD leaf6027Box) leaf6027InnerLog = true := by
  rfl'

private theorem leaf6027InnerLogValid :
    leaf6027InnerLog.Valid 8 (innerAD leaf6027Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6027CoverageChecked

private noncomputable def leaf6027InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907381/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6027InputLogOnePlusV_eq :
    leaf6027InputLogOnePlusV = outerEnclosure 24
      (leaf6027Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6027RoundedFacts : LeafRoundedFacts 8
    leaf6027Certificate.logOnePlusV leaf6027InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6027InputLogOnePlusV_eq }

private noncomputable def leaf6027Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi267InputQChi innerPair294Input
    leaf6027InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6027LowerChecked :
    lowerCheck 24 leaf6027Box leaf6027Inputs = true := by
  rfl'

private theorem leaf6027CoversExact : CoversExact 8
    leaf6027Box leaf6027Certificate leaf6027InnerLog leaf6027Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi267RoundedFacts
    innerPair294RoundedFacts leaf6027RoundedFacts (by rfl)

private theorem leaf6027FlatSound : Sound leaf6027Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6027CertificateValid
    leaf6027InnerLogValid leaf6027CoversExact leaf6027LowerChecked

private noncomputable def leaf6028Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6028Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712706048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (690428425/536870912) }, upper := { exponent := 1, mantissa := (2677/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429102589/137425412096) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6028InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf6028LocalValidity :
    LeafFacts leaf6028Box leaf6028Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6028Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712706048) }) = true
      norm_num [leaf6028Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6028CertificateValid :
    WideCertificateValid leaf6028Box leaf6028Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi267ValidityFacts
    leaf6028LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6028CoverageChecked :
    coverageCheck (innerAD leaf6028Box) leaf6028InnerLog = true := by
  rfl'

private theorem leaf6028InnerLogValid :
    leaf6028InnerLog.Valid 8 (innerAD leaf6028Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf6028CoverageChecked

private noncomputable def leaf6028InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629531/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6028InputLogOnePlusV_eq :
    leaf6028InputLogOnePlusV = outerEnclosure 24
      (leaf6028Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6028RoundedFacts : LeafRoundedFacts 8
    leaf6028Certificate.logOnePlusV leaf6028InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6028InputLogOnePlusV_eq }

private noncomputable def leaf6028Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi267InputQChi innerPair339Input
    leaf6028InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6028LowerChecked :
    lowerCheck 24 leaf6028Box leaf6028Inputs = true := by
  rfl'

private theorem leaf6028CoversExact : CoversExact 8
    leaf6028Box leaf6028Certificate leaf6028InnerLog leaf6028Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi267RoundedFacts
    innerPair339RoundedFacts leaf6028RoundedFacts (by rfl)

private theorem leaf6028FlatSound : Sound leaf6028Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6028CertificateValid
    leaf6028InnerLogValid leaf6028CoversExact leaf6028LowerChecked

private noncomputable def leaf6029Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6029Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712646656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (694229281/536870912) }, upper := { exponent := 1, mantissa := (5383/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429043197/137425293312) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6029InnerLog : WideLogData :=
  innerPair684Data

set_option maxRecDepth 1000000 in
private theorem leaf6029LocalValidity :
    LeafFacts leaf6029Box leaf6029Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6029Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712646656) }) = true
      norm_num [leaf6029Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6029CertificateValid :
    WideCertificateValid leaf6029Box leaf6029Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi268ValidityFacts
    leaf6029LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6029CoverageChecked :
    coverageCheck (innerAD leaf6029Box) leaf6029InnerLog = true := by
  rfl'

private theorem leaf6029InnerLogValid :
    leaf6029InnerLog.Valid 8 (innerAD leaf6029Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint95PositiveFacts.valid leaf6029CoverageChecked

private noncomputable def leaf6029InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629539/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6029InputLogOnePlusV_eq :
    leaf6029InputLogOnePlusV = outerEnclosure 24
      (leaf6029Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6029RoundedFacts : LeafRoundedFacts 8
    leaf6029Certificate.logOnePlusV leaf6029InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6029InputLogOnePlusV_eq }

private noncomputable def leaf6029Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi268InputQChi innerPair684Input
    leaf6029InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6029LowerChecked :
    lowerCheck 24 leaf6029Box leaf6029Inputs = true := by
  rfl'

private theorem leaf6029CoversExact : CoversExact 8
    leaf6029Box leaf6029Certificate leaf6029InnerLog leaf6029Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi268RoundedFacts
    innerPair684RoundedFacts leaf6029RoundedFacts (by rfl)

private theorem leaf6029FlatSound : Sound leaf6029Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6029CertificateValid
    leaf6029InnerLogValid leaf6029CoversExact leaf6029LowerChecked

private noncomputable def leaf6030Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6030Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712587264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (697964603/536870912) }, upper := { exponent := 1, mantissa := (1353/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428983805/137425174528) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6030InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6030LocalValidity :
    LeafFacts leaf6030Box leaf6030Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6030Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712587264) }) = true
      norm_num [leaf6030Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6030CertificateValid :
    WideCertificateValid leaf6030Box leaf6030Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi268ValidityFacts
    leaf6030LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6030CoverageChecked :
    coverageCheck (innerAD leaf6030Box) leaf6030InnerLog = true := by
  rfl'

private theorem leaf6030InnerLogValid :
    leaf6030InnerLog.Valid 8 (innerAD leaf6030Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6030CoverageChecked

private noncomputable def leaf6030InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6030InputLogOnePlusV_eq :
    leaf6030InputLogOnePlusV = outerEnclosure 24
      (leaf6030Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6030RoundedFacts : LeafRoundedFacts 8
    leaf6030Certificate.logOnePlusV leaf6030InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6030InputLogOnePlusV_eq }

private noncomputable def leaf6030Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi268InputQChi innerPair340Input
    leaf6030InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6030LowerChecked :
    lowerCheck 24 leaf6030Box leaf6030Inputs = true := by
  rfl'

private theorem leaf6030CoversExact : CoversExact 8
    leaf6030Box leaf6030Certificate leaf6030InnerLog leaf6030Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi268RoundedFacts
    innerPair340RoundedFacts leaf6030RoundedFacts (by rfl)

private theorem leaf6030FlatSound : Sound leaf6030Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6030CertificateValid
    leaf6030InnerLogValid leaf6030CoversExact leaf6030LowerChecked

private noncomputable def leaf6031Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6031Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435799/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712649728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (694098219/536870912) }, upper := { exponent := 1, mantissa := (10763/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429046269/137425299456) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6031InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6031LocalValidity :
    LeafFacts leaf6031Box leaf6031Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6031Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712649728) }) = true
      norm_num [leaf6031Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6031CertificateValid :
    WideCertificateValid leaf6031Box leaf6031Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi269ValidityFacts
    leaf6031LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6031CoverageChecked :
    coverageCheck (innerAD leaf6031Box) leaf6031InnerLog = true := by
  rfl'

private theorem leaf6031InnerLogValid :
    leaf6031InnerLog.Valid 8 (innerAD leaf6031Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6031CoverageChecked

private noncomputable def leaf6031InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6031InputLogOnePlusV_eq :
    leaf6031InputLogOnePlusV = outerEnclosure 24
      (leaf6031Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6031RoundedFacts : LeafRoundedFacts 8
    leaf6031Certificate.logOnePlusV leaf6031InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6031InputLogOnePlusV_eq }

private noncomputable def leaf6031Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi269InputQChi innerPair340Input
    leaf6031InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6031LowerChecked :
    lowerCheck 24 leaf6031Box leaf6031Inputs = true := by
  rfl'

private theorem leaf6031CoversExact : CoversExact 8
    leaf6031Box leaf6031Certificate leaf6031InnerLog leaf6031Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi269RoundedFacts
    innerPair340RoundedFacts leaf6031RoundedFacts (by rfl)

private theorem leaf6031FlatSound : Sound leaf6031Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6031CertificateValid
    leaf6031InnerLogValid leaf6031CoversExact leaf6031LowerChecked

private noncomputable def leaf6032Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6032Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712589312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (697899073/536870912) }, upper := { exponent := 1, mantissa := (5411/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428985853/137425178624) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6032InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6032LocalValidity :
    LeafFacts leaf6032Box leaf6032Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6032Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712589312) }) = true
      norm_num [leaf6032Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6032CertificateValid :
    WideCertificateValid leaf6032Box leaf6032Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi269ValidityFacts
    leaf6032LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6032CoverageChecked :
    coverageCheck (innerAD leaf6032Box) leaf6032InnerLog = true := by
  rfl'

private theorem leaf6032InnerLogValid :
    leaf6032InnerLog.Valid 8 (innerAD leaf6032Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6032CoverageChecked

private noncomputable def leaf6032InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6032InputLogOnePlusV_eq :
    leaf6032InputLogOnePlusV = outerEnclosure 24
      (leaf6032Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6032RoundedFacts : LeafRoundedFacts 8
    leaf6032Certificate.logOnePlusV leaf6032InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6032InputLogOnePlusV_eq }

private noncomputable def leaf6032Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi269InputQChi innerPair340Input
    leaf6032InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6032LowerChecked :
    lowerCheck 24 leaf6032Box leaf6032Inputs = true := by
  rfl'

private theorem leaf6032CoversExact : CoversExact 8
    leaf6032Box leaf6032Certificate leaf6032InnerLog leaf6032Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi269RoundedFacts
    innerPair340RoundedFacts leaf6032RoundedFacts (by rfl)

private theorem leaf6032FlatSound : Sound leaf6032Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6032CertificateValid
    leaf6032InnerLogValid leaf6032CoversExact leaf6032LowerChecked

private noncomputable def leaf6033Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6033Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435801/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712534016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (701437801/536870912) }, upper := { exponent := 1, mantissa := (2719/2048) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428930557/137425068032) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6033InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6033LocalValidity :
    LeafFacts leaf6033Box leaf6033Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6033Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712534016) }) = true
      norm_num [leaf6033Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6033CertificateValid :
    WideCertificateValid leaf6033Box leaf6033Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi270ValidityFacts
    leaf6033LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6033CoverageChecked :
    coverageCheck (innerAD leaf6033Box) leaf6033InnerLog = true := by
  rfl'

private theorem leaf6033InnerLogValid :
    leaf6033InnerLog.Valid 8 (innerAD leaf6033Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6033CoverageChecked

private noncomputable def leaf6033InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726847/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6033InputLogOnePlusV_eq :
    leaf6033InputLogOnePlusV = outerEnclosure 24
      (leaf6033Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6033RoundedFacts : LeafRoundedFacts 8
    leaf6033Certificate.logOnePlusV leaf6033InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6033InputLogOnePlusV_eq }

private noncomputable def leaf6033Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi270InputQChi innerPair340Input
    leaf6033InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6033LowerChecked :
    lowerCheck 24 leaf6033Box leaf6033Inputs = true := by
  rfl'

private theorem leaf6033CoversExact : CoversExact 8
    leaf6033Box leaf6033Certificate leaf6033InnerLog leaf6033Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi270RoundedFacts
    innerPair340RoundedFacts leaf6033RoundedFacts (by rfl)

private theorem leaf6033FlatSound : Sound leaf6033Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6033CertificateValid
    leaf6033InnerLogValid leaf6033CoversExact leaf6033LowerChecked

private noncomputable def leaf6034Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6034Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712472576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (705304187/536870912) }, upper := { exponent := 1, mantissa := (1367/1024) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428869117/137424945152) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6034InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6034LocalValidity :
    LeafFacts leaf6034Box leaf6034Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6034Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712472576) }) = true
      norm_num [leaf6034Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6034CertificateValid :
    WideCertificateValid leaf6034Box leaf6034Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi270ValidityFacts
    leaf6034LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6034CoverageChecked :
    coverageCheck (innerAD leaf6034Box) leaf6034InnerLog = true := by
  rfl'

private theorem leaf6034InnerLogValid :
    leaf6034InnerLog.Valid 8 (innerAD leaf6034Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6034CoverageChecked

private noncomputable def leaf6034InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6034InputLogOnePlusV_eq :
    leaf6034InputLogOnePlusV = outerEnclosure 24
      (leaf6034Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6034RoundedFacts : LeafRoundedFacts 8
    leaf6034Certificate.logOnePlusV leaf6034InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6034InputLogOnePlusV_eq }

private noncomputable def leaf6034Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi270InputQChi innerPair345Input
    leaf6034InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6034LowerChecked :
    lowerCheck 24 leaf6034Box leaf6034Inputs = true := by
  rfl'

private theorem leaf6034CoversExact : CoversExact 8
    leaf6034Box leaf6034Certificate leaf6034InnerLog leaf6034Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi270RoundedFacts
    innerPair345RoundedFacts leaf6034RoundedFacts (by rfl)

private theorem leaf6034FlatSound : Sound leaf6034Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6034CertificateValid
    leaf6034InnerLogValid leaf6034CoversExact leaf6034LowerChecked

private noncomputable def leaf6035Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6035Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712528896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (701699927/536870912) }, upper := { exponent := 1, mantissa := (10881/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428925437/137425057792) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6035InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6035LocalValidity :
    LeafFacts leaf6035Box leaf6035Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6035Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712528896) }) = true
      norm_num [leaf6035Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6035CertificateValid :
    WideCertificateValid leaf6035Box leaf6035Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi269ValidityFacts
    leaf6035LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6035CoverageChecked :
    coverageCheck (innerAD leaf6035Box) leaf6035InnerLog = true := by
  rfl'

private theorem leaf6035InnerLogValid :
    leaf6035InnerLog.Valid 8 (innerAD leaf6035Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6035CoverageChecked

private noncomputable def leaf6035InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6035InputLogOnePlusV_eq :
    leaf6035InputLogOnePlusV = outerEnclosure 24
      (leaf6035Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6035RoundedFacts : LeafRoundedFacts 8
    leaf6035Certificate.logOnePlusV leaf6035InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6035InputLogOnePlusV_eq }

private noncomputable def leaf6035Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi269InputQChi innerPair340Input
    leaf6035InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6035LowerChecked :
    lowerCheck 24 leaf6035Box leaf6035Inputs = true := by
  rfl'

private theorem leaf6035CoversExact : CoversExact 8
    leaf6035Box leaf6035Certificate leaf6035InnerLog leaf6035Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi269RoundedFacts
    innerPair340RoundedFacts leaf6035RoundedFacts (by rfl)

private theorem leaf6035FlatSound : Sound leaf6035Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6035CertificateValid
    leaf6035InnerLogValid leaf6035CoversExact leaf6035LowerChecked

private noncomputable def leaf6036Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6036Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712468480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (705500781/536870912) }, upper := { exponent := 1, mantissa := (2735/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428865021/137424936960) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6036InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6036LocalValidity :
    LeafFacts leaf6036Box leaf6036Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6036Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712468480) }) = true
      norm_num [leaf6036Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6036CertificateValid :
    WideCertificateValid leaf6036Box leaf6036Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi269ValidityFacts
    leaf6036LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6036CoverageChecked :
    coverageCheck (innerAD leaf6036Box) leaf6036InnerLog = true := by
  rfl'

private theorem leaf6036InnerLogValid :
    leaf6036InnerLog.Valid 8 (innerAD leaf6036Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6036CoverageChecked

private noncomputable def leaf6036InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6036InputLogOnePlusV_eq :
    leaf6036InputLogOnePlusV = outerEnclosure 24
      (leaf6036Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6036RoundedFacts : LeafRoundedFacts 8
    leaf6036Certificate.logOnePlusV leaf6036InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6036InputLogOnePlusV_eq }

private noncomputable def leaf6036Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi269InputQChi innerPair345Input
    leaf6036InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6036LowerChecked :
    lowerCheck 24 leaf6036Box leaf6036Inputs = true := by
  rfl'

private theorem leaf6036CoversExact : CoversExact 8
    leaf6036Box leaf6036Certificate leaf6036InnerLog leaf6036Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi269RoundedFacts
    innerPair345RoundedFacts leaf6036RoundedFacts (by rfl)

private theorem leaf6036FlatSound : Sound leaf6036Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6036CertificateValid
    leaf6036InnerLogValid leaf6036CoversExact leaf6036LowerChecked

private noncomputable def leaf6037Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6037Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712411136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (709170573/536870912) }, upper := { exponent := 1, mantissa := (2749/2048) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428807677/137424822272) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6037InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6037LocalValidity :
    LeafFacts leaf6037Box leaf6037Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6037Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712411136) }) = true
      norm_num [leaf6037Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6037CertificateValid :
    WideCertificateValid leaf6037Box leaf6037Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi270ValidityFacts
    leaf6037LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6037CoverageChecked :
    coverageCheck (innerAD leaf6037Box) leaf6037InnerLog = true := by
  rfl'

private theorem leaf6037InnerLogValid :
    leaf6037InnerLog.Valid 8 (innerAD leaf6037Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6037CoverageChecked

private noncomputable def leaf6037InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6037InputLogOnePlusV_eq :
    leaf6037InputLogOnePlusV = outerEnclosure 24
      (leaf6037Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6037RoundedFacts : LeafRoundedFacts 8
    leaf6037Certificate.logOnePlusV leaf6037InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6037InputLogOnePlusV_eq }

private noncomputable def leaf6037Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi270InputQChi innerPair345Input
    leaf6037InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6037LowerChecked :
    lowerCheck 24 leaf6037Box leaf6037Inputs = true := by
  rfl'

private theorem leaf6037CoversExact : CoversExact 8
    leaf6037Box leaf6037Certificate leaf6037InnerLog leaf6037Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi270RoundedFacts
    innerPair345RoundedFacts leaf6037RoundedFacts (by rfl)

private theorem leaf6037FlatSound : Sound leaf6037Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6037CertificateValid
    leaf6037InnerLogValid leaf6037CoversExact leaf6037LowerChecked

private noncomputable def leaf6038Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6038Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712349696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (713036959/536870912) }, upper := { exponent := 1, mantissa := (691/512) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428746237/137424699392) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6038InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6038LocalValidity :
    LeafFacts leaf6038Box leaf6038Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6038Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712349696) }) = true
      norm_num [leaf6038Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6038CertificateValid :
    WideCertificateValid leaf6038Box leaf6038Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi270ValidityFacts
    leaf6038LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6038CoverageChecked :
    coverageCheck (innerAD leaf6038Box) leaf6038InnerLog = true := by
  rfl'

private theorem leaf6038InnerLogValid :
    leaf6038InnerLog.Valid 8 (innerAD leaf6038Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6038CoverageChecked

private noncomputable def leaf6038InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6038InputLogOnePlusV_eq :
    leaf6038InputLogOnePlusV = outerEnclosure 24
      (leaf6038Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6038RoundedFacts : LeafRoundedFacts 8
    leaf6038Certificate.logOnePlusV leaf6038InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6038InputLogOnePlusV_eq }

private noncomputable def leaf6038Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi270InputQChi innerPair346Input
    leaf6038InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6038LowerChecked :
    lowerCheck 24 leaf6038Box leaf6038Inputs = true := by
  rfl'

private theorem leaf6038CoversExact : CoversExact 8
    leaf6038Box leaf6038Certificate leaf6038InnerLog leaf6038Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi270RoundedFacts
    innerPair346RoundedFacts leaf6038RoundedFacts (by rfl)

private theorem leaf6038FlatSound : Sound leaf6038Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6038CertificateValid
    leaf6038InnerLogValid leaf6038CoversExact leaf6038LowerChecked

private noncomputable def leaf6039Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6039Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712647680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (694098215/536870912) }, upper := { exponent := 1, mantissa := (10765/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137429044221/137425295360) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6039InnerLog : WideLogData :=
  innerPair684Data

set_option maxRecDepth 1000000 in
private theorem leaf6039LocalValidity :
    LeafFacts leaf6039Box leaf6039Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6039Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712647680) }) = true
      norm_num [leaf6039Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6039CertificateValid :
    WideCertificateValid leaf6039Box leaf6039Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi267ValidityFacts
    leaf6039LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6039CoverageChecked :
    coverageCheck (innerAD leaf6039Box) leaf6039InnerLog = true := by
  rfl'

private theorem leaf6039InnerLogValid :
    leaf6039InnerLog.Valid 8 (innerAD leaf6039Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint95PositiveFacts.valid leaf6039CoverageChecked

private noncomputable def leaf6039InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6039InputLogOnePlusV_eq :
    leaf6039InputLogOnePlusV = outerEnclosure 24
      (leaf6039Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6039RoundedFacts : LeafRoundedFacts 8
    leaf6039Certificate.logOnePlusV leaf6039InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6039InputLogOnePlusV_eq }

private noncomputable def leaf6039Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi267InputQChi innerPair684Input
    leaf6039InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6039LowerChecked :
    lowerCheck 24 leaf6039Box leaf6039Inputs = true := by
  rfl'

private theorem leaf6039CoversExact : CoversExact 8
    leaf6039Box leaf6039Certificate leaf6039InnerLog leaf6039Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi267RoundedFacts
    innerPair684RoundedFacts leaf6039RoundedFacts (by rfl)

private theorem leaf6039FlatSound : Sound leaf6039Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6039CertificateValid
    leaf6039InnerLogValid leaf6039CoversExact leaf6039LowerChecked

private noncomputable def leaf6040Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6040Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712589312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (697768005/536870912) }, upper := { exponent := 1, mantissa := (5411/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428985853/137425178624) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6040InnerLog : WideLogData :=
  innerPair689Data

set_option maxRecDepth 1000000 in
private theorem leaf6040LocalValidity :
    LeafFacts leaf6040Box leaf6040Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6040Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712589312) }) = true
      norm_num [leaf6040Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6040CertificateValid :
    WideCertificateValid leaf6040Box leaf6040Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi267ValidityFacts
    leaf6040LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6040CoverageChecked :
    coverageCheck (innerAD leaf6040Box) leaf6040InnerLog = true := by
  rfl'

private theorem leaf6040InnerLogValid :
    leaf6040InnerLog.Valid 8 (innerAD leaf6040Box) :=
  wideLogDataValid_of_cachedCheck endpoint436PositiveFacts
    endpoint447PositiveFacts.valid leaf6040CoverageChecked

private noncomputable def leaf6040InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6040InputLogOnePlusV_eq :
    leaf6040InputLogOnePlusV = outerEnclosure 24
      (leaf6040Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6040RoundedFacts : LeafRoundedFacts 8
    leaf6040Certificate.logOnePlusV leaf6040InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6040InputLogOnePlusV_eq }

private noncomputable def leaf6040Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi267InputQChi innerPair689Input
    leaf6040InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6040LowerChecked :
    lowerCheck 24 leaf6040Box leaf6040Inputs = true := by
  rfl'

private theorem leaf6040CoversExact : CoversExact 8
    leaf6040Box leaf6040Certificate leaf6040InnerLog leaf6040Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi267RoundedFacts
    innerPair689RoundedFacts leaf6040RoundedFacts (by rfl)

private theorem leaf6040FlatSound : Sound leaf6040Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6040CertificateValid
    leaf6040InnerLogValid leaf6040CoversExact leaf6040LowerChecked

private noncomputable def leaf6041Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6041Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712527872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (701699925/536870912) }, upper := { exponent := 1, mantissa := (5441/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428924413/137425055744) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6041InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6041LocalValidity :
    LeafFacts leaf6041Box leaf6041Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6041Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712527872) }) = true
      norm_num [leaf6041Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6041CertificateValid :
    WideCertificateValid leaf6041Box leaf6041Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi268ValidityFacts
    leaf6041LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6041CoverageChecked :
    coverageCheck (innerAD leaf6041Box) leaf6041InnerLog = true := by
  rfl'

private theorem leaf6041InnerLogValid :
    leaf6041InnerLog.Valid 8 (innerAD leaf6041Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6041CoverageChecked

private noncomputable def leaf6041InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6041InputLogOnePlusV_eq :
    leaf6041InputLogOnePlusV = outerEnclosure 24
      (leaf6041Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6041RoundedFacts : LeafRoundedFacts 8
    leaf6041Certificate.logOnePlusV leaf6041InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6041InputLogOnePlusV_eq }

private noncomputable def leaf6041Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi268InputQChi innerPair340Input
    leaf6041InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6041LowerChecked :
    lowerCheck 24 leaf6041Box leaf6041Inputs = true := by
  rfl'

private theorem leaf6041CoversExact : CoversExact 8
    leaf6041Box leaf6041Certificate leaf6041InnerLog leaf6041Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi268RoundedFacts
    innerPair340RoundedFacts leaf6041RoundedFacts (by rfl)

private theorem leaf6041FlatSound : Sound leaf6041Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6041CertificateValid
    leaf6041InnerLogValid leaf6041CoversExact leaf6041LowerChecked

private noncomputable def leaf6042Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6042Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712468480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (705435247/536870912) }, upper := { exponent := 1, mantissa := (2735/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428865021/137424936960) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6042InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6042LocalValidity :
    LeafFacts leaf6042Box leaf6042Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6042Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712468480) }) = true
      norm_num [leaf6042Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6042CertificateValid :
    WideCertificateValid leaf6042Box leaf6042Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi268ValidityFacts
    leaf6042LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6042CoverageChecked :
    coverageCheck (innerAD leaf6042Box) leaf6042InnerLog = true := by
  rfl'

private theorem leaf6042InnerLogValid :
    leaf6042InnerLog.Valid 8 (innerAD leaf6042Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6042CoverageChecked

private noncomputable def leaf6042InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6042InputLogOnePlusV_eq :
    leaf6042InputLogOnePlusV = outerEnclosure 24
      (leaf6042Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6042RoundedFacts : LeafRoundedFacts 8
    leaf6042Certificate.logOnePlusV leaf6042InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6042InputLogOnePlusV_eq }

private noncomputable def leaf6042Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi268InputQChi innerPair345Input
    leaf6042InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6042LowerChecked :
    lowerCheck 24 leaf6042Box leaf6042Inputs = true := by
  rfl'

private theorem leaf6042CoversExact : CoversExact 8
    leaf6042Box leaf6042Certificate leaf6042InnerLog leaf6042Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi268RoundedFacts
    innerPair345RoundedFacts leaf6042RoundedFacts (by rfl)

private theorem leaf6042FlatSound : Sound leaf6042Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6042CertificateValid
    leaf6042InnerLogValid leaf6042CoversExact leaf6042LowerChecked

private noncomputable def leaf6043Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6043Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712530944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (701437795/536870912) }, upper := { exponent := 1, mantissa := (10879/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428927485/137425061888) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6043InnerLog : WideLogData :=
  innerPair699Data

set_option maxRecDepth 1000000 in
private theorem leaf6043LocalValidity :
    LeafFacts leaf6043Box leaf6043Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6043Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712530944) }) = true
      norm_num [leaf6043Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6043CertificateValid :
    WideCertificateValid leaf6043Box leaf6043Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi267ValidityFacts
    leaf6043LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6043CoverageChecked :
    coverageCheck (innerAD leaf6043Box) leaf6043InnerLog = true := by
  rfl'

private theorem leaf6043InnerLogValid :
    leaf6043InnerLog.Valid 8 (innerAD leaf6043Box) :=
  wideLogDataValid_of_cachedCheck endpoint444PositiveFacts
    endpoint447PositiveFacts.valid leaf6043CoverageChecked

private noncomputable def leaf6043InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6043InputLogOnePlusV_eq :
    leaf6043InputLogOnePlusV = outerEnclosure 24
      (leaf6043Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6043RoundedFacts : LeafRoundedFacts 8
    leaf6043Certificate.logOnePlusV leaf6043InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6043InputLogOnePlusV_eq }

private noncomputable def leaf6043Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi267InputQChi innerPair699Input
    leaf6043InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6043LowerChecked :
    lowerCheck 24 leaf6043Box leaf6043Inputs = true := by
  rfl'

private theorem leaf6043CoversExact : CoversExact 8
    leaf6043Box leaf6043Certificate leaf6043InnerLog leaf6043Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi267RoundedFacts
    innerPair699RoundedFacts leaf6043RoundedFacts (by rfl)

private theorem leaf6043FlatSound : Sound leaf6043Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6043CertificateValid
    leaf6043InnerLogValid leaf6043CoversExact leaf6043LowerChecked

private noncomputable def leaf6044Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf6044Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712472576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (705107585/536870912) }, upper := { exponent := 1, mantissa := (1367/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428869117/137424945152) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6044InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6044LocalValidity :
    LeafFacts leaf6044Box leaf6044Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6044Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712472576) }) = true
      norm_num [leaf6044Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6044CertificateValid :
    WideCertificateValid leaf6044Box leaf6044Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi267ValidityFacts
    leaf6044LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6044CoverageChecked :
    coverageCheck (innerAD leaf6044Box) leaf6044InnerLog = true := by
  rfl'

private theorem leaf6044InnerLogValid :
    leaf6044InnerLog.Valid 8 (innerAD leaf6044Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6044CoverageChecked

private noncomputable def leaf6044InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453695/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6044InputLogOnePlusV_eq :
    leaf6044InputLogOnePlusV = outerEnclosure 24
      (leaf6044Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6044RoundedFacts : LeafRoundedFacts 8
    leaf6044Certificate.logOnePlusV leaf6044InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6044InputLogOnePlusV_eq }

private noncomputable def leaf6044Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi267InputQChi innerPair345Input
    leaf6044InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6044LowerChecked :
    lowerCheck 24 leaf6044Box leaf6044Inputs = true := by
  rfl'

private theorem leaf6044CoversExact : CoversExact 8
    leaf6044Box leaf6044Certificate leaf6044InnerLog leaf6044Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi267RoundedFacts
    innerPair345RoundedFacts leaf6044RoundedFacts (by rfl)

private theorem leaf6044FlatSound : Sound leaf6044Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6044CertificateValid
    leaf6044InnerLogValid leaf6044CoversExact leaf6044LowerChecked

private noncomputable def leaf6045Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6045Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712409088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (709170569/536870912) }, upper := { exponent := 1, mantissa := (5499/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428805629/137424818176) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6045InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6045LocalValidity :
    LeafFacts leaf6045Box leaf6045Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6045Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712409088) }) = true
      norm_num [leaf6045Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6045CertificateValid :
    WideCertificateValid leaf6045Box leaf6045Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi268ValidityFacts
    leaf6045LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6045CoverageChecked :
    coverageCheck (innerAD leaf6045Box) leaf6045InnerLog = true := by
  rfl'

private theorem leaf6045InnerLogValid :
    leaf6045InnerLog.Valid 8 (innerAD leaf6045Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6045CoverageChecked

private noncomputable def leaf6045InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf6045InputLogOnePlusV_eq :
    leaf6045InputLogOnePlusV = outerEnclosure 24
      (leaf6045Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6045RoundedFacts : LeafRoundedFacts 8
    leaf6045Certificate.logOnePlusV leaf6045InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6045InputLogOnePlusV_eq }

private noncomputable def leaf6045Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi268InputQChi innerPair345Input
    leaf6045InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6045LowerChecked :
    lowerCheck 24 leaf6045Box leaf6045Inputs = true := by
  rfl'

private theorem leaf6045CoversExact : CoversExact 8
    leaf6045Box leaf6045Certificate leaf6045InnerLog leaf6045Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi268RoundedFacts
    innerPair345RoundedFacts leaf6045RoundedFacts (by rfl)

private theorem leaf6045FlatSound : Sound leaf6045Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6045CertificateValid
    leaf6045InnerLogValid leaf6045CoversExact leaf6045LowerChecked

private noncomputable def leaf6046Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf6046Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712349696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (712905891/536870912) }, upper := { exponent := 1, mantissa := (691/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428746237/137424699392) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6046InnerLog : WideLogData :=
  innerPair365Data

set_option maxRecDepth 1000000 in
private theorem leaf6046LocalValidity :
    LeafFacts leaf6046Box leaf6046Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6046Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712349696) }) = true
      norm_num [leaf6046Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6046CertificateValid :
    WideCertificateValid leaf6046Box leaf6046Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi268ValidityFacts
    leaf6046LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6046CoverageChecked :
    coverageCheck (innerAD leaf6046Box) leaf6046InnerLog = true := by
  rfl'

private theorem leaf6046InnerLogValid :
    leaf6046InnerLog.Valid 8 (innerAD leaf6046Box) :=
  wideLogDataValid_of_cachedCheck endpoint95PositiveFacts
    endpoint451PositiveFacts.valid leaf6046CoverageChecked

private noncomputable def leaf6046InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6046InputLogOnePlusV_eq :
    leaf6046InputLogOnePlusV = outerEnclosure 24
      (leaf6046Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6046RoundedFacts : LeafRoundedFacts 8
    leaf6046Certificate.logOnePlusV leaf6046InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6046InputLogOnePlusV_eq }

private noncomputable def leaf6046Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi268InputQChi innerPair365Input
    leaf6046InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6046LowerChecked :
    lowerCheck 24 leaf6046Box leaf6046Inputs = true := by
  rfl'

private theorem leaf6046CoversExact : CoversExact 8
    leaf6046Box leaf6046Certificate leaf6046InnerLog leaf6046Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi268RoundedFacts
    innerPair365RoundedFacts leaf6046RoundedFacts (by rfl)

private theorem leaf6046FlatSound : Sound leaf6046Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6046CertificateValid
    leaf6046InnerLogValid leaf6046CoversExact leaf6046LowerChecked

private noncomputable def leaf6047Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6047Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712408064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (709301635/536870912) }, upper := { exponent := 1, mantissa := (10999/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428804605/137424816128) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6047InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6047LocalValidity :
    LeafFacts leaf6047Box leaf6047Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6047Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712408064) }) = true
      norm_num [leaf6047Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6047CertificateValid :
    WideCertificateValid leaf6047Box leaf6047Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi269ValidityFacts
    leaf6047LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6047CoverageChecked :
    coverageCheck (innerAD leaf6047Box) leaf6047InnerLog = true := by
  rfl'

private theorem leaf6047InnerLogValid :
    leaf6047InnerLog.Valid 8 (innerAD leaf6047Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6047CoverageChecked

private noncomputable def leaf6047InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11357/16384) }

set_option maxRecDepth 1000000 in
private theorem leaf6047InputLogOnePlusV_eq :
    leaf6047InputLogOnePlusV = outerEnclosure 24
      (leaf6047Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6047RoundedFacts : LeafRoundedFacts 8
    leaf6047Certificate.logOnePlusV leaf6047InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6047InputLogOnePlusV_eq }

private noncomputable def leaf6047Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi269InputQChi innerPair345Input
    leaf6047InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6047LowerChecked :
    lowerCheck 24 leaf6047Box leaf6047Inputs = true := by
  rfl'

private theorem leaf6047CoversExact : CoversExact 8
    leaf6047Box leaf6047Certificate leaf6047InnerLog leaf6047Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi269RoundedFacts
    innerPair345RoundedFacts leaf6047RoundedFacts (by rfl)

private theorem leaf6047FlatSound : Sound leaf6047Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6047CertificateValid
    leaf6047InnerLogValid leaf6047CoversExact leaf6047LowerChecked

private noncomputable def leaf6048Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6048Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712347648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (713102489/536870912) }, upper := { exponent := 1, mantissa := (5529/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428744189/137424695296) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6048InnerLog : WideLogData :=
  innerPair702Data

set_option maxRecDepth 1000000 in
private theorem leaf6048LocalValidity :
    LeafFacts leaf6048Box leaf6048Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6048Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712347648) }) = true
      norm_num [leaf6048Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6048CertificateValid :
    WideCertificateValid leaf6048Box leaf6048Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi269ValidityFacts
    leaf6048LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6048CoverageChecked :
    coverageCheck (innerAD leaf6048Box) leaf6048InnerLog = true := by
  rfl'

private theorem leaf6048InnerLogValid :
    leaf6048InnerLog.Valid 8 (innerAD leaf6048Box) :=
  wideLogDataValid_of_cachedCheck endpoint447PositiveFacts
    endpoint451PositiveFacts.valid leaf6048CoverageChecked

private noncomputable def leaf6048InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6048InputLogOnePlusV_eq :
    leaf6048InputLogOnePlusV = outerEnclosure 24
      (leaf6048Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6048RoundedFacts : LeafRoundedFacts 8
    leaf6048Certificate.logOnePlusV leaf6048InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6048InputLogOnePlusV_eq }

private noncomputable def leaf6048Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi269InputQChi innerPair702Input
    leaf6048InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6048LowerChecked :
    lowerCheck 24 leaf6048Box leaf6048Inputs = true := by
  rfl'

private theorem leaf6048CoversExact : CoversExact 8
    leaf6048Box leaf6048Certificate leaf6048InnerLog leaf6048Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi269RoundedFacts
    innerPair702RoundedFacts leaf6048RoundedFacts (by rfl)

private theorem leaf6048FlatSound : Sound leaf6048Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6048CertificateValid
    leaf6048InnerLogValid leaf6048CoversExact leaf6048LowerChecked

private noncomputable def leaf6049Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6049Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712288256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (716903345/536870912) }, upper := { exponent := 1, mantissa := (2779/2048) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428684797/137424576512) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6049InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6049LocalValidity :
    LeafFacts leaf6049Box leaf6049Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6049Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712288256) }) = true
      norm_num [leaf6049Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6049CertificateValid :
    WideCertificateValid leaf6049Box leaf6049Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi270ValidityFacts
    leaf6049LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6049CoverageChecked :
    coverageCheck (innerAD leaf6049Box) leaf6049InnerLog = true := by
  rfl'

private theorem leaf6049InnerLogValid :
    leaf6049InnerLog.Valid 8 (innerAD leaf6049Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6049CoverageChecked

private noncomputable def leaf6049InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6049InputLogOnePlusV_eq :
    leaf6049InputLogOnePlusV = outerEnclosure 24
      (leaf6049Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6049RoundedFacts : LeafRoundedFacts 8
    leaf6049Certificate.logOnePlusV leaf6049InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6049InputLogOnePlusV_eq }

private noncomputable def leaf6049Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi270InputQChi innerPair346Input
    leaf6049InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6049LowerChecked :
    lowerCheck 24 leaf6049Box leaf6049Inputs = true := by
  rfl'

private theorem leaf6049CoversExact : CoversExact 8
    leaf6049Box leaf6049Certificate leaf6049InnerLog leaf6049Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi270RoundedFacts
    innerPair346RoundedFacts leaf6049RoundedFacts (by rfl)

private theorem leaf6049FlatSound : Sound leaf6049Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6049CertificateValid
    leaf6049InnerLogValid leaf6049CoversExact leaf6049LowerChecked

private noncomputable def leaf6050Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6050Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712226816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (720769731/536870912) }, upper := { exponent := 1, mantissa := (1397/1024) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428623357/137424453632) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6050InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6050LocalValidity :
    LeafFacts leaf6050Box leaf6050Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6050Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712226816) }) = true
      norm_num [leaf6050Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6050CertificateValid :
    WideCertificateValid leaf6050Box leaf6050Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi270ValidityFacts
    leaf6050LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6050CoverageChecked :
    coverageCheck (innerAD leaf6050Box) leaf6050InnerLog = true := by
  rfl'

private theorem leaf6050InnerLogValid :
    leaf6050InnerLog.Valid 8 (innerAD leaf6050Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6050CoverageChecked

private noncomputable def leaf6050InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814795/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6050InputLogOnePlusV_eq :
    leaf6050InputLogOnePlusV = outerEnclosure 24
      (leaf6050Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6050RoundedFacts : LeafRoundedFacts 8
    leaf6050Certificate.logOnePlusV leaf6050InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6050InputLogOnePlusV_eq }

private noncomputable def leaf6050Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi270InputQChi innerPair346Input
    leaf6050InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6050LowerChecked :
    lowerCheck 24 leaf6050Box leaf6050Inputs = true := by
  rfl'

private theorem leaf6050CoversExact : CoversExact 8
    leaf6050Box leaf6050Certificate leaf6050InnerLog leaf6050Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi270RoundedFacts
    innerPair346RoundedFacts leaf6050RoundedFacts (by rfl)

private theorem leaf6050FlatSound : Sound leaf6050Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6050CertificateValid
    leaf6050InnerLogValid leaf6050CoversExact leaf6050LowerChecked

private noncomputable def leaf6051Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6051Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712287232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (716903343/536870912) }, upper := { exponent := 1, mantissa := (11117/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428683773/137424574464) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6051InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6051LocalValidity :
    LeafFacts leaf6051Box leaf6051Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6051Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712287232) }) = true
      norm_num [leaf6051Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6051CertificateValid :
    WideCertificateValid leaf6051Box leaf6051Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi269ValidityFacts
    leaf6051LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6051CoverageChecked :
    coverageCheck (innerAD leaf6051Box) leaf6051InnerLog = true := by
  rfl'

private theorem leaf6051InnerLogValid :
    leaf6051InnerLog.Valid 8 (innerAD leaf6051Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6051CoverageChecked

private noncomputable def leaf6051InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6051InputLogOnePlusV_eq :
    leaf6051InputLogOnePlusV = outerEnclosure 24
      (leaf6051Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6051RoundedFacts : LeafRoundedFacts 8
    leaf6051Certificate.logOnePlusV leaf6051InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6051InputLogOnePlusV_eq }

private noncomputable def leaf6051Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi269InputQChi innerPair346Input
    leaf6051InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6051LowerChecked :
    lowerCheck 24 leaf6051Box leaf6051Inputs = true := by
  rfl'

private theorem leaf6051CoversExact : CoversExact 8
    leaf6051Box leaf6051Certificate leaf6051InnerLog leaf6051Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi269RoundedFacts
    innerPair346RoundedFacts leaf6051RoundedFacts (by rfl)

private theorem leaf6051FlatSound : Sound leaf6051Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6051CertificateValid
    leaf6051InnerLogValid leaf6051CoversExact leaf6051LowerChecked

private noncomputable def leaf6052Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf6052Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712226816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (720704197/536870912) }, upper := { exponent := 1, mantissa := (1397/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428623357/137424453632) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6052InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6052LocalValidity :
    LeafFacts leaf6052Box leaf6052Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6052Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712226816) }) = true
      norm_num [leaf6052Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6052CertificateValid :
    WideCertificateValid leaf6052Box leaf6052Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi269ValidityFacts
    leaf6052LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6052CoverageChecked :
    coverageCheck (innerAD leaf6052Box) leaf6052InnerLog = true := by
  rfl'

private theorem leaf6052InnerLogValid :
    leaf6052InnerLog.Valid 8 (innerAD leaf6052Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6052CoverageChecked

private noncomputable def leaf6052InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814795/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6052InputLogOnePlusV_eq :
    leaf6052InputLogOnePlusV = outerEnclosure 24
      (leaf6052Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6052RoundedFacts : LeafRoundedFacts 8
    leaf6052Certificate.logOnePlusV leaf6052InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6052InputLogOnePlusV_eq }

private noncomputable def leaf6052Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi269InputQChi innerPair346Input
    leaf6052InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6052LowerChecked :
    lowerCheck 24 leaf6052Box leaf6052Inputs = true := by
  rfl'

private theorem leaf6052CoversExact : CoversExact 8
    leaf6052Box leaf6052Certificate leaf6052InnerLog leaf6052Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi269RoundedFacts
    innerPair346RoundedFacts leaf6052RoundedFacts (by rfl)

private theorem leaf6052FlatSound : Sound leaf6052Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6052CertificateValid
    leaf6052InnerLogValid leaf6052CoversExact leaf6052LowerChecked

private noncomputable def leaf6053Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6053Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712165376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (724636117/536870912) }, upper := { exponent := 1, mantissa := (2809/2048) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428561917/137424330752) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6053InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6053LocalValidity :
    LeafFacts leaf6053Box leaf6053Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6053Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712165376) }) = true
      norm_num [leaf6053Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6053CertificateValid :
    WideCertificateValid leaf6053Box leaf6053Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi270ValidityFacts
    leaf6053LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6053CoverageChecked :
    coverageCheck (innerAD leaf6053Box) leaf6053InnerLog = true := by
  rfl'

private theorem leaf6053InnerLogValid :
    leaf6053InnerLog.Valid 8 (innerAD leaf6053Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6053CoverageChecked

private noncomputable def leaf6053InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6053InputLogOnePlusV_eq :
    leaf6053InputLogOnePlusV = outerEnclosure 24
      (leaf6053Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6053RoundedFacts : LeafRoundedFacts 8
    leaf6053Certificate.logOnePlusV leaf6053InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6053InputLogOnePlusV_eq }

private noncomputable def leaf6053Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi270InputQChi innerPair352Input
    leaf6053InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6053LowerChecked :
    lowerCheck 24 leaf6053Box leaf6053Inputs = true := by
  rfl'

private theorem leaf6053CoversExact : CoversExact 8
    leaf6053Box leaf6053Certificate leaf6053InnerLog leaf6053Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi270RoundedFacts
    innerPair352RoundedFacts leaf6053RoundedFacts (by rfl)

private theorem leaf6053FlatSound : Sound leaf6053Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6053CertificateValid
    leaf6053InnerLogValid leaf6053CoversExact leaf6053LowerChecked

private noncomputable def leaf6054Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf6054Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712103936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (728502503/536870912) }, upper := { exponent := 1, mantissa := (353/256) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428500477/137424207872) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6054InnerLog : WideLogData :=
  innerPair708Data

set_option maxRecDepth 1000000 in
private theorem leaf6054LocalValidity :
    LeafFacts leaf6054Box leaf6054Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6054Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712103936) }) = true
      norm_num [leaf6054Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6054CertificateValid :
    WideCertificateValid leaf6054Box leaf6054Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi270ValidityFacts
    leaf6054LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6054CoverageChecked :
    coverageCheck (innerAD leaf6054Box) leaf6054InnerLog = true := by
  rfl'

private theorem leaf6054InnerLogValid :
    leaf6054InnerLog.Valid 8 (innerAD leaf6054Box) :=
  wideLogDataValid_of_cachedCheck endpoint451PositiveFacts
    endpoint460PositiveFacts.valid leaf6054CoverageChecked

private noncomputable def leaf6054InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6054InputLogOnePlusV_eq :
    leaf6054InputLogOnePlusV = outerEnclosure 24
      (leaf6054Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6054RoundedFacts : LeafRoundedFacts 8
    leaf6054Certificate.logOnePlusV leaf6054InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6054InputLogOnePlusV_eq }

private noncomputable def leaf6054Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi270InputQChi innerPair708Input
    leaf6054InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6054LowerChecked :
    lowerCheck 24 leaf6054Box leaf6054Inputs = true := by
  rfl'

private theorem leaf6054CoversExact : CoversExact 8
    leaf6054Box leaf6054Certificate leaf6054InnerLog leaf6054Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi270RoundedFacts
    innerPair708RoundedFacts leaf6054RoundedFacts (by rfl)

private theorem leaf6054FlatSound : Sound leaf6054Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6054CertificateValid
    leaf6054InnerLogValid leaf6054CoversExact leaf6054LowerChecked

private noncomputable def leaf6055Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6055Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435803/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712418304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (708777383/536870912) }, upper := { exponent := 1, mantissa := (10989/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428814845/137424836608) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6055InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6055LocalValidity :
    LeafFacts leaf6055Box leaf6055Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6055Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712418304) }) = true
      norm_num [leaf6055Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6055CertificateValid :
    WideCertificateValid leaf6055Box leaf6055Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi271ValidityFacts
    leaf6055LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6055CoverageChecked :
    coverageCheck (innerAD leaf6055Box) leaf6055InnerLog = true := by
  rfl'

private theorem leaf6055InnerLogValid :
    leaf6055InnerLog.Valid 8 (innerAD leaf6055Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6055CoverageChecked

private noncomputable def leaf6055InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814783/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6055InputLogOnePlusV_eq :
    leaf6055InputLogOnePlusV = outerEnclosure 24
      (leaf6055Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6055RoundedFacts : LeafRoundedFacts 8
    leaf6055Certificate.logOnePlusV leaf6055InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6055InputLogOnePlusV_eq }

private noncomputable def leaf6055Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi271InputQChi innerPair345Input
    leaf6055InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6055LowerChecked :
    lowerCheck 24 leaf6055Box leaf6055Inputs = true := by
  rfl'

private theorem leaf6055CoversExact : CoversExact 8
    leaf6055Box leaf6055Certificate leaf6055InnerLog leaf6055Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi271RoundedFacts
    innerPair345RoundedFacts leaf6055RoundedFacts (by rfl)

private theorem leaf6055FlatSound : Sound leaf6055Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6055CertificateValid
    leaf6055InnerLogValid leaf6055CoversExact leaf6055LowerChecked

private noncomputable def leaf6056Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6056Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712355840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (712709301/536870912) }, upper := { exponent := 1, mantissa := (5525/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428752381/137424711680) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6056InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6056LocalValidity :
    LeafFacts leaf6056Box leaf6056Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6056Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712355840) }) = true
      norm_num [leaf6056Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6056CertificateValid :
    WideCertificateValid leaf6056Box leaf6056Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi271ValidityFacts
    leaf6056LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6056CoverageChecked :
    coverageCheck (innerAD leaf6056Box) leaf6056InnerLog = true := by
  rfl'

private theorem leaf6056InnerLogValid :
    leaf6056InnerLog.Valid 8 (innerAD leaf6056Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6056CoverageChecked

private noncomputable def leaf6056InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814787/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6056InputLogOnePlusV_eq :
    leaf6056InputLogOnePlusV = outerEnclosure 24
      (leaf6056Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6056RoundedFacts : LeafRoundedFacts 8
    leaf6056Certificate.logOnePlusV leaf6056InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6056InputLogOnePlusV_eq }

private noncomputable def leaf6056Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi271InputQChi innerPair346Input
    leaf6056InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6056LowerChecked :
    lowerCheck 24 leaf6056Box leaf6056Inputs = true := by
  rfl'

private theorem leaf6056CoversExact : CoversExact 8
    leaf6056Box leaf6056Certificate leaf6056InnerLog leaf6056Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi271RoundedFacts
    innerPair346RoundedFacts leaf6056RoundedFacts (by rfl)

private theorem leaf6056FlatSound : Sound leaf6056Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6056CertificateValid
    leaf6056InnerLogValid leaf6056CoversExact leaf6056LowerChecked

private noncomputable def leaf6057Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6057Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435805/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712302592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (716116965/536870912) }, upper := { exponent := 1, mantissa := (5551/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428699133/137424605184) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6057InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6057LocalValidity :
    LeafFacts leaf6057Box leaf6057Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6057Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712302592) }) = true
      norm_num [leaf6057Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6057CertificateValid :
    WideCertificateValid leaf6057Box leaf6057Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi272ValidityFacts
    leaf6057LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6057CoverageChecked :
    coverageCheck (innerAD leaf6057Box) leaf6057InnerLog = true := by
  rfl'

private theorem leaf6057InnerLogValid :
    leaf6057InnerLog.Valid 8 (innerAD leaf6057Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6057CoverageChecked

private noncomputable def leaf6057InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6057InputLogOnePlusV_eq :
    leaf6057InputLogOnePlusV = outerEnclosure 24
      (leaf6057Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6057RoundedFacts : LeafRoundedFacts 8
    leaf6057Certificate.logOnePlusV leaf6057InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6057InputLogOnePlusV_eq }

private noncomputable def leaf6057Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi272InputQChi innerPair346Input
    leaf6057InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6057LowerChecked :
    lowerCheck 24 leaf6057Box leaf6057Inputs = true := by
  rfl'

private theorem leaf6057CoversExact : CoversExact 8
    leaf6057Box leaf6057Certificate leaf6057InnerLog leaf6057Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi272RoundedFacts
    innerPair346RoundedFacts leaf6057RoundedFacts (by rfl)

private theorem leaf6057FlatSound : Sound leaf6057Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6057CertificateValid
    leaf6057InnerLogValid leaf6057CoversExact leaf6057LowerChecked

private noncomputable def leaf6058Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6058Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712239104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (720114415/536870912) }, upper := { exponent := 1, mantissa := (2791/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428635645/137424478208) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6058InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6058LocalValidity :
    LeafFacts leaf6058Box leaf6058Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6058Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712239104) }) = true
      norm_num [leaf6058Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6058CertificateValid :
    WideCertificateValid leaf6058Box leaf6058Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi272ValidityFacts
    leaf6058LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6058CoverageChecked :
    coverageCheck (innerAD leaf6058Box) leaf6058InnerLog = true := by
  rfl'

private theorem leaf6058InnerLogValid :
    leaf6058InnerLog.Valid 8 (innerAD leaf6058Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6058CoverageChecked

private noncomputable def leaf6058InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6058InputLogOnePlusV_eq :
    leaf6058InputLogOnePlusV = outerEnclosure 24
      (leaf6058Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6058RoundedFacts : LeafRoundedFacts 8
    leaf6058Certificate.logOnePlusV leaf6058InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6058InputLogOnePlusV_eq }

private noncomputable def leaf6058Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi272InputQChi innerPair346Input
    leaf6058InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6058LowerChecked :
    lowerCheck 24 leaf6058Box leaf6058Inputs = true := by
  rfl'

private theorem leaf6058CoversExact : CoversExact 8
    leaf6058Box leaf6058Certificate leaf6058InnerLog leaf6058Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi272RoundedFacts
    innerPair346RoundedFacts leaf6058RoundedFacts (by rfl)

private theorem leaf6058FlatSound : Sound leaf6058Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6058CertificateValid
    leaf6058InnerLogValid leaf6058CoversExact leaf6058LowerChecked

private noncomputable def leaf6059Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6059Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712293376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (716641219/536870912) }, upper := { exponent := 1, mantissa := (11111/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428689917/137424586752) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6059InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6059LocalValidity :
    LeafFacts leaf6059Box leaf6059Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6059Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712293376) }) = true
      norm_num [leaf6059Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6059CertificateValid :
    WideCertificateValid leaf6059Box leaf6059Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi271ValidityFacts
    leaf6059LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6059CoverageChecked :
    coverageCheck (innerAD leaf6059Box) leaf6059InnerLog = true := by
  rfl'

private theorem leaf6059InnerLogValid :
    leaf6059InnerLog.Valid 8 (innerAD leaf6059Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6059CoverageChecked

private noncomputable def leaf6059InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6059InputLogOnePlusV_eq :
    leaf6059InputLogOnePlusV = outerEnclosure 24
      (leaf6059Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6059RoundedFacts : LeafRoundedFacts 8
    leaf6059Certificate.logOnePlusV leaf6059InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6059InputLogOnePlusV_eq }

private noncomputable def leaf6059Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi271InputQChi innerPair346Input
    leaf6059InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6059LowerChecked :
    lowerCheck 24 leaf6059Box leaf6059Inputs = true := by
  rfl'

private theorem leaf6059CoversExact : CoversExact 8
    leaf6059Box leaf6059Certificate leaf6059InnerLog leaf6059Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi271RoundedFacts
    innerPair346RoundedFacts leaf6059RoundedFacts (by rfl)

private theorem leaf6059FlatSound : Sound leaf6059Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6059CertificateValid
    leaf6059InnerLogValid leaf6059CoversExact leaf6059LowerChecked

private noncomputable def leaf6060Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6060Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (310933921/310915072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (720573137/536870912) }, upper := { exponent := 1, mantissa := (2793/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (621848993/621830144) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6060InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6060LocalValidity :
    LeafFacts leaf6060Box leaf6060Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6060Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (310933921/310915072) }) = true
      norm_num [leaf6060Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6060CertificateValid :
    WideCertificateValid leaf6060Box leaf6060Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi271ValidityFacts
    leaf6060LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6060CoverageChecked :
    coverageCheck (innerAD leaf6060Box) leaf6060InnerLog = true := by
  rfl'

private theorem leaf6060InnerLogValid :
    leaf6060InnerLog.Valid 8 (innerAD leaf6060Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6060CoverageChecked

private noncomputable def leaf6060InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6060InputLogOnePlusV_eq :
    leaf6060InputLogOnePlusV = outerEnclosure 24
      (leaf6060Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6060RoundedFacts : LeafRoundedFacts 8
    leaf6060Certificate.logOnePlusV leaf6060InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6060InputLogOnePlusV_eq }

private noncomputable def leaf6060Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi271InputQChi innerPair346Input
    leaf6060InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6060LowerChecked :
    lowerCheck 24 leaf6060Box leaf6060Inputs = true := by
  rfl'

private theorem leaf6060CoversExact : CoversExact 8
    leaf6060Box leaf6060Certificate leaf6060InnerLog leaf6060Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi271RoundedFacts
    innerPair346RoundedFacts leaf6060RoundedFacts (by rfl)

private theorem leaf6060FlatSound : Sound leaf6060Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6060CertificateValid
    leaf6060InnerLogValid leaf6060CoversExact leaf6060LowerChecked

private noncomputable def leaf6061Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6061Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712175616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (724111865/536870912) }, upper := { exponent := 1, mantissa := (5613/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428572157/137424351232) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6061InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6061LocalValidity :
    LeafFacts leaf6061Box leaf6061Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6061Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712175616) }) = true
      norm_num [leaf6061Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6061CertificateValid :
    WideCertificateValid leaf6061Box leaf6061Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi272ValidityFacts
    leaf6061LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6061CoverageChecked :
    coverageCheck (innerAD leaf6061Box) leaf6061InnerLog = true := by
  rfl'

private theorem leaf6061InnerLogValid :
    leaf6061InnerLog.Valid 8 (innerAD leaf6061Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6061CoverageChecked

private noncomputable def leaf6061InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907399/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6061InputLogOnePlusV_eq :
    leaf6061InputLogOnePlusV = outerEnclosure 24
      (leaf6061Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6061RoundedFacts : LeafRoundedFacts 8
    leaf6061Certificate.logOnePlusV leaf6061InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6061InputLogOnePlusV_eq }

private noncomputable def leaf6061Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi272InputQChi innerPair352Input
    leaf6061InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6061LowerChecked :
    lowerCheck 24 leaf6061Box leaf6061Inputs = true := by
  rfl'

private theorem leaf6061CoversExact : CoversExact 8
    leaf6061Box leaf6061Certificate leaf6061InnerLog leaf6061Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi272RoundedFacts
    innerPair352RoundedFacts leaf6061RoundedFacts (by rfl)

private theorem leaf6061FlatSound : Sound leaf6061Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6061CertificateValid
    leaf6061InnerLogValid leaf6061CoversExact leaf6061LowerChecked

private noncomputable def leaf6062Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6062Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712112128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (728109315/536870912) }, upper := { exponent := 1, mantissa := (1411/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428508669/137424224256) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6062InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6062LocalValidity :
    LeafFacts leaf6062Box leaf6062Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6062Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712112128) }) = true
      norm_num [leaf6062Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6062CertificateValid :
    WideCertificateValid leaf6062Box leaf6062Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi272ValidityFacts
    leaf6062LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6062CoverageChecked :
    coverageCheck (innerAD leaf6062Box) leaf6062InnerLog = true := by
  rfl'

private theorem leaf6062InnerLogValid :
    leaf6062InnerLog.Valid 8 (innerAD leaf6062Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6062CoverageChecked

private noncomputable def leaf6062InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907401/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6062InputLogOnePlusV_eq :
    leaf6062InputLogOnePlusV = outerEnclosure 24
      (leaf6062Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6062RoundedFacts : LeafRoundedFacts 8
    leaf6062Certificate.logOnePlusV leaf6062InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6062InputLogOnePlusV_eq }

private noncomputable def leaf6062Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi272InputQChi innerPair353Input
    leaf6062InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6062LowerChecked :
    lowerCheck 24 leaf6062Box leaf6062Inputs = true := by
  rfl'

private theorem leaf6062CoversExact : CoversExact 8
    leaf6062Box leaf6062Certificate leaf6062InnerLog leaf6062Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi272RoundedFacts
    innerPair353RoundedFacts leaf6062RoundedFacts (by rfl)

private theorem leaf6062FlatSound : Sound leaf6062Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6062CertificateValid
    leaf6062InnerLogValid leaf6062CoversExact leaf6062LowerChecked

private noncomputable def leaf6063Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6063Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435807/268435456) }, vSqrt := { lower := (8191/8192), upper := (967836571/967777280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (723456547/536870912) }, upper := { exponent := 1, mantissa := (11215/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1935613851/1935554560) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6063InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6063LocalValidity :
    LeafFacts leaf6063Box leaf6063Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6063Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (967836571/967777280) }) = true
      norm_num [leaf6063Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6063CertificateValid :
    WideCertificateValid leaf6063Box leaf6063Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi273ValidityFacts
    leaf6063LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6063CoverageChecked :
    coverageCheck (innerAD leaf6063Box) leaf6063InnerLog = true := by
  rfl'

private theorem leaf6063InnerLogValid :
    leaf6063InnerLog.Valid 8 (innerAD leaf6063Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6063CoverageChecked

private noncomputable def leaf6063InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629595/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6063InputLogOnePlusV_eq :
    leaf6063InputLogOnePlusV = outerEnclosure 24
      (leaf6063Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6063RoundedFacts : LeafRoundedFacts 8
    leaf6063Certificate.logOnePlusV leaf6063InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6063InputLogOnePlusV_eq }

private noncomputable def leaf6063Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi273InputQChi innerPair352Input
    leaf6063InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6063LowerChecked :
    lowerCheck 24 leaf6063Box leaf6063Inputs = true := by
  rfl'

private theorem leaf6063CoversExact : CoversExact 8
    leaf6063Box leaf6063Certificate leaf6063InnerLog leaf6063Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi273RoundedFacts
    innerPair352RoundedFacts leaf6063RoundedFacts (by rfl)

private theorem leaf6063FlatSound : Sound leaf6063Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6063CertificateValid
    leaf6063InnerLogValid leaf6063CoversExact leaf6063LowerChecked

private noncomputable def leaf6064Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6064Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712122368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (727519529/536870912) }, upper := { exponent := 1, mantissa := (5639/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428518909/137424244736) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6064InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6064LocalValidity :
    LeafFacts leaf6064Box leaf6064Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6064Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712122368) }) = true
      norm_num [leaf6064Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6064CertificateValid :
    WideCertificateValid leaf6064Box leaf6064Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi273ValidityFacts
    leaf6064LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6064CoverageChecked :
    coverageCheck (innerAD leaf6064Box) leaf6064InnerLog = true := by
  rfl'

private theorem leaf6064InnerLogValid :
    leaf6064InnerLog.Valid 8 (innerAD leaf6064Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6064CoverageChecked

private noncomputable def leaf6064InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629603/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6064InputLogOnePlusV_eq :
    leaf6064InputLogOnePlusV = outerEnclosure 24
      (leaf6064Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6064RoundedFacts : LeafRoundedFacts 8
    leaf6064Certificate.logOnePlusV leaf6064InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6064InputLogOnePlusV_eq }

private noncomputable def leaf6064Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi273InputQChi innerPair353Input
    leaf6064InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6064LowerChecked :
    lowerCheck 24 leaf6064Box leaf6064Inputs = true := by
  rfl'

private theorem leaf6064CoversExact : CoversExact 8
    leaf6064Box leaf6064Certificate leaf6064InnerLog leaf6064Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi273RoundedFacts
    innerPair353RoundedFacts leaf6064RoundedFacts (by rfl)

private theorem leaf6064FlatSound : Sound leaf6064Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6064CertificateValid
    leaf6064InnerLogValid leaf6064CoversExact leaf6064LowerChecked

private noncomputable def leaf6065Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6065Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435809/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285543936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (730796129/536870912) }, upper := { exponent := 1, mantissa := (177/128) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571420593/10571087872) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6065InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6065LocalValidity :
    LeafFacts leaf6065Box leaf6065Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6065Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285543936) }) = true
      norm_num [leaf6065Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6065CertificateValid :
    WideCertificateValid leaf6065Box leaf6065Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi274ValidityFacts
    leaf6065LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6065CoverageChecked :
    coverageCheck (innerAD leaf6065Box) leaf6065InnerLog = true := by
  rfl'

private theorem leaf6065InnerLogValid :
    leaf6065InnerLog.Valid 8 (innerAD leaf6065Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6065CoverageChecked

private noncomputable def leaf6065InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629609/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6065InputLogOnePlusV_eq :
    leaf6065InputLogOnePlusV = outerEnclosure 24
      (leaf6065Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6065RoundedFacts : LeafRoundedFacts 8
    leaf6065Certificate.logOnePlusV leaf6065InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6065InputLogOnePlusV_eq }

private noncomputable def leaf6065Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi274InputQChi innerPair353Input
    leaf6065InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6065LowerChecked :
    lowerCheck 24 leaf6065Box leaf6065Inputs = true := by
  rfl'

private theorem leaf6065CoversExact : CoversExact 8
    leaf6065Box leaf6065Certificate leaf6065InnerLog leaf6065Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi274RoundedFacts
    innerPair353RoundedFacts leaf6065RoundedFacts (by rfl)

private theorem leaf6065FlatSound : Sound leaf6065Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6065CertificateValid
    leaf6065InnerLogValid leaf6065CoversExact leaf6065LowerChecked

private noncomputable def leaf6066Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6066Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712005632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (734924643/536870912) }, upper := { exponent := 1, mantissa := (89/64) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428402173/137424011264) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6066InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6066LocalValidity :
    LeafFacts leaf6066Box leaf6066Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6066Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712005632) }) = true
      norm_num [leaf6066Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6066CertificateValid :
    WideCertificateValid leaf6066Box leaf6066Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi274ValidityFacts
    leaf6066LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6066CoverageChecked :
    coverageCheck (innerAD leaf6066Box) leaf6066InnerLog = true := by
  rfl'

private theorem leaf6066InnerLogValid :
    leaf6066InnerLog.Valid 8 (innerAD leaf6066Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6066CoverageChecked

private noncomputable def leaf6066InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629617/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6066InputLogOnePlusV_eq :
    leaf6066InputLogOnePlusV = outerEnclosure 24
      (leaf6066Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6066RoundedFacts : LeafRoundedFacts 8
    leaf6066Certificate.logOnePlusV leaf6066InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6066InputLogOnePlusV_eq }

private noncomputable def leaf6066Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi274InputQChi innerPair353Input
    leaf6066InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6066LowerChecked :
    lowerCheck 24 leaf6066Box leaf6066Inputs = true := by
  rfl'

private theorem leaf6066CoversExact : CoversExact 8
    leaf6066Box leaf6066Certificate leaf6066InnerLog leaf6066Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi274RoundedFacts
    innerPair353RoundedFacts leaf6066RoundedFacts (by rfl)

private theorem leaf6066FlatSound : Sound leaf6066Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6066CertificateValid
    leaf6066InnerLogValid leaf6066CoversExact leaf6066LowerChecked

private noncomputable def leaf6067Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6067Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285542912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (731582511/536870912) }, upper := { exponent := 1, mantissa := (11341/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571419569/10571085824) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6067InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6067LocalValidity :
    LeafFacts leaf6067Box leaf6067Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6067Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285542912) }) = true
      norm_num [leaf6067Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6067CertificateValid :
    WideCertificateValid leaf6067Box leaf6067Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi273ValidityFacts
    leaf6067LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6067CoverageChecked :
    coverageCheck (innerAD leaf6067Box) leaf6067InnerLog = true := by
  rfl'

private theorem leaf6067InnerLogValid :
    leaf6067InnerLog.Valid 8 (innerAD leaf6067Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6067CoverageChecked

private noncomputable def leaf6067InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814805/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6067InputLogOnePlusV_eq :
    leaf6067InputLogOnePlusV = outerEnclosure 24
      (leaf6067Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6067RoundedFacts : LeafRoundedFacts 8
    leaf6067Certificate.logOnePlusV leaf6067InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6067InputLogOnePlusV_eq }

private noncomputable def leaf6067Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi273InputQChi innerPair353Input
    leaf6067InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6067LowerChecked :
    lowerCheck 24 leaf6067Box leaf6067Inputs = true := by
  rfl'

private theorem leaf6067CoversExact : CoversExact 8
    leaf6067Box leaf6067Certificate leaf6067InnerLog leaf6067Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi273RoundedFacts
    innerPair353RoundedFacts leaf6067RoundedFacts (by rfl)

private theorem leaf6067FlatSound : Sound leaf6067Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6067CertificateValid
    leaf6067InnerLogValid leaf6067CoversExact leaf6067LowerChecked

private noncomputable def leaf6068Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6068Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711993344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (735645493/536870912) }, upper := { exponent := 1, mantissa := (2851/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428389885/137423986688) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6068InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6068LocalValidity :
    LeafFacts leaf6068Box leaf6068Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6068Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711993344) }) = true
      norm_num [leaf6068Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6068CertificateValid :
    WideCertificateValid leaf6068Box leaf6068Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi273ValidityFacts
    leaf6068LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6068CoverageChecked :
    coverageCheck (innerAD leaf6068Box) leaf6068InnerLog = true := by
  rfl'

private theorem leaf6068InnerLogValid :
    leaf6068InnerLog.Valid 8 (innerAD leaf6068Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6068CoverageChecked

private noncomputable def leaf6068InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814809/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6068InputLogOnePlusV_eq :
    leaf6068InputLogOnePlusV = outerEnclosure 24
      (leaf6068Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6068RoundedFacts : LeafRoundedFacts 8
    leaf6068Certificate.logOnePlusV leaf6068InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6068InputLogOnePlusV_eq }

private noncomputable def leaf6068Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi273InputQChi innerPair353Input
    leaf6068InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6068LowerChecked :
    lowerCheck 24 leaf6068Box leaf6068Inputs = true := by
  rfl'

private theorem leaf6068CoversExact : CoversExact 8
    leaf6068Box leaf6068Certificate leaf6068InnerLog leaf6068Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi273RoundedFacts
    innerPair353RoundedFacts leaf6068RoundedFacts (by rfl)

private theorem leaf6068FlatSound : Sound leaf6068Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6068CertificateValid
    leaf6068InnerLogValid leaf6068CoversExact leaf6068LowerChecked

private noncomputable def leaf6069Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6069Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711940096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (739053157/536870912) }, upper := { exponent := 1, mantissa := (179/128) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428336637/137423880192) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6069InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6069LocalValidity :
    LeafFacts leaf6069Box leaf6069Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6069Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711940096) }) = true
      norm_num [leaf6069Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6069CertificateValid :
    WideCertificateValid leaf6069Box leaf6069Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi274ValidityFacts
    leaf6069LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6069CoverageChecked :
    coverageCheck (innerAD leaf6069Box) leaf6069InnerLog = true := by
  rfl'

private theorem leaf6069InnerLogValid :
    leaf6069InnerLog.Valid 8 (innerAD leaf6069Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6069CoverageChecked

private noncomputable def leaf6069InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6069InputLogOnePlusV_eq :
    leaf6069InputLogOnePlusV = outerEnclosure 24
      (leaf6069Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6069RoundedFacts : LeafRoundedFacts 8
    leaf6069Certificate.logOnePlusV leaf6069InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6069InputLogOnePlusV_eq }

private noncomputable def leaf6069Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi274InputQChi innerPair356Input
    leaf6069InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6069LowerChecked :
    lowerCheck 24 leaf6069Box leaf6069Inputs = true := by
  rfl'

private theorem leaf6069CoversExact : CoversExact 8
    leaf6069Box leaf6069Certificate leaf6069InnerLog leaf6069Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi274RoundedFacts
    innerPair356RoundedFacts leaf6069RoundedFacts (by rfl)

private theorem leaf6069FlatSound : Sound leaf6069Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6069CertificateValid
    leaf6069InnerLogValid leaf6069CoversExact leaf6069LowerChecked

private noncomputable def leaf6070Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6070Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711874560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (743181671/536870912) }, upper := { exponent := 1, mantissa := (45/32) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428271101/137423749120) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6070InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6070LocalValidity :
    LeafFacts leaf6070Box leaf6070Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6070Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711874560) }) = true
      norm_num [leaf6070Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6070CertificateValid :
    WideCertificateValid leaf6070Box leaf6070Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi274ValidityFacts
    leaf6070LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6070CoverageChecked :
    coverageCheck (innerAD leaf6070Box) leaf6070InnerLog = true := by
  rfl'

private theorem leaf6070InnerLogValid :
    leaf6070InnerLog.Valid 8 (innerAD leaf6070Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6070CoverageChecked

private noncomputable def leaf6070InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629633/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6070InputLogOnePlusV_eq :
    leaf6070InputLogOnePlusV = outerEnclosure 24
      (leaf6070Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6070RoundedFacts : LeafRoundedFacts 8
    leaf6070Certificate.logOnePlusV leaf6070InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6070InputLogOnePlusV_eq }

private noncomputable def leaf6070Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi274InputQChi innerPair356Input
    leaf6070InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6070LowerChecked :
    lowerCheck 24 leaf6070Box leaf6070Inputs = true := by
  rfl'

private theorem leaf6070CoversExact : CoversExact 8
    leaf6070Box leaf6070Certificate leaf6070InnerLog leaf6070Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi274RoundedFacts
    innerPair356RoundedFacts leaf6070RoundedFacts (by rfl)

private theorem leaf6070FlatSound : Sound leaf6070Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6070CertificateValid
    leaf6070InnerLogValid leaf6070CoversExact leaf6070LowerChecked

private noncomputable def leaf6071Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6071Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712168448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (724505055/536870912) }, upper := { exponent := 1, mantissa := (11233/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428564989/137424336896) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6071InnerLog : WideLogData :=
  innerPair352Data

set_option maxRecDepth 1000000 in
private theorem leaf6071LocalValidity :
    LeafFacts leaf6071Box leaf6071Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6071Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712168448) }) = true
      norm_num [leaf6071Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6071CertificateValid :
    WideCertificateValid leaf6071Box leaf6071Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi271ValidityFacts
    leaf6071LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6071CoverageChecked :
    coverageCheck (innerAD leaf6071Box) leaf6071InnerLog = true := by
  rfl'

private theorem leaf6071InnerLogValid :
    leaf6071InnerLog.Valid 8 (innerAD leaf6071Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint93PositiveFacts.valid leaf6071CoverageChecked

private noncomputable def leaf6071InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6071InputLogOnePlusV_eq :
    leaf6071InputLogOnePlusV = outerEnclosure 24
      (leaf6071Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6071RoundedFacts : LeafRoundedFacts 8
    leaf6071Certificate.logOnePlusV leaf6071InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6071InputLogOnePlusV_eq }

private noncomputable def leaf6071Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi271InputQChi innerPair352Input
    leaf6071InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6071LowerChecked :
    lowerCheck 24 leaf6071Box leaf6071Inputs = true := by
  rfl'

private theorem leaf6071CoversExact : CoversExact 8
    leaf6071Box leaf6071Certificate leaf6071InnerLog leaf6071Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi271RoundedFacts
    innerPair352RoundedFacts leaf6071RoundedFacts (by rfl)

private theorem leaf6071FlatSound : Sound leaf6071Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6071CertificateValid
    leaf6071InnerLogValid leaf6071CoversExact leaf6071LowerChecked

private noncomputable def leaf6072Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6072Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712105984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (728436973/536870912) }, upper := { exponent := 1, mantissa := (5647/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428502525/137424211968) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6072InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6072LocalValidity :
    LeafFacts leaf6072Box leaf6072Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6072Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712105984) }) = true
      norm_num [leaf6072Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6072CertificateValid :
    WideCertificateValid leaf6072Box leaf6072Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi271ValidityFacts
    leaf6072LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6072CoverageChecked :
    coverageCheck (innerAD leaf6072Box) leaf6072InnerLog = true := by
  rfl'

private theorem leaf6072InnerLogValid :
    leaf6072InnerLog.Valid 8 (innerAD leaf6072Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6072CoverageChecked

private noncomputable def leaf6072InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6072InputLogOnePlusV_eq :
    leaf6072InputLogOnePlusV = outerEnclosure 24
      (leaf6072Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6072RoundedFacts : LeafRoundedFacts 8
    leaf6072Certificate.logOnePlusV leaf6072InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6072InputLogOnePlusV_eq }

private noncomputable def leaf6072Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi271InputQChi innerPair353Input
    leaf6072InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6072LowerChecked :
    lowerCheck 24 leaf6072Box leaf6072Inputs = true := by
  rfl'

private theorem leaf6072CoversExact : CoversExact 8
    leaf6072Box leaf6072Certificate leaf6072InnerLog leaf6072Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi271RoundedFacts
    innerPair353RoundedFacts leaf6072RoundedFacts (by rfl)

private theorem leaf6072FlatSound : Sound leaf6072Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6072CertificateValid
    leaf6072InnerLogValid leaf6072CoversExact leaf6072LowerChecked

private noncomputable def leaf6073Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6073Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712048640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (732106765/536870912) }, upper := { exponent := 1, mantissa := (5675/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428445181/137424097280) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6073InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6073LocalValidity :
    LeafFacts leaf6073Box leaf6073Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6073Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712048640) }) = true
      norm_num [leaf6073Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6073CertificateValid :
    WideCertificateValid leaf6073Box leaf6073Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi272ValidityFacts
    leaf6073LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6073CoverageChecked :
    coverageCheck (innerAD leaf6073Box) leaf6073InnerLog = true := by
  rfl'

private theorem leaf6073InnerLogValid :
    leaf6073InnerLog.Valid 8 (innerAD leaf6073Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6073CoverageChecked

private noncomputable def leaf6073InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6073InputLogOnePlusV_eq :
    leaf6073InputLogOnePlusV = outerEnclosure 24
      (leaf6073Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6073RoundedFacts : LeafRoundedFacts 8
    leaf6073Certificate.logOnePlusV leaf6073InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6073InputLogOnePlusV_eq }

private noncomputable def leaf6073Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi272InputQChi innerPair353Input
    leaf6073InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6073LowerChecked :
    lowerCheck 24 leaf6073Box leaf6073Inputs = true := by
  rfl'

private theorem leaf6073CoversExact : CoversExact 8
    leaf6073Box leaf6073Certificate leaf6073InnerLog leaf6073Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi272RoundedFacts
    innerPair353RoundedFacts leaf6073RoundedFacts (by rfl)

private theorem leaf6073FlatSound : Sound leaf6073Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6073CertificateValid
    leaf6073InnerLogValid leaf6073CoversExact leaf6073LowerChecked

private noncomputable def leaf6074Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6074Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711985152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (736104215/536870912) }, upper := { exponent := 1, mantissa := (2853/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428381693/137423970304) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6074InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6074LocalValidity :
    LeafFacts leaf6074Box leaf6074Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6074Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711985152) }) = true
      norm_num [leaf6074Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6074CertificateValid :
    WideCertificateValid leaf6074Box leaf6074Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi272ValidityFacts
    leaf6074LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6074CoverageChecked :
    coverageCheck (innerAD leaf6074Box) leaf6074InnerLog = true := by
  rfl'

private theorem leaf6074InnerLogValid :
    leaf6074InnerLog.Valid 8 (innerAD leaf6074Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6074CoverageChecked

private noncomputable def leaf6074InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629619/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6074InputLogOnePlusV_eq :
    leaf6074InputLogOnePlusV = outerEnclosure 24
      (leaf6074Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6074RoundedFacts : LeafRoundedFacts 8
    leaf6074Certificate.logOnePlusV leaf6074InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6074InputLogOnePlusV_eq }

private noncomputable def leaf6074Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi272InputQChi innerPair353Input
    leaf6074InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6074LowerChecked :
    lowerCheck 24 leaf6074Box leaf6074Inputs = true := by
  rfl'

private theorem leaf6074CoversExact : CoversExact 8
    leaf6074Box leaf6074Certificate leaf6074InnerLog leaf6074Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi272RoundedFacts
    innerPair353RoundedFacts leaf6074RoundedFacts (by rfl)

private theorem leaf6074FlatSound : Sound leaf6074Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6074CertificateValid
    leaf6074InnerLogValid leaf6074CoversExact leaf6074LowerChecked

private noncomputable def leaf6075Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6075Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68712043520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (732368891/536870912) }, upper := { exponent := 1, mantissa := (11355/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428440061/137424087040) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6075InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6075LocalValidity :
    LeafFacts leaf6075Box leaf6075Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6075Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68712043520) }) = true
      norm_num [leaf6075Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6075CertificateValid :
    WideCertificateValid leaf6075Box leaf6075Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi271ValidityFacts
    leaf6075LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6075CoverageChecked :
    coverageCheck (innerAD leaf6075Box) leaf6075InnerLog = true := by
  rfl'

private theorem leaf6075InnerLogValid :
    leaf6075InnerLog.Valid 8 (innerAD leaf6075Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6075CoverageChecked

private noncomputable def leaf6075InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6075InputLogOnePlusV_eq :
    leaf6075InputLogOnePlusV = outerEnclosure 24
      (leaf6075Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6075RoundedFacts : LeafRoundedFacts 8
    leaf6075Certificate.logOnePlusV leaf6075InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6075InputLogOnePlusV_eq }

private noncomputable def leaf6075Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi271InputQChi innerPair353Input
    leaf6075InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6075LowerChecked :
    lowerCheck 24 leaf6075Box leaf6075Inputs = true := by
  rfl'

private theorem leaf6075CoversExact : CoversExact 8
    leaf6075Box leaf6075Certificate leaf6075InnerLog leaf6075Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi271RoundedFacts
    innerPair353RoundedFacts leaf6075RoundedFacts (by rfl)

private theorem leaf6075FlatSound : Sound leaf6075Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6075CertificateValid
    leaf6075InnerLogValid leaf6075CoversExact leaf6075LowerChecked

private noncomputable def leaf6076Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf6076Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711981056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (736300809/536870912) }, upper := { exponent := 1, mantissa := (1427/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428377597/137423962112) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6076InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6076LocalValidity :
    LeafFacts leaf6076Box leaf6076Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6076Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711981056) }) = true
      norm_num [leaf6076Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6076CertificateValid :
    WideCertificateValid leaf6076Box leaf6076Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi271ValidityFacts
    leaf6076LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6076CoverageChecked :
    coverageCheck (innerAD leaf6076Box) leaf6076InnerLog = true := by
  rfl'

private theorem leaf6076InnerLogValid :
    leaf6076InnerLog.Valid 8 (innerAD leaf6076Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6076CoverageChecked

private noncomputable def leaf6076InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907405/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6076InputLogOnePlusV_eq :
    leaf6076InputLogOnePlusV = outerEnclosure 24
      (leaf6076Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6076RoundedFacts : LeafRoundedFacts 8
    leaf6076Certificate.logOnePlusV leaf6076InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6076InputLogOnePlusV_eq }

private noncomputable def leaf6076Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi271InputQChi innerPair353Input
    leaf6076InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6076LowerChecked :
    lowerCheck 24 leaf6076Box leaf6076Inputs = true := by
  rfl'

private theorem leaf6076CoversExact : CoversExact 8
    leaf6076Box leaf6076Certificate leaf6076InnerLog leaf6076Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi271RoundedFacts
    innerPair353RoundedFacts leaf6076RoundedFacts (by rfl)

private theorem leaf6076FlatSound : Sound leaf6076Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6076CertificateValid
    leaf6076InnerLogValid leaf6076CoversExact leaf6076LowerChecked

private noncomputable def leaf6077Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6077Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711921664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (740101665/536870912) }, upper := { exponent := 1, mantissa := (5737/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428318205/137423843328) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6077InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6077LocalValidity :
    LeafFacts leaf6077Box leaf6077Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6077Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711921664) }) = true
      norm_num [leaf6077Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6077CertificateValid :
    WideCertificateValid leaf6077Box leaf6077Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi272ValidityFacts
    leaf6077LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6077CoverageChecked :
    coverageCheck (innerAD leaf6077Box) leaf6077InnerLog = true := by
  rfl'

private theorem leaf6077InnerLogValid :
    leaf6077InnerLog.Valid 8 (innerAD leaf6077Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6077CoverageChecked

private noncomputable def leaf6077InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629627/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6077InputLogOnePlusV_eq :
    leaf6077InputLogOnePlusV = outerEnclosure 24
      (leaf6077Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6077RoundedFacts : LeafRoundedFacts 8
    leaf6077Certificate.logOnePlusV leaf6077InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6077InputLogOnePlusV_eq }

private noncomputable def leaf6077Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi272InputQChi innerPair356Input
    leaf6077InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6077LowerChecked :
    lowerCheck 24 leaf6077Box leaf6077Inputs = true := by
  rfl'

private theorem leaf6077CoversExact : CoversExact 8
    leaf6077Box leaf6077Certificate leaf6077InnerLog leaf6077Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi272RoundedFacts
    innerPair356RoundedFacts leaf6077RoundedFacts (by rfl)

private theorem leaf6077FlatSound : Sound leaf6077Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6077CertificateValid
    leaf6077InnerLogValid leaf6077CoversExact leaf6077LowerChecked

private noncomputable def leaf6078Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf6078Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285527552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (744099115/536870912) }, upper := { exponent := 1, mantissa := (721/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571404209/10571055104) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6078InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6078LocalValidity :
    LeafFacts leaf6078Box leaf6078Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6078Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285527552) }) = true
      norm_num [leaf6078Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6078CertificateValid :
    WideCertificateValid leaf6078Box leaf6078Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi272ValidityFacts
    leaf6078LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6078CoverageChecked :
    coverageCheck (innerAD leaf6078Box) leaf6078InnerLog = true := by
  rfl'

private theorem leaf6078InnerLogValid :
    leaf6078InnerLog.Valid 8 (innerAD leaf6078Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6078CoverageChecked

private noncomputable def leaf6078InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6078InputLogOnePlusV_eq :
    leaf6078InputLogOnePlusV = outerEnclosure 24
      (leaf6078Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6078RoundedFacts : LeafRoundedFacts 8
    leaf6078Certificate.logOnePlusV leaf6078InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6078InputLogOnePlusV_eq }

private noncomputable def leaf6078Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi272InputQChi innerPair357Input
    leaf6078InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6078LowerChecked :
    lowerCheck 24 leaf6078Box leaf6078Inputs = true := by
  rfl'

private theorem leaf6078CoversExact : CoversExact 8
    leaf6078Box leaf6078Certificate leaf6078InnerLog leaf6078Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi272RoundedFacts
    innerPair357RoundedFacts leaf6078RoundedFacts (by rfl)

private theorem leaf6078FlatSound : Sound leaf6078Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6078CertificateValid
    leaf6078InnerLogValid leaf6078CoversExact leaf6078LowerChecked

private noncomputable def leaf6079Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6079Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711928832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (739708475/536870912) }, upper := { exponent := 1, mantissa := (11467/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428325373/137423857664) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6079InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6079LocalValidity :
    LeafFacts leaf6079Box leaf6079Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6079Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711928832) }) = true
      norm_num [leaf6079Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6079CertificateValid :
    WideCertificateValid leaf6079Box leaf6079Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi273ValidityFacts
    leaf6079LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6079CoverageChecked :
    coverageCheck (innerAD leaf6079Box) leaf6079InnerLog = true := by
  rfl'

private theorem leaf6079InnerLogValid :
    leaf6079InnerLog.Valid 8 (innerAD leaf6079Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6079CoverageChecked

private noncomputable def leaf6079InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814813/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6079InputLogOnePlusV_eq :
    leaf6079InputLogOnePlusV = outerEnclosure 24
      (leaf6079Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6079RoundedFacts : LeafRoundedFacts 8
    leaf6079Certificate.logOnePlusV leaf6079InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6079InputLogOnePlusV_eq }

private noncomputable def leaf6079Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi273InputQChi innerPair356Input
    leaf6079InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6079LowerChecked :
    lowerCheck 24 leaf6079Box leaf6079Inputs = true := by
  rfl'

private theorem leaf6079CoversExact : CoversExact 8
    leaf6079Box leaf6079Certificate leaf6079InnerLog leaf6079Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi273RoundedFacts
    innerPair356RoundedFacts leaf6079RoundedFacts (by rfl)

private theorem leaf6079FlatSound : Sound leaf6079Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6079CertificateValid
    leaf6079InnerLogValid leaf6079CoversExact leaf6079LowerChecked

private noncomputable def leaf6080Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6080Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711864320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (743771457/536870912) }, upper := { exponent := 1, mantissa := (5765/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428260861/137423728640) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6080InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6080LocalValidity :
    LeafFacts leaf6080Box leaf6080Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6080Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711864320) }) = true
      norm_num [leaf6080Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6080CertificateValid :
    WideCertificateValid leaf6080Box leaf6080Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi273ValidityFacts
    leaf6080LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6080CoverageChecked :
    coverageCheck (innerAD leaf6080Box) leaf6080InnerLog = true := by
  rfl'

private theorem leaf6080InnerLogValid :
    leaf6080InnerLog.Valid 8 (innerAD leaf6080Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6080CoverageChecked

private noncomputable def leaf6080InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814817/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6080InputLogOnePlusV_eq :
    leaf6080InputLogOnePlusV = outerEnclosure 24
      (leaf6080Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6080RoundedFacts : LeafRoundedFacts 8
    leaf6080Certificate.logOnePlusV leaf6080InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6080InputLogOnePlusV_eq }

private noncomputable def leaf6080Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi273InputQChi innerPair357Input
    leaf6080InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6080LowerChecked :
    lowerCheck 24 leaf6080Box leaf6080Inputs = true := by
  rfl'

private theorem leaf6080CoversExact : CoversExact 8
    leaf6080Box leaf6080Certificate leaf6080InnerLog leaf6080Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi273RoundedFacts
    innerPair357RoundedFacts leaf6080RoundedFacts (by rfl)

private theorem leaf6080FlatSound : Sound leaf6080Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6080CertificateValid
    leaf6080InnerLogValid leaf6080CoversExact leaf6080LowerChecked

private noncomputable def leaf6081Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6081Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711809024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (747310185/536870912) }, upper := { exponent := 1, mantissa := (181/128) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428205565/137423618048) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6081InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6081LocalValidity :
    LeafFacts leaf6081Box leaf6081Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6081Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711809024) }) = true
      norm_num [leaf6081Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6081CertificateValid :
    WideCertificateValid leaf6081Box leaf6081Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi274ValidityFacts
    leaf6081LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6081CoverageChecked :
    coverageCheck (innerAD leaf6081Box) leaf6081InnerLog = true := by
  rfl'

private theorem leaf6081InnerLogValid :
    leaf6081InnerLog.Valid 8 (innerAD leaf6081Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6081CoverageChecked

private noncomputable def leaf6081InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629641/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6081InputLogOnePlusV_eq :
    leaf6081InputLogOnePlusV = outerEnclosure 24
      (leaf6081Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6081RoundedFacts : LeafRoundedFacts 8
    leaf6081Certificate.logOnePlusV leaf6081InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6081InputLogOnePlusV_eq }

private noncomputable def leaf6081Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi274InputQChi innerPair357Input
    leaf6081InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6081LowerChecked :
    lowerCheck 24 leaf6081Box leaf6081Inputs = true := by
  rfl'

private theorem leaf6081CoversExact : CoversExact 8
    leaf6081Box leaf6081Certificate leaf6081InnerLog leaf6081Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi274RoundedFacts
    innerPair357RoundedFacts leaf6081RoundedFacts (by rfl)

private theorem leaf6081FlatSound : Sound leaf6081Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6081CertificateValid
    leaf6081InnerLogValid leaf6081CoversExact leaf6081LowerChecked

private noncomputable def leaf6082Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6082Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041867264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (751438699/536870912) }, upper := { exponent := 1, mantissa := (91/64) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084008237/8083734528) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6082InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6082LocalValidity :
    LeafFacts leaf6082Box leaf6082Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6082Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041867264) }) = true
      norm_num [leaf6082Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6082CertificateValid :
    WideCertificateValid leaf6082Box leaf6082Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi274ValidityFacts
    leaf6082LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6082CoverageChecked :
    coverageCheck (innerAD leaf6082Box) leaf6082InnerLog = true := by
  rfl'

private theorem leaf6082InnerLogValid :
    leaf6082InnerLog.Valid 8 (innerAD leaf6082Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6082CoverageChecked

private noncomputable def leaf6082InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6082InputLogOnePlusV_eq :
    leaf6082InputLogOnePlusV = outerEnclosure 24
      (leaf6082Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6082RoundedFacts : LeafRoundedFacts 8
    leaf6082Certificate.logOnePlusV leaf6082InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6082InputLogOnePlusV_eq }

private noncomputable def leaf6082Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi274InputQChi innerPair357Input
    leaf6082InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6082LowerChecked :
    lowerCheck 24 leaf6082Box leaf6082Inputs = true := by
  rfl'

private theorem leaf6082CoversExact : CoversExact 8
    leaf6082Box leaf6082Certificate leaf6082InnerLog leaf6082Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi274RoundedFacts
    innerPair357RoundedFacts leaf6082RoundedFacts (by rfl)

private theorem leaf6082FlatSound : Sound leaf6082Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6082CertificateValid
    leaf6082InnerLogValid leaf6082CoversExact leaf6082LowerChecked

private noncomputable def leaf6083Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6083Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711799808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (747834439/536870912) }, upper := { exponent := 1, mantissa := (11593/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428196349/137423599616) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6083InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6083LocalValidity :
    LeafFacts leaf6083Box leaf6083Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6083Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711799808) }) = true
      norm_num [leaf6083Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6083CertificateValid :
    WideCertificateValid leaf6083Box leaf6083Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi273ValidityFacts
    leaf6083LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6083CoverageChecked :
    coverageCheck (innerAD leaf6083Box) leaf6083InnerLog = true := by
  rfl'

private theorem leaf6083InnerLogValid :
    leaf6083InnerLog.Valid 8 (innerAD leaf6083Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6083CoverageChecked

private noncomputable def leaf6083InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814821/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6083InputLogOnePlusV_eq :
    leaf6083InputLogOnePlusV = outerEnclosure 24
      (leaf6083Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6083RoundedFacts : LeafRoundedFacts 8
    leaf6083Certificate.logOnePlusV leaf6083InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6083InputLogOnePlusV_eq }

private noncomputable def leaf6083Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi273InputQChi innerPair357Input
    leaf6083InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6083LowerChecked :
    lowerCheck 24 leaf6083Box leaf6083Inputs = true := by
  rfl'

private theorem leaf6083CoversExact : CoversExact 8
    leaf6083Box leaf6083Certificate leaf6083InnerLog leaf6083Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi273RoundedFacts
    innerPair357RoundedFacts leaf6083RoundedFacts (by rfl)

private theorem leaf6083FlatSound : Sound leaf6083Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6083CertificateValid
    leaf6083InnerLogValid leaf6083CoversExact leaf6083LowerChecked

private noncomputable def leaf6084Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf6084Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711735296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (751897421/536870912) }, upper := { exponent := 1, mantissa := (1457/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428131837/137423470592) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6084InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6084LocalValidity :
    LeafFacts leaf6084Box leaf6084Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6084Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711735296) }) = true
      norm_num [leaf6084Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6084CertificateValid :
    WideCertificateValid leaf6084Box leaf6084Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi273ValidityFacts
    leaf6084LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6084CoverageChecked :
    coverageCheck (innerAD leaf6084Box) leaf6084InnerLog = true := by
  rfl'

private theorem leaf6084InnerLogValid :
    leaf6084InnerLog.Valid 8 (innerAD leaf6084Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6084CoverageChecked

private noncomputable def leaf6084InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814825/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6084InputLogOnePlusV_eq :
    leaf6084InputLogOnePlusV = outerEnclosure 24
      (leaf6084Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6084RoundedFacts : LeafRoundedFacts 8
    leaf6084Certificate.logOnePlusV leaf6084InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6084InputLogOnePlusV_eq }

private noncomputable def leaf6084Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi273InputQChi innerPair357Input
    leaf6084InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6084LowerChecked :
    lowerCheck 24 leaf6084Box leaf6084Inputs = true := by
  rfl'

private theorem leaf6084CoversExact : CoversExact 8
    leaf6084Box leaf6084Certificate leaf6084InnerLog leaf6084Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi273RoundedFacts
    innerPair357RoundedFacts leaf6084RoundedFacts (by rfl)

private theorem leaf6084FlatSound : Sound leaf6084Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6084CertificateValid
    leaf6084InnerLogValid leaf6084CoversExact leaf6084LowerChecked

private noncomputable def leaf6085Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6085Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (967836571/967770112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (755567213/536870912) }, upper := { exponent := 1, mantissa := (183/128) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1935606683/1935540224) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6085InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6085LocalValidity :
    LeafFacts leaf6085Box leaf6085Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6085Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (967836571/967770112) }) = true
      norm_num [leaf6085Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6085CertificateValid :
    WideCertificateValid leaf6085Box leaf6085Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi274ValidityFacts
    leaf6085LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6085CoverageChecked :
    coverageCheck (innerAD leaf6085Box) leaf6085InnerLog = true := by
  rfl'

private theorem leaf6085InnerLogValid :
    leaf6085InnerLog.Valid 8 (innerAD leaf6085Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6085CoverageChecked

private noncomputable def leaf6085InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629657/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6085InputLogOnePlusV_eq :
    leaf6085InputLogOnePlusV = outerEnclosure 24
      (leaf6085Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6085RoundedFacts : LeafRoundedFacts 8
    leaf6085Certificate.logOnePlusV leaf6085InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6085InputLogOnePlusV_eq }

private noncomputable def leaf6085Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi274InputQChi innerPair367Input
    leaf6085InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6085LowerChecked :
    lowerCheck 24 leaf6085Box leaf6085Inputs = true := by
  rfl'

private theorem leaf6085CoversExact : CoversExact 8
    leaf6085Box leaf6085Certificate leaf6085InnerLog leaf6085Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi274RoundedFacts
    innerPair367RoundedFacts leaf6085RoundedFacts (by rfl)

private theorem leaf6085FlatSound : Sound leaf6085Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6085CertificateValid
    leaf6085InnerLogValid leaf6085CoversExact leaf6085LowerChecked

private noncomputable def leaf6086Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf6086Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711612416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (759695727/536870912) }, upper := { exponent := 1, mantissa := (23/16) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428008957/137423224832) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6086InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6086LocalValidity :
    LeafFacts leaf6086Box leaf6086Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6086Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711612416) }) = true
      norm_num [leaf6086Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6086CertificateValid :
    WideCertificateValid leaf6086Box leaf6086Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi274ValidityFacts
    leaf6086LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6086CoverageChecked :
    coverageCheck (innerAD leaf6086Box) leaf6086InnerLog = true := by
  rfl'

private theorem leaf6086InnerLogValid :
    leaf6086InnerLog.Valid 8 (innerAD leaf6086Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6086CoverageChecked

private noncomputable def leaf6086InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6086InputLogOnePlusV_eq :
    leaf6086InputLogOnePlusV = outerEnclosure 24
      (leaf6086Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6086RoundedFacts : LeafRoundedFacts 8
    leaf6086Certificate.logOnePlusV leaf6086InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6086InputLogOnePlusV_eq }

private noncomputable def leaf6086Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi274InputQChi innerPair367Input
    leaf6086InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6086LowerChecked :
    lowerCheck 24 leaf6086Box leaf6086Inputs = true := by
  rfl'

private theorem leaf6086CoversExact : CoversExact 8
    leaf6086Box leaf6086Certificate leaf6086InnerLog leaf6086Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi274RoundedFacts
    innerPair367RoundedFacts leaf6086RoundedFacts (by rfl)

private theorem leaf6086FlatSound : Sound leaf6086Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6086CertificateValid
    leaf6086InnerLogValid leaf6086CoversExact leaf6086LowerChecked

private noncomputable def component121Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node0_sound : Sound component121Node0Box :=
  sound_of_literal_split component121Node0Box leaf6023Box leaf6024Box
    .k (113/32) (by rfl) (by rfl)
    leaf6023FlatSound leaf6024FlatSound

private noncomputable def component121Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node1_sound : Sound component121Node1Box :=
  sound_of_literal_split component121Node1Box leaf6025Box leaf6026Box
    .k (113/32) (by rfl) (by rfl)
    leaf6025FlatSound leaf6026FlatSound

private noncomputable def component121Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node2_sound : Sound component121Node2Box :=
  sound_of_literal_split component121Node2Box component121Node0Box component121Node1Box
    .chi (57/128) (by rfl) (by rfl)
    component121Node0_sound component121Node1_sound

private noncomputable def component121Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node3_sound : Sound component121Node3Box :=
  sound_of_literal_split component121Node3Box leaf6027Box leaf6028Box
    .k (115/32) (by rfl) (by rfl)
    leaf6027FlatSound leaf6028FlatSound

private noncomputable def component121Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node4_sound : Sound component121Node4Box :=
  sound_of_literal_split component121Node4Box leaf6029Box leaf6030Box
    .k (115/32) (by rfl) (by rfl)
    leaf6029FlatSound leaf6030FlatSound

private noncomputable def component121Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node5_sound : Sound component121Node5Box :=
  sound_of_literal_split component121Node5Box component121Node3Box component121Node4Box
    .chi (57/128) (by rfl) (by rfl)
    component121Node3_sound component121Node4_sound

private noncomputable def component121Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node6_sound : Sound component121Node6Box :=
  sound_of_literal_split component121Node6Box component121Node2Box component121Node5Box
    .k (57/16) (by rfl) (by rfl)
    component121Node2_sound component121Node5_sound

private noncomputable def component121Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node7_sound : Sound component121Node7Box :=
  sound_of_literal_split component121Node7Box leaf6031Box leaf6032Box
    .k (113/32) (by rfl) (by rfl)
    leaf6031FlatSound leaf6032FlatSound

private noncomputable def component121Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node8_sound : Sound component121Node8Box :=
  sound_of_literal_split component121Node8Box leaf6033Box leaf6034Box
    .k (113/32) (by rfl) (by rfl)
    leaf6033FlatSound leaf6034FlatSound

private noncomputable def component121Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node9_sound : Sound component121Node9Box :=
  sound_of_literal_split component121Node9Box component121Node7Box component121Node8Box
    .chi (59/128) (by rfl) (by rfl)
    component121Node7_sound component121Node8_sound

private noncomputable def component121Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node10_sound : Sound component121Node10Box :=
  sound_of_literal_split component121Node10Box leaf6035Box leaf6036Box
    .k (115/32) (by rfl) (by rfl)
    leaf6035FlatSound leaf6036FlatSound

private noncomputable def component121Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node11_sound : Sound component121Node11Box :=
  sound_of_literal_split component121Node11Box leaf6037Box leaf6038Box
    .k (115/32) (by rfl) (by rfl)
    leaf6037FlatSound leaf6038FlatSound

private noncomputable def component121Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node12_sound : Sound component121Node12Box :=
  sound_of_literal_split component121Node12Box component121Node10Box component121Node11Box
    .chi (59/128) (by rfl) (by rfl)
    component121Node10_sound component121Node11_sound

private noncomputable def component121Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node13_sound : Sound component121Node13Box :=
  sound_of_literal_split component121Node13Box component121Node9Box component121Node12Box
    .k (57/16) (by rfl) (by rfl)
    component121Node9_sound component121Node12_sound

private noncomputable def component121Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node14_sound : Sound component121Node14Box :=
  sound_of_literal_split component121Node14Box component121Node6Box component121Node13Box
    .chi (29/64) (by rfl) (by rfl)
    component121Node6_sound component121Node13_sound

private noncomputable def component121Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node15_sound : Sound component121Node15Box :=
  sound_of_literal_split component121Node15Box leaf6039Box leaf6040Box
    .k (117/32) (by rfl) (by rfl)
    leaf6039FlatSound leaf6040FlatSound

private noncomputable def component121Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node16_sound : Sound component121Node16Box :=
  sound_of_literal_split component121Node16Box leaf6041Box leaf6042Box
    .k (117/32) (by rfl) (by rfl)
    leaf6041FlatSound leaf6042FlatSound

private noncomputable def component121Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node17_sound : Sound component121Node17Box :=
  sound_of_literal_split component121Node17Box component121Node15Box component121Node16Box
    .chi (57/128) (by rfl) (by rfl)
    component121Node15_sound component121Node16_sound

private noncomputable def component121Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node18_sound : Sound component121Node18Box :=
  sound_of_literal_split component121Node18Box leaf6043Box leaf6044Box
    .k (119/32) (by rfl) (by rfl)
    leaf6043FlatSound leaf6044FlatSound

private noncomputable def component121Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node19_sound : Sound component121Node19Box :=
  sound_of_literal_split component121Node19Box leaf6045Box leaf6046Box
    .k (119/32) (by rfl) (by rfl)
    leaf6045FlatSound leaf6046FlatSound

private noncomputable def component121Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node20_sound : Sound component121Node20Box :=
  sound_of_literal_split component121Node20Box component121Node18Box component121Node19Box
    .chi (57/128) (by rfl) (by rfl)
    component121Node18_sound component121Node19_sound

private noncomputable def component121Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node21_sound : Sound component121Node21Box :=
  sound_of_literal_split component121Node21Box component121Node17Box component121Node20Box
    .k (59/16) (by rfl) (by rfl)
    component121Node17_sound component121Node20_sound

private noncomputable def component121Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node22_sound : Sound component121Node22Box :=
  sound_of_literal_split component121Node22Box leaf6047Box leaf6048Box
    .k (117/32) (by rfl) (by rfl)
    leaf6047FlatSound leaf6048FlatSound

private noncomputable def component121Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node23_sound : Sound component121Node23Box :=
  sound_of_literal_split component121Node23Box leaf6049Box leaf6050Box
    .k (117/32) (by rfl) (by rfl)
    leaf6049FlatSound leaf6050FlatSound

private noncomputable def component121Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node24_sound : Sound component121Node24Box :=
  sound_of_literal_split component121Node24Box component121Node22Box component121Node23Box
    .chi (59/128) (by rfl) (by rfl)
    component121Node22_sound component121Node23_sound

private noncomputable def component121Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node25_sound : Sound component121Node25Box :=
  sound_of_literal_split component121Node25Box leaf6051Box leaf6052Box
    .k (119/32) (by rfl) (by rfl)
    leaf6051FlatSound leaf6052FlatSound

private noncomputable def component121Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (59/128), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node26_sound : Sound component121Node26Box :=
  sound_of_literal_split component121Node26Box leaf6053Box leaf6054Box
    .k (119/32) (by rfl) (by rfl)
    leaf6053FlatSound leaf6054FlatSound

private noncomputable def component121Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node27_sound : Sound component121Node27Box :=
  sound_of_literal_split component121Node27Box component121Node25Box component121Node26Box
    .chi (59/128) (by rfl) (by rfl)
    component121Node25_sound component121Node26_sound

private noncomputable def component121Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node28_sound : Sound component121Node28Box :=
  sound_of_literal_split component121Node28Box component121Node24Box component121Node27Box
    .k (59/16) (by rfl) (by rfl)
    component121Node24_sound component121Node27_sound

private noncomputable def component121Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node29_sound : Sound component121Node29Box :=
  sound_of_literal_split component121Node29Box component121Node21Box component121Node28Box
    .chi (29/64) (by rfl) (by rfl)
    component121Node21_sound component121Node28_sound

private noncomputable def component121Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component121Node30_sound : Sound component121Node30Box :=
  sound_of_literal_split component121Node30Box component121Node14Box component121Node29Box
    .k (29/8) (by rfl) (by rfl)
    component121Node14_sound component121Node29_sound

private noncomputable def component121Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node31_sound : Sound component121Node31Box :=
  sound_of_literal_split component121Node31Box leaf6055Box leaf6056Box
    .k (113/32) (by rfl) (by rfl)
    leaf6055FlatSound leaf6056FlatSound

private noncomputable def component121Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node32_sound : Sound component121Node32Box :=
  sound_of_literal_split component121Node32Box leaf6057Box leaf6058Box
    .k (113/32) (by rfl) (by rfl)
    leaf6057FlatSound leaf6058FlatSound

private noncomputable def component121Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node33_sound : Sound component121Node33Box :=
  sound_of_literal_split component121Node33Box component121Node31Box component121Node32Box
    .chi (61/128) (by rfl) (by rfl)
    component121Node31_sound component121Node32_sound

private noncomputable def component121Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node34_sound : Sound component121Node34Box :=
  sound_of_literal_split component121Node34Box leaf6059Box leaf6060Box
    .k (115/32) (by rfl) (by rfl)
    leaf6059FlatSound leaf6060FlatSound

private noncomputable def component121Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node35_sound : Sound component121Node35Box :=
  sound_of_literal_split component121Node35Box leaf6061Box leaf6062Box
    .k (115/32) (by rfl) (by rfl)
    leaf6061FlatSound leaf6062FlatSound

private noncomputable def component121Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node36_sound : Sound component121Node36Box :=
  sound_of_literal_split component121Node36Box component121Node34Box component121Node35Box
    .chi (61/128) (by rfl) (by rfl)
    component121Node34_sound component121Node35_sound

private noncomputable def component121Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node37_sound : Sound component121Node37Box :=
  sound_of_literal_split component121Node37Box component121Node33Box component121Node36Box
    .k (57/16) (by rfl) (by rfl)
    component121Node33_sound component121Node36_sound

private noncomputable def component121Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node38_sound : Sound component121Node38Box :=
  sound_of_literal_split component121Node38Box leaf6063Box leaf6064Box
    .k (113/32) (by rfl) (by rfl)
    leaf6063FlatSound leaf6064FlatSound

private noncomputable def component121Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node39_sound : Sound component121Node39Box :=
  sound_of_literal_split component121Node39Box leaf6065Box leaf6066Box
    .k (113/32) (by rfl) (by rfl)
    leaf6065FlatSound leaf6066FlatSound

private noncomputable def component121Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node40_sound : Sound component121Node40Box :=
  sound_of_literal_split component121Node40Box component121Node38Box component121Node39Box
    .chi (63/128) (by rfl) (by rfl)
    component121Node38_sound component121Node39_sound

private noncomputable def component121Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node41_sound : Sound component121Node41Box :=
  sound_of_literal_split component121Node41Box leaf6067Box leaf6068Box
    .k (115/32) (by rfl) (by rfl)
    leaf6067FlatSound leaf6068FlatSound

private noncomputable def component121Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node42_sound : Sound component121Node42Box :=
  sound_of_literal_split component121Node42Box leaf6069Box leaf6070Box
    .k (115/32) (by rfl) (by rfl)
    leaf6069FlatSound leaf6070FlatSound

private noncomputable def component121Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node43_sound : Sound component121Node43Box :=
  sound_of_literal_split component121Node43Box component121Node41Box component121Node42Box
    .chi (63/128) (by rfl) (by rfl)
    component121Node41_sound component121Node42_sound

private noncomputable def component121Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node44_sound : Sound component121Node44Box :=
  sound_of_literal_split component121Node44Box component121Node40Box component121Node43Box
    .k (57/16) (by rfl) (by rfl)
    component121Node40_sound component121Node43_sound

private noncomputable def component121Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node45_sound : Sound component121Node45Box :=
  sound_of_literal_split component121Node45Box component121Node37Box component121Node44Box
    .chi (31/64) (by rfl) (by rfl)
    component121Node37_sound component121Node44_sound

private noncomputable def component121Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node46_sound : Sound component121Node46Box :=
  sound_of_literal_split component121Node46Box leaf6071Box leaf6072Box
    .k (117/32) (by rfl) (by rfl)
    leaf6071FlatSound leaf6072FlatSound

private noncomputable def component121Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node47_sound : Sound component121Node47Box :=
  sound_of_literal_split component121Node47Box leaf6073Box leaf6074Box
    .k (117/32) (by rfl) (by rfl)
    leaf6073FlatSound leaf6074FlatSound

private noncomputable def component121Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node48_sound : Sound component121Node48Box :=
  sound_of_literal_split component121Node48Box component121Node46Box component121Node47Box
    .chi (61/128) (by rfl) (by rfl)
    component121Node46_sound component121Node47_sound

private noncomputable def component121Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/32), chiHi := (61/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node49_sound : Sound component121Node49Box :=
  sound_of_literal_split component121Node49Box leaf6075Box leaf6076Box
    .k (119/32) (by rfl) (by rfl)
    leaf6075FlatSound leaf6076FlatSound

private noncomputable def component121Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (61/128), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node50_sound : Sound component121Node50Box :=
  sound_of_literal_split component121Node50Box leaf6077Box leaf6078Box
    .k (119/32) (by rfl) (by rfl)
    leaf6077FlatSound leaf6078FlatSound

private noncomputable def component121Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node51_sound : Sound component121Node51Box :=
  sound_of_literal_split component121Node51Box component121Node49Box component121Node50Box
    .chi (61/128) (by rfl) (by rfl)
    component121Node49_sound component121Node50_sound

private noncomputable def component121Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component121Node52_sound : Sound component121Node52Box :=
  sound_of_literal_split component121Node52Box component121Node48Box component121Node51Box
    .k (59/16) (by rfl) (by rfl)
    component121Node48_sound component121Node51_sound

private noncomputable def component121Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node53_sound : Sound component121Node53Box :=
  sound_of_literal_split component121Node53Box leaf6079Box leaf6080Box
    .k (117/32) (by rfl) (by rfl)
    leaf6079FlatSound leaf6080FlatSound

private noncomputable def component121Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node54_sound : Sound component121Node54Box :=
  sound_of_literal_split component121Node54Box leaf6081Box leaf6082Box
    .k (117/32) (by rfl) (by rfl)
    leaf6081FlatSound leaf6082FlatSound

private noncomputable def component121Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node55_sound : Sound component121Node55Box :=
  sound_of_literal_split component121Node55Box component121Node53Box component121Node54Box
    .chi (63/128) (by rfl) (by rfl)
    component121Node53_sound component121Node54_sound

private noncomputable def component121Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (31/64), chiHi := (63/128) }

set_option maxRecDepth 1000000 in
private theorem component121Node56_sound : Sound component121Node56Box :=
  sound_of_literal_split component121Node56Box leaf6083Box leaf6084Box
    .k (119/32) (by rfl) (by rfl)
    leaf6083FlatSound leaf6084FlatSound

private noncomputable def component121Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (63/128), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node57_sound : Sound component121Node57Box :=
  sound_of_literal_split component121Node57Box leaf6085Box leaf6086Box
    .k (119/32) (by rfl) (by rfl)
    leaf6085FlatSound leaf6086FlatSound

private noncomputable def component121Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node58_sound : Sound component121Node58Box :=
  sound_of_literal_split component121Node58Box component121Node56Box component121Node57Box
    .chi (63/128) (by rfl) (by rfl)
    component121Node56_sound component121Node57_sound

private noncomputable def component121Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node59_sound : Sound component121Node59Box :=
  sound_of_literal_split component121Node59Box component121Node55Box component121Node58Box
    .k (59/16) (by rfl) (by rfl)
    component121Node55_sound component121Node58_sound

private noncomputable def component121Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node60_sound : Sound component121Node60Box :=
  sound_of_literal_split component121Node60Box component121Node52Box component121Node59Box
    .chi (31/64) (by rfl) (by rfl)
    component121Node52_sound component121Node59_sound

private noncomputable def component121Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component121Node61_sound : Sound component121Node61Box :=
  sound_of_literal_split component121Node61Box component121Node45Box component121Node60Box
    .k (29/8) (by rfl) (by rfl)
    component121Node45_sound component121Node60_sound

noncomputable def component121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component121_sound : Sound component121Box :=
  sound_of_literal_split component121Box component121Node30Box component121Node61Box
    .chi (15/32) (by rfl) (by rfl)
    component121Node30_sound component121Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
