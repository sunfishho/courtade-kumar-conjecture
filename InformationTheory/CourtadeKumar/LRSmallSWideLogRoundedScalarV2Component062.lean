import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf2946Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2946Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433726464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1723785919/1073741824) }, upper := { exponent := 0, mantissa := (26593/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870648319/274867452928) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2946InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2946LocalValidity :
    LeafFacts leaf2946Box leaf2946Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2946Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433726464) }) = true
      norm_num [leaf2946Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2946CertificateValid :
    WideCertificateValid leaf2946Box leaf2946Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi183ValidityFacts
    leaf2946LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2946CoverageChecked :
    coverageCheck (innerAD leaf2946Box) leaf2946InnerLog = true := by
  rfl'

private theorem leaf2946InnerLogValid :
    leaf2946InnerLog.Valid 8 (innerAD leaf2946Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2946CoverageChecked

private noncomputable def leaf2946InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2946InputLogOnePlusV_eq :
    leaf2946InputLogOnePlusV = outerEnclosure 24
      (leaf2946Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2946RoundedFacts : LeafRoundedFacts 8
    leaf2946Certificate.logOnePlusV leaf2946InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2946InputLogOnePlusV_eq }

private noncomputable def leaf2946Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2946InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2946LowerChecked :
    lowerCheck 24 leaf2946Box leaf2946Inputs = true := by
  rfl'

private theorem leaf2946CoversExact : CoversExact 8
    leaf2946Box leaf2946Certificate leaf2946InnerLog leaf2946Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2946RoundedFacts (by rfl)

private theorem leaf2946FlatSound : Sound leaf2946Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2946CertificateValid
    leaf2946InnerLogValid leaf2946CoversExact leaf2946LowerChecked

private noncomputable def leaf2947Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2947Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084335616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1726407197/1073741824) }, upper := { exponent := 0, mantissa := (13317/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168860431/16168671232) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2947InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf2947LocalValidity :
    LeafFacts leaf2947Box leaf2947Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2947Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084335616) }) = true
      norm_num [leaf2947Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2947CertificateValid :
    WideCertificateValid leaf2947Box leaf2947Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi183ValidityFacts
    leaf2947LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2947CoverageChecked :
    coverageCheck (innerAD leaf2947Box) leaf2947InnerLog = true := by
  rfl'

private theorem leaf2947InnerLogValid :
    leaf2947InnerLog.Valid 8 (innerAD leaf2947Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf2947CoverageChecked

private noncomputable def leaf2947InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2947InputLogOnePlusV_eq :
    leaf2947InputLogOnePlusV = outerEnclosure 24
      (leaf2947Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2947RoundedFacts : LeafRoundedFacts 8
    leaf2947Certificate.logOnePlusV leaf2947InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2947InputLogOnePlusV_eq }

private noncomputable def leaf2947Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi183InputQChi innerPair157Input
    leaf2947InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2947LowerChecked :
    lowerCheck 24 leaf2947Box leaf2947Inputs = true := by
  rfl'

private theorem leaf2947CoversExact : CoversExact 8
    leaf2947Box leaf2947Certificate leaf2947InnerLog leaf2947Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi183RoundedFacts
    innerPair157RoundedFacts leaf2947RoundedFacts (by rfl)

private theorem leaf2947FlatSound : Sound leaf2947Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2947CertificateValid
    leaf2947InnerLogValid leaf2947CoversExact leaf2947LowerChecked

private noncomputable def leaf2948Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2948Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433598976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1740037853/1073741824) }, upper := { exponent := 0, mantissa := (13421/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870520831/274867197952) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2948InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2948LocalValidity :
    LeafFacts leaf2948Box leaf2948Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2948Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433598976) }) = true
      norm_num [leaf2948Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2948CertificateValid :
    WideCertificateValid leaf2948Box leaf2948Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi184ValidityFacts
    leaf2948LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2948CoverageChecked :
    coverageCheck (innerAD leaf2948Box) leaf2948InnerLog = true := by
  rfl'

private theorem leaf2948InnerLogValid :
    leaf2948InnerLog.Valid 8 (innerAD leaf2948Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2948CoverageChecked

private noncomputable def leaf2948InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2948InputLogOnePlusV_eq :
    leaf2948InputLogOnePlusV = outerEnclosure 24
      (leaf2948Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2948RoundedFacts : LeafRoundedFacts 8
    leaf2948Certificate.logOnePlusV leaf2948InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2948InputLogOnePlusV_eq }

private noncomputable def leaf2948Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi184InputQChi innerPair166Input
    leaf2948InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2948LowerChecked :
    lowerCheck 24 leaf2948Box leaf2948Inputs = true := by
  rfl'

private theorem leaf2948CoversExact : CoversExact 8
    leaf2948Box leaf2948Certificate leaf2948InnerLog leaf2948Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi184RoundedFacts
    innerPair166RoundedFacts leaf2948RoundedFacts (by rfl)

private theorem leaf2948FlatSound : Sound leaf2948Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2948CertificateValid
    leaf2948InnerLogValid leaf2948CoversExact leaf2948LowerChecked

private noncomputable def leaf2949Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2949Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433577472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1742724663/1073741824) }, upper := { exponent := 0, mantissa := (6721/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870499327/274867154944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2949InnerLog : WideLogData :=
  innerPair188Data

set_option maxRecDepth 1000000 in
private theorem leaf2949LocalValidity :
    LeafFacts leaf2949Box leaf2949Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2949Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433577472) }) = true
      norm_num [leaf2949Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2949CertificateValid :
    WideCertificateValid leaf2949Box leaf2949Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi184ValidityFacts
    leaf2949LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2949CoverageChecked :
    coverageCheck (innerAD leaf2949Box) leaf2949InnerLog = true := by
  rfl'

private theorem leaf2949InnerLogValid :
    leaf2949InnerLog.Valid 8 (innerAD leaf2949Box) :=
  wideLogDataValid_of_cachedCheck endpoint55PositiveFacts
    endpoint171PositiveFacts.valid leaf2949CoverageChecked

private noncomputable def leaf2949InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2949InputLogOnePlusV_eq :
    leaf2949InputLogOnePlusV = outerEnclosure 24
      (leaf2949Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2949RoundedFacts : LeafRoundedFacts 8
    leaf2949Certificate.logOnePlusV leaf2949InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2949InputLogOnePlusV_eq }

private noncomputable def leaf2949Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi184InputQChi innerPair188Input
    leaf2949InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2949LowerChecked :
    lowerCheck 24 leaf2949Box leaf2949Inputs = true := by
  rfl'

private theorem leaf2949CoversExact : CoversExact 8
    leaf2949Box leaf2949Certificate leaf2949InnerLog leaf2949Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi184RoundedFacts
    innerPair188RoundedFacts leaf2949RoundedFacts (by rfl)

private theorem leaf2949FlatSound : Sound leaf2949Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2949CertificateValid
    leaf2949InnerLogValid leaf2949CoversExact leaf2949LowerChecked

private noncomputable def leaf2950Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2950Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162245632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1729028475/1073741824) }, upper := { exponent := 0, mantissa := (26675/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324707089/18324491264) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2950InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2950LocalValidity :
    LeafFacts leaf2950Box leaf2950Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2950Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162245632) }) = true
      norm_num [leaf2950Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2950CertificateValid :
    WideCertificateValid leaf2950Box leaf2950Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi183ValidityFacts
    leaf2950LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2950CoverageChecked :
    coverageCheck (innerAD leaf2950Box) leaf2950InnerLog = true := by
  rfl'

private theorem leaf2950InnerLogValid :
    leaf2950InnerLog.Valid 8 (innerAD leaf2950Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2950CoverageChecked

private noncomputable def leaf2950InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2950InputLogOnePlusV_eq :
    leaf2950InputLogOnePlusV = outerEnclosure 24
      (leaf2950Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2950RoundedFacts : LeafRoundedFacts 8
    leaf2950Certificate.logOnePlusV leaf2950InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2950InputLogOnePlusV_eq }

private noncomputable def leaf2950Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi183InputQChi innerPair166Input
    leaf2950InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2950LowerChecked :
    lowerCheck 24 leaf2950Box leaf2950Inputs = true := by
  rfl'

private theorem leaf2950CoversExact : CoversExact 8
    leaf2950Box leaf2950Certificate leaf2950InnerLog leaf2950Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi183RoundedFacts
    innerPair166RoundedFacts leaf2950RoundedFacts (by rfl)

private theorem leaf2950FlatSound : Sound leaf2950Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2950CertificateValid
    leaf2950InnerLogValid leaf2950CoversExact leaf2950LowerChecked

private noncomputable def leaf2951Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2951Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433663488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1731649753/1073741824) }, upper := { exponent := 0, mantissa := (6679/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870585343/274867326976) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2951InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2951LocalValidity :
    LeafFacts leaf2951Box leaf2951Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2951Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433663488) }) = true
      norm_num [leaf2951Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2951CertificateValid :
    WideCertificateValid leaf2951Box leaf2951Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi183ValidityFacts
    leaf2951LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2951CoverageChecked :
    coverageCheck (innerAD leaf2951Box) leaf2951InnerLog = true := by
  rfl'

private theorem leaf2951InnerLogValid :
    leaf2951InnerLog.Valid 8 (innerAD leaf2951Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2951CoverageChecked

private noncomputable def leaf2951InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2951InputLogOnePlusV_eq :
    leaf2951InputLogOnePlusV = outerEnclosure 24
      (leaf2951Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2951RoundedFacts : LeafRoundedFacts 8
    leaf2951Certificate.logOnePlusV leaf2951InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2951InputLogOnePlusV_eq }

private noncomputable def leaf2951Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi183InputQChi innerPair166Input
    leaf2951InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2951LowerChecked :
    lowerCheck 24 leaf2951Box leaf2951Inputs = true := by
  rfl'

private theorem leaf2951CoversExact : CoversExact 8
    leaf2951Box leaf2951Certificate leaf2951InnerLog leaf2951Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi183RoundedFacts
    innerPair166RoundedFacts leaf2951RoundedFacts (by rfl)

private theorem leaf2951FlatSound : Sound leaf2951Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2951CertificateValid
    leaf2951InnerLogValid leaf2951CoversExact leaf2951LowerChecked

private noncomputable def leaf2952Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2952Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433555968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1745411473/1073741824) }, upper := { exponent := 0, mantissa := (13463/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870477823/274867111936) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2952InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2952LocalValidity :
    LeafFacts leaf2952Box leaf2952Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2952Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433555968) }) = true
      norm_num [leaf2952Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2952CertificateValid :
    WideCertificateValid leaf2952Box leaf2952Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi184ValidityFacts
    leaf2952LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2952CoverageChecked :
    coverageCheck (innerAD leaf2952Box) leaf2952InnerLog = true := by
  rfl'

private theorem leaf2952InnerLogValid :
    leaf2952InnerLog.Valid 8 (innerAD leaf2952Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2952CoverageChecked

private noncomputable def leaf2952InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2952InputLogOnePlusV_eq :
    leaf2952InputLogOnePlusV = outerEnclosure 24
      (leaf2952Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2952RoundedFacts : LeafRoundedFacts 8
    leaf2952Certificate.logOnePlusV leaf2952InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2952InputLogOnePlusV_eq }

private noncomputable def leaf2952Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi184InputQChi innerPair61Input
    leaf2952InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2952LowerChecked :
    lowerCheck 24 leaf2952Box leaf2952Inputs = true := by
  rfl'

private theorem leaf2952CoversExact : CoversExact 8
    leaf2952Box leaf2952Certificate leaf2952InnerLog leaf2952Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi184RoundedFacts
    innerPair61RoundedFacts leaf2952RoundedFacts (by rfl)

private theorem leaf2952FlatSound : Sound leaf2952Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2952CertificateValid
    leaf2952InnerLogValid leaf2952CoversExact leaf2952LowerChecked

private noncomputable def leaf2953Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2953Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433534464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1748098283/1073741824) }, upper := { exponent := 0, mantissa := (3371/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870456319/274867068928) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2953InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2953LocalValidity :
    LeafFacts leaf2953Box leaf2953Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2953Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433534464) }) = true
      norm_num [leaf2953Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2953CertificateValid :
    WideCertificateValid leaf2953Box leaf2953Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi184ValidityFacts
    leaf2953LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2953CoverageChecked :
    coverageCheck (innerAD leaf2953Box) leaf2953InnerLog = true := by
  rfl'

private theorem leaf2953InnerLogValid :
    leaf2953InnerLog.Valid 8 (innerAD leaf2953Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2953CoverageChecked

private noncomputable def leaf2953InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2953InputLogOnePlusV_eq :
    leaf2953InputLogOnePlusV = outerEnclosure 24
      (leaf2953Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2953RoundedFacts : LeafRoundedFacts 8
    leaf2953Certificate.logOnePlusV leaf2953InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2953InputLogOnePlusV_eq }

private noncomputable def leaf2953Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi184InputQChi innerPair61Input
    leaf2953InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2953LowerChecked :
    lowerCheck 24 leaf2953Box leaf2953Inputs = true := by
  rfl'

private theorem leaf2953CoversExact : CoversExact 8
    leaf2953Box leaf2953Certificate leaf2953InnerLog leaf2953Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi184RoundedFacts
    innerPair61RoundedFacts leaf2953RoundedFacts (by rfl)

private theorem leaf2953FlatSound : Sound leaf2953Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2953CertificateValid
    leaf2953InnerLogValid leaf2953CoversExact leaf2953LowerChecked

private noncomputable def leaf2954Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2954Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433471488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1756289787/1073741824) }, upper := { exponent := 0, mantissa := (27091/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870393343/274866942976) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2954InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2954LocalValidity :
    LeafFacts leaf2954Box leaf2954Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2954Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433471488) }) = true
      norm_num [leaf2954Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2954CertificateValid :
    WideCertificateValid leaf2954Box leaf2954Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi185ValidityFacts
    leaf2954LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2954CoverageChecked :
    coverageCheck (innerAD leaf2954Box) leaf2954InnerLog = true := by
  rfl'

private theorem leaf2954InnerLogValid :
    leaf2954InnerLog.Valid 8 (innerAD leaf2954Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2954CoverageChecked

private noncomputable def leaf2954InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2954InputLogOnePlusV_eq :
    leaf2954InputLogOnePlusV = outerEnclosure 24
      (leaf2954Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2954RoundedFacts : LeafRoundedFacts 8
    leaf2954Certificate.logOnePlusV leaf2954InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2954InputLogOnePlusV_eq }

private noncomputable def leaf2954Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi185InputQChi innerPair61Input
    leaf2954InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2954LowerChecked :
    lowerCheck 24 leaf2954Box leaf2954Inputs = true := by
  rfl'

private theorem leaf2954CoversExact : CoversExact 8
    leaf2954Box leaf2954Certificate leaf2954InnerLog leaf2954Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi185RoundedFacts
    innerPair61RoundedFacts leaf2954RoundedFacts (by rfl)

private theorem leaf2954FlatSound : Sound leaf2954Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2954CertificateValid
    leaf2954InnerLogValid leaf2954CoversExact leaf2954LowerChecked

private noncomputable def leaf2955Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2955Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811149824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1759042129/1073741824) }, upper := { exponent := 0, mantissa := (13567/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623457109/91622299648) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2955InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2955LocalValidity :
    LeafFacts leaf2955Box leaf2955Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2955Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811149824) }) = true
      norm_num [leaf2955Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2955CertificateValid :
    WideCertificateValid leaf2955Box leaf2955Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi185ValidityFacts
    leaf2955LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2955CoverageChecked :
    coverageCheck (innerAD leaf2955Box) leaf2955InnerLog = true := by
  rfl'

private theorem leaf2955InnerLogValid :
    leaf2955InnerLog.Valid 8 (innerAD leaf2955Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2955CoverageChecked

private noncomputable def leaf2955InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2955InputLogOnePlusV_eq :
    leaf2955InputLogOnePlusV = outerEnclosure 24
      (leaf2955Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2955RoundedFacts : LeafRoundedFacts 8
    leaf2955Certificate.logOnePlusV leaf2955InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2955InputLogOnePlusV_eq }

private noncomputable def leaf2955Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi185InputQChi innerPair61Input
    leaf2955InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2955LowerChecked :
    lowerCheck 24 leaf2955Box leaf2955Inputs = true := by
  rfl'

private theorem leaf2955CoversExact : CoversExact 8
    leaf2955Box leaf2955Certificate leaf2955InnerLog leaf2955Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi185RoundedFacts
    innerPair61RoundedFacts leaf2955RoundedFacts (by rfl)

private theorem leaf2955FlatSound : Sound leaf2955Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2955CertificateValid
    leaf2955InnerLogValid leaf2955CoversExact leaf2955LowerChecked

private noncomputable def leaf2956Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2956Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486668800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1772541721/1073741824) }, upper := { exponent := 0, mantissa := (6835/4096) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974053171/54973337600) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2956InnerLog : WideLogData :=
  innerPair163Data

set_option maxRecDepth 1000000 in
private theorem leaf2956LocalValidity :
    LeafFacts leaf2956Box leaf2956Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2956Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486668800) }) = true
      norm_num [leaf2956Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2956CertificateValid :
    WideCertificateValid leaf2956Box leaf2956Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi186ValidityFacts
    leaf2956LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2956CoverageChecked :
    coverageCheck (innerAD leaf2956Box) leaf2956InnerLog = true := by
  rfl'

private theorem leaf2956InnerLogValid :
    leaf2956InnerLog.Valid 8 (innerAD leaf2956Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint133PositiveFacts.valid leaf2956CoverageChecked

private noncomputable def leaf2956InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2956InputLogOnePlusV_eq :
    leaf2956InputLogOnePlusV = outerEnclosure 24
      (leaf2956Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2956RoundedFacts : LeafRoundedFacts 8
    leaf2956Certificate.logOnePlusV leaf2956InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2956InputLogOnePlusV_eq }

private noncomputable def leaf2956Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi186InputQChi innerPair163Input
    leaf2956InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2956LowerChecked :
    lowerCheck 24 leaf2956Box leaf2956Inputs = true := by
  rfl'

private theorem leaf2956CoversExact : CoversExact 8
    leaf2956Box leaf2956Certificate leaf2956InnerLog leaf2956Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi186RoundedFacts
    innerPair163RoundedFacts leaf2956RoundedFacts (by rfl)

private theorem leaf2956FlatSound : Sound leaf2956Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2956CertificateValid
    leaf2956InnerLogValid leaf2956CoversExact leaf2956LowerChecked

private noncomputable def leaf2957Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2957Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433321472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1775359595/1073741824) }, upper := { exponent := 0, mantissa := (3423/2048) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870243327/274866642944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2957InnerLog : WideLogData :=
  innerPair163Data

set_option maxRecDepth 1000000 in
private theorem leaf2957LocalValidity :
    LeafFacts leaf2957Box leaf2957Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2957Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433321472) }) = true
      norm_num [leaf2957Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2957CertificateValid :
    WideCertificateValid leaf2957Box leaf2957Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi186ValidityFacts
    leaf2957LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2957CoverageChecked :
    coverageCheck (innerAD leaf2957Box) leaf2957InnerLog = true := by
  rfl'

private theorem leaf2957InnerLogValid :
    leaf2957InnerLog.Valid 8 (innerAD leaf2957Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint133PositiveFacts.valid leaf2957CoverageChecked

private noncomputable def leaf2957InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2957InputLogOnePlusV_eq :
    leaf2957InputLogOnePlusV = outerEnclosure 24
      (leaf2957Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2957RoundedFacts : LeafRoundedFacts 8
    leaf2957Certificate.logOnePlusV leaf2957InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2957InputLogOnePlusV_eq }

private noncomputable def leaf2957Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi186InputQChi innerPair163Input
    leaf2957InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2957LowerChecked :
    lowerCheck 24 leaf2957Box leaf2957Inputs = true := by
  rfl'

private theorem leaf2957CoversExact : CoversExact 8
    leaf2957Box leaf2957Certificate leaf2957InnerLog leaf2957Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi186RoundedFacts
    innerPair163RoundedFacts leaf2957RoundedFacts (by rfl)

private theorem leaf2957FlatSound : Sound leaf2957Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2957CertificateValid
    leaf2957InnerLogValid leaf2957CoversExact leaf2957LowerChecked

private noncomputable def leaf2958Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2958Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433427456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1761794471/1073741824) }, upper := { exponent := 0, mantissa := (27177/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870349311/274866854912) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2958InnerLog : WideLogData :=
  innerPair164Data

set_option maxRecDepth 1000000 in
private theorem leaf2958LocalValidity :
    LeafFacts leaf2958Box leaf2958Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2958Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433427456) }) = true
      norm_num [leaf2958Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2958CertificateValid :
    WideCertificateValid leaf2958Box leaf2958Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi185ValidityFacts
    leaf2958LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2958CoverageChecked :
    coverageCheck (innerAD leaf2958Box) leaf2958InnerLog = true := by
  rfl'

private theorem leaf2958InnerLogValid :
    leaf2958InnerLog.Valid 8 (innerAD leaf2958Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint134PositiveFacts.valid leaf2958CoverageChecked

private noncomputable def leaf2958InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2958InputLogOnePlusV_eq :
    leaf2958InputLogOnePlusV = outerEnclosure 24
      (leaf2958Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2958RoundedFacts : LeafRoundedFacts 8
    leaf2958Certificate.logOnePlusV leaf2958InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2958InputLogOnePlusV_eq }

private noncomputable def leaf2958Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi185InputQChi innerPair164Input
    leaf2958InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2958LowerChecked :
    lowerCheck 24 leaf2958Box leaf2958Inputs = true := by
  rfl'

private theorem leaf2958CoversExact : CoversExact 8
    leaf2958Box leaf2958Certificate leaf2958InnerLog leaf2958Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi185RoundedFacts
    innerPair164RoundedFacts leaf2958RoundedFacts (by rfl)

private theorem leaf2958FlatSound : Sound leaf2958Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2958CertificateValid
    leaf2958InnerLogValid leaf2958CoversExact leaf2958LowerChecked

private noncomputable def leaf2959Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2959Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486681088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1764546813/1073741824) }, upper := { exponent := 0, mantissa := (6805/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974065459/54973362176) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2959InnerLog : WideLogData :=
  innerPair165Data

set_option maxRecDepth 1000000 in
private theorem leaf2959LocalValidity :
    LeafFacts leaf2959Box leaf2959Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2959Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486681088) }) = true
      norm_num [leaf2959Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2959CertificateValid :
    WideCertificateValid leaf2959Box leaf2959Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi185ValidityFacts
    leaf2959LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2959CoverageChecked :
    coverageCheck (innerAD leaf2959Box) leaf2959InnerLog = true := by
  rfl'

private theorem leaf2959InnerLogValid :
    leaf2959InnerLog.Valid 8 (innerAD leaf2959Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint199PositiveFacts.valid leaf2959CoverageChecked

private noncomputable def leaf2959InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2959InputLogOnePlusV_eq :
    leaf2959InputLogOnePlusV = outerEnclosure 24
      (leaf2959Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2959RoundedFacts : LeafRoundedFacts 8
    leaf2959Certificate.logOnePlusV leaf2959InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2959InputLogOnePlusV_eq }

private noncomputable def leaf2959Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi185InputQChi innerPair165Input
    leaf2959InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2959LowerChecked :
    lowerCheck 24 leaf2959Box leaf2959Inputs = true := by
  rfl'

private theorem leaf2959CoversExact : CoversExact 8
    leaf2959Box leaf2959Certificate leaf2959InnerLog leaf2959Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi185RoundedFacts
    innerPair165RoundedFacts leaf2959RoundedFacts (by rfl)

private theorem leaf2959FlatSound : Sound leaf2959Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2959CertificateValid
    leaf2959InnerLogValid leaf2959CoversExact leaf2959LowerChecked

private noncomputable def leaf2960Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2960Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811099648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1778177469/1073741824) }, upper := { exponent := 0, mantissa := (6857/4096) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623406933/91622199296) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2960InnerLog : WideLogData :=
  innerPair455Data

set_option maxRecDepth 1000000 in
private theorem leaf2960LocalValidity :
    LeafFacts leaf2960Box leaf2960Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2960Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811099648) }) = true
      norm_num [leaf2960Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2960CertificateValid :
    WideCertificateValid leaf2960Box leaf2960Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi186ValidityFacts
    leaf2960LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2960CoverageChecked :
    coverageCheck (innerAD leaf2960Box) leaf2960InnerLog = true := by
  rfl'

private theorem leaf2960InnerLogValid :
    leaf2960InnerLog.Valid 8 (innerAD leaf2960Box) :=
  wideLogDataValid_of_cachedCheck endpoint174PositiveFacts
    endpoint56PositiveFacts.valid leaf2960CoverageChecked

private noncomputable def leaf2960InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2960InputLogOnePlusV_eq :
    leaf2960InputLogOnePlusV = outerEnclosure 24
      (leaf2960Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2960RoundedFacts : LeafRoundedFacts 8
    leaf2960Certificate.logOnePlusV leaf2960InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2960InputLogOnePlusV_eq }

private noncomputable def leaf2960Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi186InputQChi innerPair455Input
    leaf2960InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2960LowerChecked :
    lowerCheck 24 leaf2960Box leaf2960Inputs = true := by
  rfl'

private theorem leaf2960CoversExact : CoversExact 8
    leaf2960Box leaf2960Certificate leaf2960InnerLog leaf2960Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi186RoundedFacts
    innerPair455RoundedFacts leaf2960RoundedFacts (by rfl)

private theorem leaf2960FlatSound : Sound leaf2960Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2960CertificateValid
    leaf2960InnerLogValid leaf2960CoversExact leaf2960LowerChecked

private noncomputable def leaf2961Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2961Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433276416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1780995343/1073741824) }, upper := { exponent := 0, mantissa := (1717/1024) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870198271/274866552832) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2961InnerLog : WideLogData :=
  innerPair174Data

set_option maxRecDepth 1000000 in
private theorem leaf2961LocalValidity :
    LeafFacts leaf2961Box leaf2961Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2961Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433276416) }) = true
      norm_num [leaf2961Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2961CertificateValid :
    WideCertificateValid leaf2961Box leaf2961Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi186ValidityFacts
    leaf2961LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2961CoverageChecked :
    coverageCheck (innerAD leaf2961Box) leaf2961InnerLog = true := by
  rfl'

private theorem leaf2961InnerLogValid :
    leaf2961InnerLog.Valid 8 (innerAD leaf2961Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint59PositiveFacts.valid leaf2961CoverageChecked

private noncomputable def leaf2961InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2961InputLogOnePlusV_eq :
    leaf2961InputLogOnePlusV = outerEnclosure 24
      (leaf2961Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2961RoundedFacts : LeafRoundedFacts 8
    leaf2961Certificate.logOnePlusV leaf2961InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2961InputLogOnePlusV_eq }

private noncomputable def leaf2961Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi186InputQChi innerPair174Input
    leaf2961InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2961LowerChecked :
    lowerCheck 24 leaf2961Box leaf2961Inputs = true := by
  rfl'

private theorem leaf2961CoversExact : CoversExact 8
    leaf2961Box leaf2961Certificate leaf2961InnerLog leaf2961Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi186RoundedFacts
    innerPair174RoundedFacts leaf2961RoundedFacts (by rfl)

private theorem leaf2961FlatSound : Sound leaf2961Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2961CertificateValid
    leaf2961InnerLogValid leaf2961CoversExact leaf2961LowerChecked

private noncomputable def leaf2962Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2962Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433642496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1734271031/1073741824) }, upper := { exponent := 0, mantissa := (26757/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870564351/274867284992) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2962InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2962LocalValidity :
    LeafFacts leaf2962Box leaf2962Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2962Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433642496) }) = true
      norm_num [leaf2962Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2962CertificateValid :
    WideCertificateValid leaf2962Box leaf2962Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi183ValidityFacts
    leaf2962LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2962CoverageChecked :
    coverageCheck (innerAD leaf2962Box) leaf2962InnerLog = true := by
  rfl'

private theorem leaf2962InnerLogValid :
    leaf2962InnerLog.Valid 8 (innerAD leaf2962Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2962CoverageChecked

private noncomputable def leaf2962InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2962InputLogOnePlusV_eq :
    leaf2962InputLogOnePlusV = outerEnclosure 24
      (leaf2962Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2962RoundedFacts : LeafRoundedFacts 8
    leaf2962Certificate.logOnePlusV leaf2962InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2962InputLogOnePlusV_eq }

private noncomputable def leaf2962Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi183InputQChi innerPair166Input
    leaf2962InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2962LowerChecked :
    lowerCheck 24 leaf2962Box leaf2962Inputs = true := by
  rfl'

private theorem leaf2962CoversExact : CoversExact 8
    leaf2962Box leaf2962Certificate leaf2962InnerLog leaf2962Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi183RoundedFacts
    innerPair166RoundedFacts leaf2962RoundedFacts (by rfl)

private theorem leaf2962FlatSound : Sound leaf2962Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2962CertificateValid
    leaf2962InnerLogValid leaf2962CoversExact leaf2962LowerChecked

private noncomputable def leaf2963Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2963Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811207168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1736892309/1073741824) }, upper := { exponent := 0, mantissa := (13399/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623514453/91622414336) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2963InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2963LocalValidity :
    LeafFacts leaf2963Box leaf2963Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2963Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811207168) }) = true
      norm_num [leaf2963Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2963CertificateValid :
    WideCertificateValid leaf2963Box leaf2963Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi183ValidityFacts
    leaf2963LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2963CoverageChecked :
    coverageCheck (innerAD leaf2963Box) leaf2963InnerLog = true := by
  rfl'

private theorem leaf2963InnerLogValid :
    leaf2963InnerLog.Valid 8 (innerAD leaf2963Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2963CoverageChecked

private noncomputable def leaf2963InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2963InputLogOnePlusV_eq :
    leaf2963InputLogOnePlusV = outerEnclosure 24
      (leaf2963Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2963RoundedFacts : LeafRoundedFacts 8
    leaf2963Certificate.logOnePlusV leaf2963InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2963InputLogOnePlusV_eq }

private noncomputable def leaf2963Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi183InputQChi innerPair166Input
    leaf2963InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2963LowerChecked :
    lowerCheck 24 leaf2963Box leaf2963Inputs = true := by
  rfl'

private theorem leaf2963CoversExact : CoversExact 8
    leaf2963Box leaf2963Certificate leaf2963InnerLog leaf2963Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi183RoundedFacts
    innerPair166RoundedFacts leaf2963RoundedFacts (by rfl)

private theorem leaf2963FlatSound : Sound leaf2963Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2963CertificateValid
    leaf2963InnerLogValid leaf2963CoversExact leaf2963LowerChecked

private noncomputable def leaf2964Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2964Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486702592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1750785093/1073741824) }, upper := { exponent := 0, mantissa := (13505/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974086963/54973405184) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2964InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2964LocalValidity :
    LeafFacts leaf2964Box leaf2964Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2964Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486702592) }) = true
      norm_num [leaf2964Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2964CertificateValid :
    WideCertificateValid leaf2964Box leaf2964Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi184ValidityFacts
    leaf2964LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2964CoverageChecked :
    coverageCheck (innerAD leaf2964Box) leaf2964InnerLog = true := by
  rfl'

private theorem leaf2964InnerLogValid :
    leaf2964InnerLog.Valid 8 (innerAD leaf2964Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2964CoverageChecked

private noncomputable def leaf2964InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2964InputLogOnePlusV_eq :
    leaf2964InputLogOnePlusV = outerEnclosure 24
      (leaf2964Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2964RoundedFacts : LeafRoundedFacts 8
    leaf2964Certificate.logOnePlusV leaf2964InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2964InputLogOnePlusV_eq }

private noncomputable def leaf2964Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi184InputQChi innerPair61Input
    leaf2964InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2964LowerChecked :
    lowerCheck 24 leaf2964Box leaf2964Inputs = true := by
  rfl'

private theorem leaf2964CoversExact : CoversExact 8
    leaf2964Box leaf2964Certificate leaf2964InnerLog leaf2964Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi184RoundedFacts
    innerPair61RoundedFacts leaf2964RoundedFacts (by rfl)

private theorem leaf2964FlatSound : Sound leaf2964Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2964CertificateValid
    leaf2964InnerLogValid leaf2964CoversExact leaf2964LowerChecked

private noncomputable def leaf2965Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2965Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433491456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1753471903/1073741824) }, upper := { exponent := 0, mantissa := (6763/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870413311/274866982912) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2965InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2965LocalValidity :
    LeafFacts leaf2965Box leaf2965Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2965Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433491456) }) = true
      norm_num [leaf2965Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2965CertificateValid :
    WideCertificateValid leaf2965Box leaf2965Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi184ValidityFacts
    leaf2965LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2965CoverageChecked :
    coverageCheck (innerAD leaf2965Box) leaf2965InnerLog = true := by
  rfl'

private theorem leaf2965InnerLogValid :
    leaf2965InnerLog.Valid 8 (innerAD leaf2965Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2965CoverageChecked

private noncomputable def leaf2965InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2965InputLogOnePlusV_eq :
    leaf2965InputLogOnePlusV = outerEnclosure 24
      (leaf2965Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2965RoundedFacts : LeafRoundedFacts 8
    leaf2965Certificate.logOnePlusV leaf2965InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2965InputLogOnePlusV_eq }

private noncomputable def leaf2965Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi184InputQChi innerPair61Input
    leaf2965InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2965LowerChecked :
    lowerCheck 24 leaf2965Box leaf2965Inputs = true := by
  rfl'

private theorem leaf2965CoversExact : CoversExact 8
    leaf2965Box leaf2965Certificate leaf2965InnerLog leaf2965Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi184RoundedFacts
    innerPair61RoundedFacts leaf2965RoundedFacts (by rfl)

private theorem leaf2965FlatSound : Sound leaf2965Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2965CertificateValid
    leaf2965InnerLogValid leaf2965CoversExact leaf2965LowerChecked

private noncomputable def leaf2966Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2966Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433600512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1739513587/1073741824) }, upper := { exponent := 0, mantissa := (26839/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870522367/274867201024) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2966InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2966LocalValidity :
    LeafFacts leaf2966Box leaf2966Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2966Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433600512) }) = true
      norm_num [leaf2966Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2966CertificateValid :
    WideCertificateValid leaf2966Box leaf2966Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi183ValidityFacts
    leaf2966LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2966CoverageChecked :
    coverageCheck (innerAD leaf2966Box) leaf2966InnerLog = true := by
  rfl'

private theorem leaf2966InnerLogValid :
    leaf2966InnerLog.Valid 8 (innerAD leaf2966Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2966CoverageChecked

private noncomputable def leaf2966InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2966InputLogOnePlusV_eq :
    leaf2966InputLogOnePlusV = outerEnclosure 24
      (leaf2966Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2966RoundedFacts : LeafRoundedFacts 8
    leaf2966Certificate.logOnePlusV leaf2966InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2966InputLogOnePlusV_eq }

private noncomputable def leaf2966Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi183InputQChi innerPair166Input
    leaf2966InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2966LowerChecked :
    lowerCheck 24 leaf2966Box leaf2966Inputs = true := by
  rfl'

private theorem leaf2966CoversExact : CoversExact 8
    leaf2966Box leaf2966Certificate leaf2966InnerLog leaf2966Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi183RoundedFacts
    innerPair166RoundedFacts leaf2966RoundedFacts (by rfl)

private theorem leaf2966FlatSound : Sound leaf2966Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2966CertificateValid
    leaf2966InnerLogValid leaf2966CoversExact leaf2966LowerChecked

private noncomputable def leaf2967Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2967Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (65527/65536), upper := (27487384371/27486715904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1742134865/1073741824) }, upper := { exponent := 0, mantissa := (105/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (54974100275/54973431808) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2967InnerLog : WideLogData :=
  innerPair166Data

set_option maxRecDepth 1000000 in
private theorem leaf2967LocalValidity :
    LeafFacts leaf2967Box leaf2967Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2967Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (27487384371/27486715904) }) = true
      norm_num [leaf2967Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2967CertificateValid :
    WideCertificateValid leaf2967Box leaf2967Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi183ValidityFacts
    leaf2967LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2967CoverageChecked :
    coverageCheck (innerAD leaf2967Box) leaf2967InnerLog = true := by
  rfl'

private theorem leaf2967InnerLogValid :
    leaf2967InnerLog.Valid 8 (innerAD leaf2967Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint45PositiveFacts.valid leaf2967CoverageChecked

private noncomputable def leaf2967InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2967InputLogOnePlusV_eq :
    leaf2967InputLogOnePlusV = outerEnclosure 24
      (leaf2967Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2967RoundedFacts : LeafRoundedFacts 8
    leaf2967Certificate.logOnePlusV leaf2967InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2967InputLogOnePlusV_eq }

private noncomputable def leaf2967Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi183InputQChi innerPair166Input
    leaf2967InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2967LowerChecked :
    lowerCheck 24 leaf2967Box leaf2967Inputs = true := by
  rfl'

private theorem leaf2967CoversExact : CoversExact 8
    leaf2967Box leaf2967Certificate leaf2967InnerLog leaf2967Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi183RoundedFacts
    innerPair166RoundedFacts leaf2967RoundedFacts (by rfl)

private theorem leaf2967FlatSound : Sound leaf2967Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2967CertificateValid
    leaf2967InnerLogValid leaf2967CoversExact leaf2967LowerChecked

private noncomputable def leaf2968Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2968Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (25362045/25361408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1756158713/1073741824) }, upper := { exponent := 0, mantissa := (13547/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (50723453/50722816) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2968InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2968LocalValidity :
    LeafFacts leaf2968Box leaf2968Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2968Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (25362045/25361408) }) = true
      norm_num [leaf2968Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2968CertificateValid :
    WideCertificateValid leaf2968Box leaf2968Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi184ValidityFacts
    leaf2968LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2968CoverageChecked :
    coverageCheck (innerAD leaf2968Box) leaf2968InnerLog = true := by
  rfl'

private theorem leaf2968InnerLogValid :
    leaf2968InnerLog.Valid 8 (innerAD leaf2968Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2968CoverageChecked

private noncomputable def leaf2968InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2968InputLogOnePlusV_eq :
    leaf2968InputLogOnePlusV = outerEnclosure 24
      (leaf2968Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2968RoundedFacts : LeafRoundedFacts 8
    leaf2968Certificate.logOnePlusV leaf2968InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2968InputLogOnePlusV_eq }

private noncomputable def leaf2968Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi184InputQChi innerPair61Input
    leaf2968InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2968LowerChecked :
    lowerCheck 24 leaf2968Box leaf2968Inputs = true := by
  rfl'

private theorem leaf2968CoversExact : CoversExact 8
    leaf2968Box leaf2968Certificate leaf2968InnerLog leaf2968Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi184RoundedFacts
    innerPair61RoundedFacts leaf2968RoundedFacts (by rfl)

private theorem leaf2968FlatSound : Sound leaf2968Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2968CertificateValid
    leaf2968InnerLogValid leaf2968CoversExact leaf2968LowerChecked

private noncomputable def leaf2969Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2969Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137433448448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1758845523/1073741824) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274870370303/274866896896) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2969InnerLog : WideLogData :=
  innerPair61Data

set_option maxRecDepth 1000000 in
private theorem leaf2969LocalValidity :
    LeafFacts leaf2969Box leaf2969Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2969Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137433448448) }) = true
      norm_num [leaf2969Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2969CertificateValid :
    WideCertificateValid leaf2969Box leaf2969Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi184ValidityFacts
    leaf2969LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2969CoverageChecked :
    coverageCheck (innerAD leaf2969Box) leaf2969InnerLog = true := by
  rfl'

private theorem leaf2969InnerLogValid :
    leaf2969InnerLog.Valid 8 (innerAD leaf2969Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint48PositiveFacts.valid leaf2969CoverageChecked

private noncomputable def leaf2969InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2969InputLogOnePlusV_eq :
    leaf2969InputLogOnePlusV = outerEnclosure 24
      (leaf2969Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2969RoundedFacts : LeafRoundedFacts 8
    leaf2969Certificate.logOnePlusV leaf2969InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2969InputLogOnePlusV_eq }

private noncomputable def leaf2969Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi184InputQChi innerPair61Input
    leaf2969InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2969LowerChecked :
    lowerCheck 24 leaf2969Box leaf2969Inputs = true := by
  rfl'

private theorem leaf2969CoversExact : CoversExact 8
    leaf2969Box leaf2969Certificate leaf2969InnerLog leaf2969Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi184RoundedFacts
    innerPair61RoundedFacts leaf2969RoundedFacts (by rfl)

private theorem leaf2969FlatSound : Sound leaf2969Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2969CertificateValid
    leaf2969InnerLogValid leaf2969CoversExact leaf2969LowerChecked

private noncomputable def leaf2970Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2970Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (299426845/299419136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1767299155/1073741824) }, upper := { exponent := 0, mantissa := (27263/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (598845981/598838272) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2970InnerLog : WideLogData :=
  innerPair453Data

set_option maxRecDepth 1000000 in
private theorem leaf2970LocalValidity :
    LeafFacts leaf2970Box leaf2970Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2970Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (299426845/299419136) }) = true
      norm_num [leaf2970Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2970CertificateValid :
    WideCertificateValid leaf2970Box leaf2970Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi185ValidityFacts
    leaf2970LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2970CoverageChecked :
    coverageCheck (innerAD leaf2970Box) leaf2970InnerLog = true := by
  rfl'

private theorem leaf2970InnerLogValid :
    leaf2970InnerLog.Valid 8 (innerAD leaf2970Box) :=
  wideLogDataValid_of_cachedCheck endpoint171PositiveFacts
    endpoint199PositiveFacts.valid leaf2970CoverageChecked

private noncomputable def leaf2970InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2970InputLogOnePlusV_eq :
    leaf2970InputLogOnePlusV = outerEnclosure 24
      (leaf2970Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2970RoundedFacts : LeafRoundedFacts 8
    leaf2970Certificate.logOnePlusV leaf2970InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2970InputLogOnePlusV_eq }

private noncomputable def leaf2970Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi185InputQChi innerPair453Input
    leaf2970InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2970LowerChecked :
    lowerCheck 24 leaf2970Box leaf2970Inputs = true := by
  rfl'

private theorem leaf2970CoversExact : CoversExact 8
    leaf2970Box leaf2970Certificate leaf2970InnerLog leaf2970Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi185RoundedFacts
    innerPair453RoundedFacts leaf2970RoundedFacts (by rfl)

private theorem leaf2970FlatSound : Sound leaf2970Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2970CertificateValid
    leaf2970InnerLogValid leaf2970CoversExact leaf2970LowerChecked

private noncomputable def leaf2971Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2971Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433361408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1770051497/1073741824) }, upper := { exponent := 0, mantissa := (13653/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870283263/274866722816) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2971InnerLog : WideLogData :=
  innerPair427Data

set_option maxRecDepth 1000000 in
private theorem leaf2971LocalValidity :
    LeafFacts leaf2971Box leaf2971Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2971Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433361408) }) = true
      norm_num [leaf2971Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2971CertificateValid :
    WideCertificateValid leaf2971Box leaf2971Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi185ValidityFacts
    leaf2971LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2971CoverageChecked :
    coverageCheck (innerAD leaf2971Box) leaf2971InnerLog = true := by
  rfl'

private theorem leaf2971InnerLogValid :
    leaf2971InnerLog.Valid 8 (innerAD leaf2971Box) :=
  wideLogDataValid_of_cachedCheck endpoint135PositiveFacts
    endpoint200PositiveFacts.valid leaf2971CoverageChecked

private noncomputable def leaf2971InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2971InputLogOnePlusV_eq :
    leaf2971InputLogOnePlusV = outerEnclosure 24
      (leaf2971Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2971RoundedFacts : LeafRoundedFacts 8
    leaf2971Certificate.logOnePlusV leaf2971InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2971InputLogOnePlusV_eq }

private noncomputable def leaf2971Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi185InputQChi innerPair427Input
    leaf2971InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2971LowerChecked :
    lowerCheck 24 leaf2971Box leaf2971Inputs = true := by
  rfl'

private theorem leaf2971CoversExact : CoversExact 8
    leaf2971Box leaf2971Certificate leaf2971InnerLog leaf2971Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi185RoundedFacts
    innerPair427RoundedFacts leaf2971RoundedFacts (by rfl)

private theorem leaf2971FlatSound : Sound leaf2971Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2971CertificateValid
    leaf2971InnerLogValid leaf2971CoversExact leaf2971LowerChecked

private noncomputable def leaf2972Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2972Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433253888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1783813217/1073741824) }, upper := { exponent := 0, mantissa := (6879/4096) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870175743/274866507776) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2972InnerLog : WideLogData :=
  innerPair424Data

set_option maxRecDepth 1000000 in
private theorem leaf2972LocalValidity :
    LeafFacts leaf2972Box leaf2972Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2972Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433253888) }) = true
      norm_num [leaf2972Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2972CertificateValid :
    WideCertificateValid leaf2972Box leaf2972Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi186ValidityFacts
    leaf2972LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2972CoverageChecked :
    coverageCheck (innerAD leaf2972Box) leaf2972InnerLog = true := by
  rfl'

private theorem leaf2972InnerLogValid :
    leaf2972InnerLog.Valid 8 (innerAD leaf2972Box) :=
  wideLogDataValid_of_cachedCheck endpoint134PositiveFacts
    endpoint59PositiveFacts.valid leaf2972CoverageChecked

private noncomputable def leaf2972InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2972InputLogOnePlusV_eq :
    leaf2972InputLogOnePlusV = outerEnclosure 24
      (leaf2972Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2972RoundedFacts : LeafRoundedFacts 8
    leaf2972Certificate.logOnePlusV leaf2972InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2972InputLogOnePlusV_eq }

private noncomputable def leaf2972Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi186InputQChi innerPair424Input
    leaf2972InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2972LowerChecked :
    lowerCheck 24 leaf2972Box leaf2972Inputs = true := by
  rfl'

private theorem leaf2972CoversExact : CoversExact 8
    leaf2972Box leaf2972Certificate leaf2972InnerLog leaf2972Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi186RoundedFacts
    innerPair424RoundedFacts leaf2972RoundedFacts (by rfl)

private theorem leaf2972FlatSound : Sound leaf2972Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2972CertificateValid
    leaf2972InnerLogValid leaf2972CoversExact leaf2972LowerChecked

private noncomputable def leaf2973Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2973Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1018051273/1018023936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1786631091/1073741824) }, upper := { exponent := 0, mantissa := (3445/2048) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2036075209/2036047872) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2973InnerLog : WideLogData :=
  innerPair477Data

set_option maxRecDepth 1000000 in
private theorem leaf2973LocalValidity :
    LeafFacts leaf2973Box leaf2973Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2973Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1018051273/1018023936) }) = true
      norm_num [leaf2973Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2973CertificateValid :
    WideCertificateValid leaf2973Box leaf2973Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi186ValidityFacts
    leaf2973LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2973CoverageChecked :
    coverageCheck (innerAD leaf2973Box) leaf2973InnerLog = true := by
  rfl'

private theorem leaf2973InnerLogValid :
    leaf2973InnerLog.Valid 8 (innerAD leaf2973Box) :=
  wideLogDataValid_of_cachedCheck endpoint201PositiveFacts
    endpoint202PositiveFacts.valid leaf2973CoverageChecked

private noncomputable def leaf2973InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2973InputLogOnePlusV_eq :
    leaf2973InputLogOnePlusV = outerEnclosure 24
      (leaf2973Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2973RoundedFacts : LeafRoundedFacts 8
    leaf2973Certificate.logOnePlusV leaf2973InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2973InputLogOnePlusV_eq }

private noncomputable def leaf2973Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi186InputQChi innerPair477Input
    leaf2973InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2973LowerChecked :
    lowerCheck 24 leaf2973Box leaf2973Inputs = true := by
  rfl'

private theorem leaf2973CoversExact : CoversExact 8
    leaf2973Box leaf2973Certificate leaf2973InnerLog leaf2973Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi186RoundedFacts
    innerPair477RoundedFacts leaf2973RoundedFacts (by rfl)

private theorem leaf2973FlatSound : Sound leaf2973Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2973CertificateValid
    leaf2973InnerLogValid leaf2973CoversExact leaf2973LowerChecked

private noncomputable def leaf2974Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2974Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433339392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1772803839/1073741824) }, upper := { exponent := 0, mantissa := (27349/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870261247/274866678784) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2974InnerLog : WideLogData :=
  innerPair478Data

set_option maxRecDepth 1000000 in
private theorem leaf2974LocalValidity :
    LeafFacts leaf2974Box leaf2974Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2974Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433339392) }) = true
      norm_num [leaf2974Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2974CertificateValid :
    WideCertificateValid leaf2974Box leaf2974Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi185ValidityFacts
    leaf2974LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2974CoverageChecked :
    coverageCheck (innerAD leaf2974Box) leaf2974InnerLog = true := by
  rfl'

private theorem leaf2974InnerLogValid :
    leaf2974InnerLog.Valid 8 (innerAD leaf2974Box) :=
  wideLogDataValid_of_cachedCheck endpoint203PositiveFacts
    endpoint204PositiveFacts.valid leaf2974CoverageChecked

private noncomputable def leaf2974InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2974InputLogOnePlusV_eq :
    leaf2974InputLogOnePlusV = outerEnclosure 24
      (leaf2974Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2974RoundedFacts : LeafRoundedFacts 8
    leaf2974Certificate.logOnePlusV leaf2974InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2974InputLogOnePlusV_eq }

private noncomputable def leaf2974Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi185InputQChi innerPair478Input
    leaf2974InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2974LowerChecked :
    lowerCheck 24 leaf2974Box leaf2974Inputs = true := by
  rfl'

private theorem leaf2974CoversExact : CoversExact 8
    leaf2974Box leaf2974Certificate leaf2974InnerLog leaf2974Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi185RoundedFacts
    innerPair478RoundedFacts leaf2974RoundedFacts (by rfl)

private theorem leaf2974FlatSound : Sound leaf2974Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2974CertificateValid
    leaf2974InnerLogValid leaf2974CoversExact leaf2974LowerChecked

private noncomputable def leaf2975Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (21/128), chiHi := (85/512) }

private noncomputable def leaf2975Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484329/2147483648) }, vSqrt := { lower := (65527/65536), upper := (3196207485/3196125184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3551145641/2147483648) }, upper := { exponent := 0, mantissa := (213/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi209LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (6392332669/6392250368) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2975InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2975LocalValidity :
    LeafFacts leaf2975Box leaf2975Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2975Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (3196207485/3196125184) }) = true
      norm_num [leaf2975Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2975CertificateValid :
    WideCertificateValid leaf2975Box leaf2975Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi209ValidityFacts
    leaf2975LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2975CoverageChecked :
    coverageCheck (innerAD leaf2975Box) leaf2975InnerLog = true := by
  rfl'

private theorem leaf2975InnerLogValid :
    leaf2975InnerLog.Valid 8 (innerAD leaf2975Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2975CoverageChecked

private noncomputable def leaf2975InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2975InputLogOnePlusV_eq :
    leaf2975InputLogOnePlusV = outerEnclosure 24
      (leaf2975Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2975RoundedFacts : LeafRoundedFacts 8
    leaf2975Certificate.logOnePlusV leaf2975InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2975InputLogOnePlusV_eq }

private noncomputable def leaf2975Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi209InputQChi innerPair56Input
    leaf2975InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2975LowerChecked :
    lowerCheck 24 leaf2975Box leaf2975Inputs = true := by
  rfl'

private theorem leaf2975CoversExact : CoversExact 8
    leaf2975Box leaf2975Certificate leaf2975InnerLog leaf2975Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi209RoundedFacts
    innerPair56RoundedFacts leaf2975RoundedFacts (by rfl)

private theorem leaf2975FlatSound : Sound leaf2975Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2975CertificateValid
    leaf2975InnerLogValid leaf2975CoversExact leaf2975LowerChecked

private noncomputable def leaf2976Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (85/512), chiHi := (43/256) }

private noncomputable def leaf2976Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484331/2147483648) }, vSqrt := { lower := (65527/65536), upper := (45812307285/45811105792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3567856299/2147483648) }, upper := { exponent := 0, mantissa := (107/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi210LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (91623413077/91622211584) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2976InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2976LocalValidity :
    LeafFacts leaf2976Box leaf2976Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2976Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (45812307285/45811105792) }) = true
      norm_num [leaf2976Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2976CertificateValid :
    WideCertificateValid leaf2976Box leaf2976Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi210ValidityFacts
    leaf2976LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2976CoverageChecked :
    coverageCheck (innerAD leaf2976Box) leaf2976InnerLog = true := by
  rfl'

private theorem leaf2976InnerLogValid :
    leaf2976InnerLog.Valid 8 (innerAD leaf2976Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2976CoverageChecked

private noncomputable def leaf2976InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2976InputLogOnePlusV_eq :
    leaf2976InputLogOnePlusV = outerEnclosure 24
      (leaf2976Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2976RoundedFacts : LeafRoundedFacts 8
    leaf2976Certificate.logOnePlusV leaf2976InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2976InputLogOnePlusV_eq }

private noncomputable def leaf2976Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi210InputQChi innerPair56Input
    leaf2976InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2976LowerChecked :
    lowerCheck 24 leaf2976Box leaf2976Inputs = true := by
  rfl'

private theorem leaf2976CoversExact : CoversExact 8
    leaf2976Box leaf2976Certificate leaf2976InnerLog leaf2976Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi210RoundedFacts
    innerPair56RoundedFacts leaf2976RoundedFacts (by rfl)

private theorem leaf2976FlatSound : Sound leaf2976Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2976CertificateValid
    leaf2976InnerLogValid leaf2976CoversExact leaf2976LowerChecked

private noncomputable def leaf2977Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (43/256), chiHi := (87/512) }

private noncomputable def leaf2977Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484331/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433274112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3578931207/2147483648) }, upper := { exponent := 0, mantissa := (54953/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi211LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870195967/274866548224) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2977InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2977LocalValidity :
    LeafFacts leaf2977Box leaf2977Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2977Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433274112) }) = true
      norm_num [leaf2977Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2977CertificateValid :
    WideCertificateValid leaf2977Box leaf2977Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi211ValidityFacts
    leaf2977LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2977CoverageChecked :
    coverageCheck (innerAD leaf2977Box) leaf2977InnerLog = true := by
  rfl'

private theorem leaf2977InnerLogValid :
    leaf2977InnerLog.Valid 8 (innerAD leaf2977Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2977CoverageChecked

private noncomputable def leaf2977InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2977InputLogOnePlusV_eq :
    leaf2977InputLogOnePlusV = outerEnclosure 24
      (leaf2977Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2977RoundedFacts : LeafRoundedFacts 8
    leaf2977Certificate.logOnePlusV leaf2977InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2977InputLogOnePlusV_eq }

private noncomputable def leaf2977Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi211InputQChi innerPair56Input
    leaf2977InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2977LowerChecked :
    lowerCheck 24 leaf2977Box leaf2977Inputs = true := by
  rfl'

private theorem leaf2977CoversExact : CoversExact 8
    leaf2977Box leaf2977Certificate leaf2977InnerLog leaf2977Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi211RoundedFacts
    innerPair56RoundedFacts leaf2977RoundedFacts (by rfl)

private theorem leaf2977FlatSound : Sound leaf2977Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2977CertificateValid
    leaf2977InnerLogValid leaf2977CoversExact leaf2977LowerChecked

private noncomputable def leaf2978Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (87/512), chiHi := (11/64) }

private noncomputable def leaf2978Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484333/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433208832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3595576333/2147483648) }, upper := { exponent := 0, mantissa := (6901/4096) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi212LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870130687/274866417664) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2978InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2978LocalValidity :
    LeafFacts leaf2978Box leaf2978Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2978Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433208832) }) = true
      norm_num [leaf2978Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2978CertificateValid :
    WideCertificateValid leaf2978Box leaf2978Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi212ValidityFacts
    leaf2978LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2978CoverageChecked :
    coverageCheck (innerAD leaf2978Box) leaf2978InnerLog = true := by
  rfl'

private theorem leaf2978InnerLogValid :
    leaf2978InnerLog.Valid 8 (innerAD leaf2978Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2978CoverageChecked

private noncomputable def leaf2978InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2978InputLogOnePlusV_eq :
    leaf2978InputLogOnePlusV = outerEnclosure 24
      (leaf2978Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2978RoundedFacts : LeafRoundedFacts 8
    leaf2978Certificate.logOnePlusV leaf2978InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2978InputLogOnePlusV_eq }

private noncomputable def leaf2978Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi212InputQChi innerPair56Input
    leaf2978InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2978LowerChecked :
    lowerCheck 24 leaf2978Box leaf2978Inputs = true := by
  rfl'

private theorem leaf2978CoversExact : CoversExact 8
    leaf2978Box leaf2978Certificate leaf2978InnerLog leaf2978Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi212RoundedFacts
    innerPair56RoundedFacts leaf2978RoundedFacts (by rfl)

private theorem leaf2978FlatSound : Sound leaf2978Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2978CertificateValid
    leaf2978InnerLogValid leaf2978CoversExact leaf2978LowerChecked

private noncomputable def leaf2979Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (43/256), chiHi := (87/512) }

private noncomputable def leaf2979Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484333/2147483648) }, vSqrt := { lower := (65527/65536), upper := (27487384371/27486650368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3584566957/2147483648) }, upper := { exponent := 0, mantissa := (215/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi211LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (54974034739/54973300736) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2979InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2979LocalValidity :
    LeafFacts leaf2979Box leaf2979Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2979Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (27487384371/27486650368) }) = true
      norm_num [leaf2979Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2979CertificateValid :
    WideCertificateValid leaf2979Box leaf2979Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi211ValidityFacts
    leaf2979LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2979CoverageChecked :
    coverageCheck (innerAD leaf2979Box) leaf2979InnerLog = true := by
  rfl'

private theorem leaf2979InnerLogValid :
    leaf2979InnerLog.Valid 8 (innerAD leaf2979Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2979CoverageChecked

private noncomputable def leaf2979InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2979InputLogOnePlusV_eq :
    leaf2979InputLogOnePlusV = outerEnclosure 24
      (leaf2979Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2979RoundedFacts : LeafRoundedFacts 8
    leaf2979Certificate.logOnePlusV leaf2979InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2979InputLogOnePlusV_eq }

private noncomputable def leaf2979Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi211InputQChi innerPair56Input
    leaf2979InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2979LowerChecked :
    lowerCheck 24 leaf2979Box leaf2979Inputs = true := by
  rfl'

private theorem leaf2979CoversExact : CoversExact 8
    leaf2979Box leaf2979Certificate leaf2979InnerLog leaf2979Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi211RoundedFacts
    innerPair56RoundedFacts leaf2979RoundedFacts (by rfl)

private theorem leaf2979FlatSound : Sound leaf2979Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2979CertificateValid
    leaf2979InnerLogValid leaf2979CoversExact leaf2979LowerChecked

private noncomputable def leaf2980Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (87/512), chiHi := (11/64) }

private noncomputable def leaf2980Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484335/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137433186304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3601277615/2147483648) }, upper := { exponent := 0, mantissa := (27/16) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi212LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274870108159/274866372608) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2980InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2980LocalValidity :
    LeafFacts leaf2980Box leaf2980Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2980Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137433186304) }) = true
      norm_num [leaf2980Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2980CertificateValid :
    WideCertificateValid leaf2980Box leaf2980Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi212ValidityFacts
    leaf2980LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2980CoverageChecked :
    coverageCheck (innerAD leaf2980Box) leaf2980InnerLog = true := by
  rfl'

private theorem leaf2980InnerLogValid :
    leaf2980InnerLog.Valid 8 (innerAD leaf2980Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2980CoverageChecked

private noncomputable def leaf2980InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2980InputLogOnePlusV_eq :
    leaf2980InputLogOnePlusV = outerEnclosure 24
      (leaf2980Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2980RoundedFacts : LeafRoundedFacts 8
    leaf2980Certificate.logOnePlusV leaf2980InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2980InputLogOnePlusV_eq }

private noncomputable def leaf2980Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi212InputQChi innerPair56Input
    leaf2980InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2980LowerChecked :
    lowerCheck 24 leaf2980Box leaf2980Inputs = true := by
  rfl'

private theorem leaf2980CoversExact : CoversExact 8
    leaf2980Box leaf2980Certificate leaf2980InnerLog leaf2980Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi212RoundedFacts
    innerPair56RoundedFacts leaf2980RoundedFacts (by rfl)

private theorem leaf2980FlatSound : Sound leaf2980Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2980CertificateValid
    leaf2980InnerLogValid leaf2980CoversExact leaf2980LowerChecked

private noncomputable def component62Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node0_sound : Sound component62Node0Box :=
  sound_of_literal_split component62Node0Box leaf2946Box leaf2947Box
    .k (249/64) (by rfl) (by rfl)
    leaf2946FlatSound leaf2947FlatSound

private noncomputable def component62Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node1_sound : Sound component62Node1Box :=
  sound_of_literal_split component62Node1Box leaf2948Box leaf2949Box
    .k (249/64) (by rfl) (by rfl)
    leaf2948FlatSound leaf2949FlatSound

private noncomputable def component62Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node2_sound : Sound component62Node2Box :=
  sound_of_literal_split component62Node2Box component62Node0Box component62Node1Box
    .chi (41/256) (by rfl) (by rfl)
    component62Node0_sound component62Node1_sound

private noncomputable def component62Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node3_sound : Sound component62Node3Box :=
  sound_of_literal_split component62Node3Box leaf2950Box leaf2951Box
    .k (251/64) (by rfl) (by rfl)
    leaf2950FlatSound leaf2951FlatSound

private noncomputable def component62Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node4_sound : Sound component62Node4Box :=
  sound_of_literal_split component62Node4Box leaf2952Box leaf2953Box
    .k (251/64) (by rfl) (by rfl)
    leaf2952FlatSound leaf2953FlatSound

private noncomputable def component62Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node5_sound : Sound component62Node5Box :=
  sound_of_literal_split component62Node5Box component62Node3Box component62Node4Box
    .chi (41/256) (by rfl) (by rfl)
    component62Node3_sound component62Node4_sound

private noncomputable def component62Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node6_sound : Sound component62Node6Box :=
  sound_of_literal_split component62Node6Box component62Node2Box component62Node5Box
    .k (125/32) (by rfl) (by rfl)
    component62Node2_sound component62Node5_sound

private noncomputable def component62Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node7_sound : Sound component62Node7Box :=
  sound_of_literal_split component62Node7Box leaf2954Box leaf2955Box
    .k (249/64) (by rfl) (by rfl)
    leaf2954FlatSound leaf2955FlatSound

private noncomputable def component62Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node8_sound : Sound component62Node8Box :=
  sound_of_literal_split component62Node8Box leaf2956Box leaf2957Box
    .k (249/64) (by rfl) (by rfl)
    leaf2956FlatSound leaf2957FlatSound

private noncomputable def component62Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node9_sound : Sound component62Node9Box :=
  sound_of_literal_split component62Node9Box component62Node7Box component62Node8Box
    .chi (43/256) (by rfl) (by rfl)
    component62Node7_sound component62Node8_sound

private noncomputable def component62Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node10_sound : Sound component62Node10Box :=
  sound_of_literal_split component62Node10Box leaf2958Box leaf2959Box
    .k (251/64) (by rfl) (by rfl)
    leaf2958FlatSound leaf2959FlatSound

private noncomputable def component62Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node11_sound : Sound component62Node11Box :=
  sound_of_literal_split component62Node11Box leaf2960Box leaf2961Box
    .k (251/64) (by rfl) (by rfl)
    leaf2960FlatSound leaf2961FlatSound

private noncomputable def component62Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node12_sound : Sound component62Node12Box :=
  sound_of_literal_split component62Node12Box component62Node10Box component62Node11Box
    .chi (43/256) (by rfl) (by rfl)
    component62Node10_sound component62Node11_sound

private noncomputable def component62Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node13_sound : Sound component62Node13Box :=
  sound_of_literal_split component62Node13Box component62Node9Box component62Node12Box
    .k (125/32) (by rfl) (by rfl)
    component62Node9_sound component62Node12_sound

private noncomputable def component62Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node14_sound : Sound component62Node14Box :=
  sound_of_literal_split component62Node14Box component62Node6Box component62Node13Box
    .chi (21/128) (by rfl) (by rfl)
    component62Node6_sound component62Node13_sound

private noncomputable def component62Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node15_sound : Sound component62Node15Box :=
  sound_of_literal_split component62Node15Box leaf2962Box leaf2963Box
    .k (253/64) (by rfl) (by rfl)
    leaf2962FlatSound leaf2963FlatSound

private noncomputable def component62Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node16_sound : Sound component62Node16Box :=
  sound_of_literal_split component62Node16Box leaf2964Box leaf2965Box
    .k (253/64) (by rfl) (by rfl)
    leaf2964FlatSound leaf2965FlatSound

private noncomputable def component62Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node17_sound : Sound component62Node17Box :=
  sound_of_literal_split component62Node17Box component62Node15Box component62Node16Box
    .chi (41/256) (by rfl) (by rfl)
    component62Node15_sound component62Node16_sound

private noncomputable def component62Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node18_sound : Sound component62Node18Box :=
  sound_of_literal_split component62Node18Box leaf2966Box leaf2967Box
    .k (255/64) (by rfl) (by rfl)
    leaf2966FlatSound leaf2967FlatSound

private noncomputable def component62Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node19_sound : Sound component62Node19Box :=
  sound_of_literal_split component62Node19Box leaf2968Box leaf2969Box
    .k (255/64) (by rfl) (by rfl)
    leaf2968FlatSound leaf2969FlatSound

private noncomputable def component62Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node20_sound : Sound component62Node20Box :=
  sound_of_literal_split component62Node20Box component62Node18Box component62Node19Box
    .chi (41/256) (by rfl) (by rfl)
    component62Node18_sound component62Node19_sound

private noncomputable def component62Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component62Node21_sound : Sound component62Node21Box :=
  sound_of_literal_split component62Node21Box component62Node17Box component62Node20Box
    .k (127/32) (by rfl) (by rfl)
    component62Node17_sound component62Node20_sound

private noncomputable def component62Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node22_sound : Sound component62Node22Box :=
  sound_of_literal_split component62Node22Box leaf2970Box leaf2971Box
    .k (253/64) (by rfl) (by rfl)
    leaf2970FlatSound leaf2971FlatSound

private noncomputable def component62Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node23_sound : Sound component62Node23Box :=
  sound_of_literal_split component62Node23Box leaf2972Box leaf2973Box
    .k (253/64) (by rfl) (by rfl)
    leaf2972FlatSound leaf2973FlatSound

private noncomputable def component62Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node24_sound : Sound component62Node24Box :=
  sound_of_literal_split component62Node24Box component62Node22Box component62Node23Box
    .chi (43/256) (by rfl) (by rfl)
    component62Node22_sound component62Node23_sound

private noncomputable def component62Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node25_sound : Sound component62Node25Box :=
  sound_of_literal_split component62Node25Box leaf2975Box leaf2976Box
    .chi (85/512) (by rfl) (by rfl)
    leaf2975FlatSound leaf2976FlatSound

private noncomputable def component62Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component62Node26_sound : Sound component62Node26Box :=
  sound_of_literal_split component62Node26Box leaf2974Box component62Node25Box
    .k (255/64) (by rfl) (by rfl)
    leaf2974FlatSound component62Node25_sound

private noncomputable def component62Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node27_sound : Sound component62Node27Box :=
  sound_of_literal_split component62Node27Box leaf2977Box leaf2978Box
    .chi (87/512) (by rfl) (by rfl)
    leaf2977FlatSound leaf2978FlatSound

private noncomputable def component62Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node28_sound : Sound component62Node28Box :=
  sound_of_literal_split component62Node28Box leaf2979Box leaf2980Box
    .chi (87/512) (by rfl) (by rfl)
    leaf2979FlatSound leaf2980FlatSound

private noncomputable def component62Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node29_sound : Sound component62Node29Box :=
  sound_of_literal_split component62Node29Box component62Node27Box component62Node28Box
    .k (255/64) (by rfl) (by rfl)
    component62Node27_sound component62Node28_sound

private noncomputable def component62Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node30_sound : Sound component62Node30Box :=
  sound_of_literal_split component62Node30Box component62Node26Box component62Node29Box
    .chi (43/256) (by rfl) (by rfl)
    component62Node26_sound component62Node29_sound

private noncomputable def component62Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node31_sound : Sound component62Node31Box :=
  sound_of_literal_split component62Node31Box component62Node24Box component62Node30Box
    .k (127/32) (by rfl) (by rfl)
    component62Node24_sound component62Node30_sound

private noncomputable def component62Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component62Node32_sound : Sound component62Node32Box :=
  sound_of_literal_split component62Node32Box component62Node21Box component62Node31Box
    .chi (21/128) (by rfl) (by rfl)
    component62Node21_sound component62Node31_sound

noncomputable def component62Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
theorem component62_sound : Sound component62Box :=
  sound_of_literal_split component62Box component62Node14Box component62Node32Box
    .k (63/16) (by rfl) (by rfl)
    component62Node14_sound component62Node32_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
