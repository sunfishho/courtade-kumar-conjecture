import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2
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

private noncomputable def leaf2517Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2517Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213999) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (771704543/536870912) }, upper := { exponent := 0, mantissa := (11921/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431855/268427998) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf2517InnerLog : WideLogData :=
  innerPair406Data

set_option maxRecDepth 1000000 in
private theorem leaf2517LocalValidity :
    LeafFacts leaf2517Box leaf2517Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2517Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213999) }) = true
      norm_num [leaf2517Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2517CertificateValid :
    WideCertificateValid leaf2517Box leaf2517Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi181ValidityFacts
    leaf2517LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2517CoverageChecked :
    coverageCheck (innerAD leaf2517Box) leaf2517InnerLog = true := by
  rfl'

private theorem leaf2517InnerLogValid :
    leaf2517InnerLog.Valid 8 (innerAD leaf2517Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint42PositiveFacts.valid leaf2517CoverageChecked

private noncomputable def leaf2517InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2517InputLogOnePlusV_eq :
    leaf2517InputLogOnePlusV = outerEnclosure 24
      (leaf2517Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2517RoundedFacts : LeafRoundedFacts 8
    leaf2517Certificate.logOnePlusV leaf2517InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2517InputLogOnePlusV_eq }

private noncomputable def leaf2517Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi181InputQChi innerPair406Input
    leaf2517InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2517LowerChecked :
    lowerCheck 24 leaf2517Box leaf2517Inputs = true := by
  rfl'

private theorem leaf2517CoversExact : CoversExact 8
    leaf2517Box leaf2517Certificate leaf2517InnerLog leaf2517Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi181RoundedFacts
    innerPair406RoundedFacts leaf2517RoundedFacts (by rfl)

private theorem leaf2517FlatSound : Sound leaf2517Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2517CertificateValid
    leaf2517InnerLogValid leaf2517CoversExact leaf2517LowerChecked

private noncomputable def leaf2518Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2518Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106943) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (779044125/536870912) }, upper := { exponent := 0, mantissa := (6017/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215871/134213886) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf2518InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2518LocalValidity :
    LeafFacts leaf2518Box leaf2518Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2518Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106943) }) = true
      norm_num [leaf2518Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2518CertificateValid :
    WideCertificateValid leaf2518Box leaf2518Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi182ValidityFacts
    leaf2518LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2518CoverageChecked :
    coverageCheck (innerAD leaf2518Box) leaf2518InnerLog = true := by
  rfl'

private theorem leaf2518InnerLogValid :
    leaf2518InnerLog.Valid 8 (innerAD leaf2518Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2518CoverageChecked

private noncomputable def leaf2518InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2518InputLogOnePlusV_eq :
    leaf2518InputLogOnePlusV = outerEnclosure 24
      (leaf2518Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2518RoundedFacts : LeafRoundedFacts 8
    leaf2518Certificate.logOnePlusV leaf2518InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2518InputLogOnePlusV_eq }

private noncomputable def leaf2518Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi182InputQChi innerPair34Input
    leaf2518InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2518LowerChecked :
    lowerCheck 24 leaf2518Box leaf2518Inputs = true := by
  rfl'

private theorem leaf2518CoversExact : CoversExact 8
    leaf2518Box leaf2518Certificate leaf2518InnerLog leaf2518Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi182RoundedFacts
    innerPair34RoundedFacts leaf2518RoundedFacts (by rfl)

private theorem leaf2518FlatSound : Sound leaf2518Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2518CertificateValid
    leaf2518InnerLogValid leaf2518CoversExact leaf2518LowerChecked

private noncomputable def leaf2519Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2519Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106983) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (773801565/536870912) }, upper := { exponent := 0, mantissa := (5977/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215911/134213966) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf2519InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf2519LocalValidity :
    LeafFacts leaf2519Box leaf2519Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2519Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106983) }) = true
      norm_num [leaf2519Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2519CertificateValid :
    WideCertificateValid leaf2519Box leaf2519Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi181ValidityFacts
    leaf2519LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2519CoverageChecked :
    coverageCheck (innerAD leaf2519Box) leaf2519InnerLog = true := by
  rfl'

private theorem leaf2519InnerLogValid :
    leaf2519InnerLog.Valid 8 (innerAD leaf2519Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf2519CoverageChecked

private noncomputable def leaf2519InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2519InputLogOnePlusV_eq :
    leaf2519InputLogOnePlusV = outerEnclosure 24
      (leaf2519Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2519RoundedFacts : LeafRoundedFacts 8
    leaf2519Certificate.logOnePlusV leaf2519InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2519InputLogOnePlusV_eq }

private noncomputable def leaf2519Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi181InputQChi innerPair37Input
    leaf2519InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2519LowerChecked :
    lowerCheck 24 leaf2519Box leaf2519Inputs = true := by
  rfl'

private theorem leaf2519CoversExact : CoversExact 8
    leaf2519Box leaf2519Certificate leaf2519InnerLog leaf2519Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi181RoundedFacts
    innerPair37RoundedFacts leaf2519RoundedFacts (by rfl)

private theorem leaf2519FlatSound : Sound leaf2519Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2519CertificateValid
    leaf2519InnerLogValid leaf2519CoversExact leaf2519LowerChecked

private noncomputable def leaf2520Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2520Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553463) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (781206679/536870912) }, upper := { exponent := 0, mantissa := (3017/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107927/67106926) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf2520InnerLog : WideLogData :=
  innerPair149Data

set_option maxRecDepth 1000000 in
private theorem leaf2520LocalValidity :
    LeafFacts leaf2520Box leaf2520Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2520Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553463) }) = true
      norm_num [leaf2520Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2520CertificateValid :
    WideCertificateValid leaf2520Box leaf2520Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi182ValidityFacts
    leaf2520LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2520CoverageChecked :
    coverageCheck (innerAD leaf2520Box) leaf2520InnerLog = true := by
  rfl'

private theorem leaf2520InnerLogValid :
    leaf2520InnerLog.Valid 8 (innerAD leaf2520Box) :=
  wideLogDataValid_of_cachedCheck endpoint41PositiveFacts
    endpoint120PositiveFacts.valid leaf2520CoverageChecked

private noncomputable def leaf2520InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2520InputLogOnePlusV_eq :
    leaf2520InputLogOnePlusV = outerEnclosure 24
      (leaf2520Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2520RoundedFacts : LeafRoundedFacts 8
    leaf2520Certificate.logOnePlusV leaf2520InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2520InputLogOnePlusV_eq }

private noncomputable def leaf2520Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi182InputQChi innerPair149Input
    leaf2520InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2520LowerChecked :
    lowerCheck 24 leaf2520Box leaf2520Inputs = true := by
  rfl'

private theorem leaf2520CoversExact : CoversExact 8
    leaf2520Box leaf2520Certificate leaf2520InnerLog leaf2520Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi182RoundedFacts
    innerPair149RoundedFacts leaf2520RoundedFacts (by rfl)

private theorem leaf2520FlatSound : Sound leaf2520Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2520CertificateValid
    leaf2520InnerLogValid leaf2520CoversExact leaf2520LowerChecked

private noncomputable def leaf2521Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2521Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213773) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (786383707/536870912) }, upper := { exponent := 0, mantissa := (12147/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431629/268427546) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf2521InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2521LocalValidity :
    LeafFacts leaf2521Box leaf2521Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2521Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213773) }) = true
      norm_num [leaf2521Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2521CertificateValid :
    WideCertificateValid leaf2521Box leaf2521Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi179ValidityFacts
    leaf2521LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2521CoverageChecked :
    coverageCheck (innerAD leaf2521Box) leaf2521InnerLog = true := by
  rfl'

private theorem leaf2521InnerLogValid :
    leaf2521InnerLog.Valid 8 (innerAD leaf2521Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2521CoverageChecked

private noncomputable def leaf2521InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2521InputLogOnePlusV_eq :
    leaf2521InputLogOnePlusV = outerEnclosure 24
      (leaf2521Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2521RoundedFacts : LeafRoundedFacts 8
    leaf2521Certificate.logOnePlusV leaf2521InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2521InputLogOnePlusV_eq }

private noncomputable def leaf2521Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2521InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2521LowerChecked :
    lowerCheck 24 leaf2521Box leaf2521Inputs = true := by
  rfl'

private theorem leaf2521CoversExact : CoversExact 8
    leaf2521Box leaf2521Certificate leaf2521InnerLog leaf2521Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2521RoundedFacts (by rfl)

private theorem leaf2521FlatSound : Sound leaf2521Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2521CertificateValid
    leaf2521InnerLogValid leaf2521CoversExact leaf2521LowerChecked

private noncomputable def leaf2522Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2522Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743478784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (793723289/536870912) }, upper := { exponent := 0, mantissa := (3065/2048) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487177523/27486957568) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf2522InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2522LocalValidity :
    LeafFacts leaf2522Box leaf2522Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2522Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743478784) }) = true
      norm_num [leaf2522Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2522CertificateValid :
    WideCertificateValid leaf2522Box leaf2522Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi180ValidityFacts
    leaf2522LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2522CoverageChecked :
    coverageCheck (innerAD leaf2522Box) leaf2522InnerLog = true := by
  rfl'

private theorem leaf2522InnerLogValid :
    leaf2522InnerLog.Valid 8 (innerAD leaf2522Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2522CoverageChecked

private noncomputable def leaf2522InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2522InputLogOnePlusV_eq :
    leaf2522InputLogOnePlusV = outerEnclosure 24
      (leaf2522Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2522RoundedFacts : LeafRoundedFacts 8
    leaf2522Certificate.logOnePlusV leaf2522InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2522InputLogOnePlusV_eq }

private noncomputable def leaf2522Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2522InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2522LowerChecked :
    lowerCheck 24 leaf2522Box leaf2522Inputs = true := by
  rfl'

private theorem leaf2522CoversExact : CoversExact 8
    leaf2522Box leaf2522Certificate leaf2522InnerLog leaf2522Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2522RoundedFacts (by rfl)

private theorem leaf2522FlatSound : Sound leaf2522Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2522CertificateValid
    leaf2522InnerLogValid leaf2522CoversExact leaf2522LowerChecked

private noncomputable def leaf2523Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2523Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717433856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (788611793/536870912) }, upper := { exponent := 0, mantissa := (6091/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435927551/137434867712) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf2523InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2523LocalValidity :
    LeafFacts leaf2523Box leaf2523Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2523Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717433856) }) = true
      norm_num [leaf2523Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2523CertificateValid :
    WideCertificateValid leaf2523Box leaf2523Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi179ValidityFacts
    leaf2523LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2523CoverageChecked :
    coverageCheck (innerAD leaf2523Box) leaf2523InnerLog = true := by
  rfl'

private theorem leaf2523InnerLogValid :
    leaf2523InnerLog.Valid 8 (innerAD leaf2523Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2523CoverageChecked

private noncomputable def leaf2523InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2523InputLogOnePlusV_eq :
    leaf2523InputLogOnePlusV = outerEnclosure 24
      (leaf2523Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2523RoundedFacts : LeafRoundedFacts 8
    leaf2523Certificate.logOnePlusV leaf2523InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2523InputLogOnePlusV_eq }

private noncomputable def leaf2523Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2523InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2523LowerChecked :
    lowerCheck 24 leaf2523Box leaf2523Inputs = true := by
  rfl'

private theorem leaf2523CoversExact : CoversExact 8
    leaf2523Box leaf2523Certificate leaf2523InnerLog leaf2523Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2523RoundedFacts (by rfl)

private theorem leaf2523FlatSound : Sound leaf2523Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2523CertificateValid
    leaf2523InnerLogValid leaf2523CoversExact leaf2523LowerChecked

private noncomputable def leaf2524Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2524Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (267387135/267382784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (796016907/536870912) }, upper := { exponent := 0, mantissa := (1537/1024) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (534769919/534765568) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf2524InnerLog : WideLogData :=
  innerPair399Data

set_option maxRecDepth 1000000 in
private theorem leaf2524LocalValidity :
    LeafFacts leaf2524Box leaf2524Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2524Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (267387135/267382784) }) = true
      norm_num [leaf2524Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2524CertificateValid :
    WideCertificateValid leaf2524Box leaf2524Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi180ValidityFacts
    leaf2524LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2524CoverageChecked :
    coverageCheck (innerAD leaf2524Box) leaf2524InnerLog = true := by
  rfl'

private theorem leaf2524InnerLogValid :
    leaf2524InnerLog.Valid 8 (innerAD leaf2524Box) :=
  wideLogDataValid_of_cachedCheck endpoint111PositiveFacts
    endpoint123PositiveFacts.valid leaf2524CoverageChecked

private noncomputable def leaf2524InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2524InputLogOnePlusV_eq :
    leaf2524InputLogOnePlusV = outerEnclosure 24
      (leaf2524Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2524RoundedFacts : LeafRoundedFacts 8
    leaf2524Certificate.logOnePlusV leaf2524InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2524InputLogOnePlusV_eq }

private noncomputable def leaf2524Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi180InputQChi innerPair399Input
    leaf2524InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2524LowerChecked :
    lowerCheck 24 leaf2524Box leaf2524Inputs = true := by
  rfl'

private theorem leaf2524CoversExact : CoversExact 8
    leaf2524Box leaf2524Certificate leaf2524InnerLog leaf2524Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi180RoundedFacts
    innerPair399RoundedFacts leaf2524RoundedFacts (by rfl)

private theorem leaf2524FlatSound : Sound leaf2524Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2524CertificateValid
    leaf2524InnerLogValid leaf2524CoversExact leaf2524LowerChecked

private noncomputable def leaf2525Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2525Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213933) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (775898587/536870912) }, upper := { exponent := 0, mantissa := (11987/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431789/268427866) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf2525InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf2525LocalValidity :
    LeafFacts leaf2525Box leaf2525Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2525Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213933) }) = true
      norm_num [leaf2525Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2525CertificateValid :
    WideCertificateValid leaf2525Box leaf2525Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi181ValidityFacts
    leaf2525LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2525CoverageChecked :
    coverageCheck (innerAD leaf2525Box) leaf2525InnerLog = true := by
  rfl'

private theorem leaf2525InnerLogValid :
    leaf2525InnerLog.Valid 8 (innerAD leaf2525Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf2525CoverageChecked

private noncomputable def leaf2525InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2525InputLogOnePlusV_eq :
    leaf2525InputLogOnePlusV = outerEnclosure 24
      (leaf2525Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2525RoundedFacts : LeafRoundedFacts 8
    leaf2525Certificate.logOnePlusV leaf2525InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2525InputLogOnePlusV_eq }

private noncomputable def leaf2525Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi181InputQChi innerPair37Input
    leaf2525InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2525LowerChecked :
    lowerCheck 24 leaf2525Box leaf2525Inputs = true := by
  rfl'

private theorem leaf2525CoversExact : CoversExact 8
    leaf2525Box leaf2525Certificate leaf2525InnerLog leaf2525Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi181RoundedFacts
    innerPair37RoundedFacts leaf2525RoundedFacts (by rfl)

private theorem leaf2525FlatSound : Sound leaf2525Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2525CertificateValid
    leaf2525InnerLogValid leaf2525CoversExact leaf2525LowerChecked

private noncomputable def leaf2526Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2526Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106909) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (783369233/536870912) }, upper := { exponent := 0, mantissa := (6051/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215837/134213818) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf2526InnerLog : WideLogData :=
  innerPair149Data

set_option maxRecDepth 1000000 in
private theorem leaf2526LocalValidity :
    LeafFacts leaf2526Box leaf2526Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2526Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106909) }) = true
      norm_num [leaf2526Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2526CertificateValid :
    WideCertificateValid leaf2526Box leaf2526Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi182ValidityFacts
    leaf2526LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2526CoverageChecked :
    coverageCheck (innerAD leaf2526Box) leaf2526InnerLog = true := by
  rfl'

private theorem leaf2526InnerLogValid :
    leaf2526InnerLog.Valid 8 (innerAD leaf2526Box) :=
  wideLogDataValid_of_cachedCheck endpoint41PositiveFacts
    endpoint120PositiveFacts.valid leaf2526CoverageChecked

private noncomputable def leaf2526InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2526InputLogOnePlusV_eq :
    leaf2526InputLogOnePlusV = outerEnclosure 24
      (leaf2526Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2526RoundedFacts : LeafRoundedFacts 8
    leaf2526Certificate.logOnePlusV leaf2526InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2526InputLogOnePlusV_eq }

private noncomputable def leaf2526Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi182InputQChi innerPair149Input
    leaf2526InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2526LowerChecked :
    lowerCheck 24 leaf2526Box leaf2526Inputs = true := by
  rfl'

private theorem leaf2526CoversExact : CoversExact 8
    leaf2526Box leaf2526Certificate leaf2526InnerLog leaf2526Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi182RoundedFacts
    innerPair149RoundedFacts leaf2526RoundedFacts (by rfl)

private theorem leaf2526FlatSound : Sound leaf2526Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2526CertificateValid
    leaf2526InnerLogValid leaf2526CoversExact leaf2526LowerChecked

private noncomputable def leaf2527Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2527Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553475) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (777995609/536870912) }, upper := { exponent := 0, mantissa := (3005/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107939/67106950) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf2527InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf2527LocalValidity :
    LeafFacts leaf2527Box leaf2527Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2527Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553475) }) = true
      norm_num [leaf2527Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2527CertificateValid :
    WideCertificateValid leaf2527Box leaf2527Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi181ValidityFacts
    leaf2527LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2527CoverageChecked :
    coverageCheck (innerAD leaf2527Box) leaf2527InnerLog = true := by
  rfl'

private theorem leaf2527InnerLogValid :
    leaf2527InnerLog.Valid 8 (innerAD leaf2527Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf2527CoverageChecked

private noncomputable def leaf2527InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2527InputLogOnePlusV_eq :
    leaf2527InputLogOnePlusV = outerEnclosure 24
      (leaf2527Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2527RoundedFacts : LeafRoundedFacts 8
    leaf2527Certificate.logOnePlusV leaf2527InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2527InputLogOnePlusV_eq }

private noncomputable def leaf2527Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi181InputQChi innerPair37Input
    leaf2527InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2527LowerChecked :
    lowerCheck 24 leaf2527Box leaf2527Inputs = true := by
  rfl'

private theorem leaf2527CoversExact : CoversExact 8
    leaf2527Box leaf2527Certificate leaf2527InnerLog leaf2527Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi181RoundedFacts
    innerPair37RoundedFacts leaf2527RoundedFacts (by rfl)

private theorem leaf2527FlatSound : Sound leaf2527Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2527CertificateValid
    leaf2527InnerLogValid leaf2527CoversExact leaf2527LowerChecked

private noncomputable def leaf2528Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2528Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776723) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (785531787/536870912) }, upper := { exponent := 0, mantissa := (1517/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33553955/33553446) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf2528InnerLog : WideLogData :=
  innerPair149Data

set_option maxRecDepth 1000000 in
private theorem leaf2528LocalValidity :
    LeafFacts leaf2528Box leaf2528Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2528Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776723) }) = true
      norm_num [leaf2528Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2528CertificateValid :
    WideCertificateValid leaf2528Box leaf2528Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi182ValidityFacts
    leaf2528LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2528CoverageChecked :
    coverageCheck (innerAD leaf2528Box) leaf2528InnerLog = true := by
  rfl'

private theorem leaf2528InnerLogValid :
    leaf2528InnerLog.Valid 8 (innerAD leaf2528Box) :=
  wideLogDataValid_of_cachedCheck endpoint41PositiveFacts
    endpoint120PositiveFacts.valid leaf2528CoverageChecked

private noncomputable def leaf2528InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2528InputLogOnePlusV_eq :
    leaf2528InputLogOnePlusV = outerEnclosure 24
      (leaf2528Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2528RoundedFacts : LeafRoundedFacts 8
    leaf2528Certificate.logOnePlusV leaf2528InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2528InputLogOnePlusV_eq }

private noncomputable def leaf2528Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi182InputQChi innerPair149Input
    leaf2528InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2528LowerChecked :
    lowerCheck 24 leaf2528Box leaf2528Inputs = true := by
  rfl'

private theorem leaf2528CoversExact : CoversExact 8
    leaf2528Box leaf2528Certificate leaf2528InnerLog leaf2528Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi182RoundedFacts
    innerPair149RoundedFacts leaf2528RoundedFacts (by rfl)

private theorem leaf2528FlatSound : Sound leaf2528Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2528CertificateValid
    leaf2528InnerLogValid leaf2528CoversExact leaf2528LowerChecked

private noncomputable def leaf2529Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2529Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905805312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (790839879/536870912) }, upper := { exponent := 0, mantissa := (12217/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811969877/45811610624) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf2529InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2529LocalValidity :
    LeafFacts leaf2529Box leaf2529Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2529Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905805312) }) = true
      norm_num [leaf2529Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2529CertificateValid :
    WideCertificateValid leaf2529Box leaf2529Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi179ValidityFacts
    leaf2529LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2529CoverageChecked :
    coverageCheck (innerAD leaf2529Box) leaf2529InnerLog = true := by
  rfl'

private theorem leaf2529InnerLogValid :
    leaf2529InnerLog.Valid 8 (innerAD leaf2529Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2529CoverageChecked

private noncomputable def leaf2529InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2529InputLogOnePlusV_eq :
    leaf2529InputLogOnePlusV = outerEnclosure 24
      (leaf2529Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2529RoundedFacts : LeafRoundedFacts 8
    leaf2529Certificate.logOnePlusV leaf2529InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2529InputLogOnePlusV_eq }

private noncomputable def leaf2529Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2529InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2529LowerChecked :
    lowerCheck 24 leaf2529Box leaf2529Inputs = true := by
  rfl'

private theorem leaf2529CoversExact : CoversExact 8
    leaf2529Box leaf2529Certificate leaf2529InnerLog leaf2529Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2529RoundedFacts (by rfl)

private theorem leaf2529FlatSound : Sound leaf2529Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2529CertificateValid
    leaf2529InnerLogValid leaf2529CoversExact leaf2529LowerChecked

private noncomputable def leaf2530Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2530Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717357056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (798310525/536870912) }, upper := { exponent := 0, mantissa := (3083/2048) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435850751/137434714112) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf2530InnerLog : WideLogData :=
  innerPair407Data

set_option maxRecDepth 1000000 in
private theorem leaf2530LocalValidity :
    LeafFacts leaf2530Box leaf2530Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2530Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717357056) }) = true
      norm_num [leaf2530Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2530CertificateValid :
    WideCertificateValid leaf2530Box leaf2530Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi180ValidityFacts
    leaf2530LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2530CoverageChecked :
    coverageCheck (innerAD leaf2530Box) leaf2530InnerLog = true := by
  rfl'

private theorem leaf2530InnerLogValid :
    leaf2530InnerLog.Valid 8 (innerAD leaf2530Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint18PositiveFacts.valid leaf2530CoverageChecked

private noncomputable def leaf2530InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2530InputLogOnePlusV_eq :
    leaf2530InputLogOnePlusV = outerEnclosure 24
      (leaf2530Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2530RoundedFacts : LeafRoundedFacts 8
    leaf2530Certificate.logOnePlusV leaf2530InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2530InputLogOnePlusV_eq }

private noncomputable def leaf2530Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi180InputQChi innerPair407Input
    leaf2530InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2530LowerChecked :
    lowerCheck 24 leaf2530Box leaf2530Inputs = true := by
  rfl'

private theorem leaf2530CoversExact : CoversExact 8
    leaf2530Box leaf2530Certificate leaf2530InnerLog leaf2530Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi180RoundedFacts
    innerPair407RoundedFacts leaf2530RoundedFacts (by rfl)

private theorem leaf2530FlatSound : Sound leaf2530Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2530CertificateValid
    leaf2530InnerLogValid leaf2530CoversExact leaf2530LowerChecked

private noncomputable def leaf2531Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2531Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717398016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (793067965/536870912) }, upper := { exponent := 0, mantissa := (3063/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435891711/137434796032) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf2531InnerLog : WideLogData :=
  innerPair472Data

set_option maxRecDepth 1000000 in
private theorem leaf2531LocalValidity :
    LeafFacts leaf2531Box leaf2531Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2531Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717398016) }) = true
      norm_num [leaf2531Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2531CertificateValid :
    WideCertificateValid leaf2531Box leaf2531Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi179ValidityFacts
    leaf2531LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2531CoverageChecked :
    coverageCheck (innerAD leaf2531Box) leaf2531InnerLog = true := by
  rfl'

private theorem leaf2531InnerLogValid :
    leaf2531InnerLog.Valid 8 (innerAD leaf2531Box) :=
  wideLogDataValid_of_cachedCheck endpoint190PositiveFacts
    endpoint191PositiveFacts.valid leaf2531CoverageChecked

private noncomputable def leaf2531InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2531InputLogOnePlusV_eq :
    leaf2531InputLogOnePlusV = outerEnclosure 24
      (leaf2531Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2531RoundedFacts : LeafRoundedFacts 8
    leaf2531Certificate.logOnePlusV leaf2531InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2531InputLogOnePlusV_eq }

private noncomputable def leaf2531Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi179InputQChi innerPair472Input
    leaf2531InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2531LowerChecked :
    lowerCheck 24 leaf2531Box leaf2531Inputs = true := by
  rfl'

private theorem leaf2531CoversExact : CoversExact 8
    leaf2531Box leaf2531Certificate leaf2531InnerLog leaf2531Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi179RoundedFacts
    innerPair472RoundedFacts leaf2531RoundedFacts (by rfl)

private theorem leaf2531FlatSound : Sound leaf2531Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2531CertificateValid
    leaf2531InnerLogValid leaf2531CoversExact leaf2531LowerChecked

private noncomputable def leaf2532Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2532Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486939136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1601241125/1073741824) }, upper := { exponent := 0, mantissa := (6175/4096) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974323507/54973878272) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2532InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2532LocalValidity :
    LeafFacts leaf2532Box leaf2532Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2532Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486939136) }) = true
      norm_num [leaf2532Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2532CertificateValid :
    WideCertificateValid leaf2532Box leaf2532Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi180ValidityFacts
    leaf2532LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2532CoverageChecked :
    coverageCheck (innerAD leaf2532Box) leaf2532InnerLog = true := by
  rfl'

private theorem leaf2532InnerLogValid :
    leaf2532InnerLog.Valid 8 (innerAD leaf2532Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2532CoverageChecked

private noncomputable def leaf2532InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2532InputLogOnePlusV_eq :
    leaf2532InputLogOnePlusV = outerEnclosure 24
      (leaf2532Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2532RoundedFacts : LeafRoundedFacts 8
    leaf2532Certificate.logOnePlusV leaf2532InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2532InputLogOnePlusV_eq }

private noncomputable def leaf2532Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi180InputQChi innerPair35Input
    leaf2532InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2532LowerChecked :
    lowerCheck 24 leaf2532Box leaf2532Inputs = true := by
  rfl'

private theorem leaf2532CoversExact : CoversExact 8
    leaf2532Box leaf2532Certificate leaf2532InnerLog leaf2532Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi180RoundedFacts
    innerPair35RoundedFacts leaf2532RoundedFacts (by rfl)

private theorem leaf2532FlatSound : Sound leaf2532Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2532CertificateValid
    leaf2532InnerLogValid leaf2532CoversExact leaf2532LowerChecked

private noncomputable def leaf2533Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2533Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434677248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1603534743/1073741824) }, upper := { exponent := 0, mantissa := (773/512) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871599103/274869354496) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2533InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf2533LocalValidity :
    LeafFacts leaf2533Box leaf2533Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2533Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434677248) }) = true
      norm_num [leaf2533Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2533CertificateValid :
    WideCertificateValid leaf2533Box leaf2533Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi180ValidityFacts
    leaf2533LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2533CoverageChecked :
    coverageCheck (innerAD leaf2533Box) leaf2533InnerLog = true := by
  rfl'

private theorem leaf2533InnerLogValid :
    leaf2533InnerLog.Valid 8 (innerAD leaf2533Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf2533CoverageChecked

private noncomputable def leaf2533InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2533InputLogOnePlusV_eq :
    leaf2533InputLogOnePlusV = outerEnclosure 24
      (leaf2533Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2533RoundedFacts : LeafRoundedFacts 8
    leaf2533Certificate.logOnePlusV leaf2533InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2533InputLogOnePlusV_eq }

private noncomputable def leaf2533Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi180InputQChi innerPair35Input
    leaf2533InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2533LowerChecked :
    lowerCheck 24 leaf2533Box leaf2533Inputs = true := by
  rfl'

private theorem leaf2533CoversExact : CoversExact 8
    leaf2533Box leaf2533Certificate leaf2533InnerLog leaf2533Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi180RoundedFacts
    innerPair35RoundedFacts leaf2533RoundedFacts (by rfl)

private theorem leaf2533FlatSound : Sound leaf2533Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2533CertificateValid
    leaf2533InnerLogValid leaf2533CoversExact leaf2533LowerChecked

private noncomputable def leaf2534Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2534Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905778688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (801062871/536870912) }, upper := { exponent := 0, mantissa := (12373/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811943253/45811557376) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf2534InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2534LocalValidity :
    LeafFacts leaf2534Box leaf2534Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2534Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905778688) }) = true
      norm_num [leaf2534Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2534CertificateValid :
    WideCertificateValid leaf2534Box leaf2534Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi175ValidityFacts
    leaf2534LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2534CoverageChecked :
    coverageCheck (innerAD leaf2534Box) leaf2534InnerLog = true := by
  rfl'

private theorem leaf2534InnerLogValid :
    leaf2534InnerLog.Valid 8 (innerAD leaf2534Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2534CoverageChecked

private noncomputable def leaf2534InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2534InputLogOnePlusV_eq :
    leaf2534InputLogOnePlusV = outerEnclosure 24
      (leaf2534Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2534RoundedFacts : LeafRoundedFacts 8
    leaf2534Certificate.logOnePlusV leaf2534InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2534InputLogOnePlusV_eq }

private noncomputable def leaf2534Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi175InputQChi innerPair409Input
    leaf2534InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2534LowerChecked :
    lowerCheck 24 leaf2534Box leaf2534Inputs = true := by
  rfl'

private theorem leaf2534CoversExact : CoversExact 8
    leaf2534Box leaf2534Certificate leaf2534InnerLog leaf2534Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi175RoundedFacts
    innerPair409RoundedFacts leaf2534RoundedFacts (by rfl)

private theorem leaf2534FlatSound : Sound leaf2534Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2534CertificateValid
    leaf2534InnerLogValid leaf2534CoversExact leaf2534LowerChecked

private noncomputable def leaf2535Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2535Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717278208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (808402453/536870912) }, upper := { exponent := 0, mantissa := (6243/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435771903/137434556416) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf2535InnerLog : WideLogData :=
  innerPair412Data

set_option maxRecDepth 1000000 in
private theorem leaf2535LocalValidity :
    LeafFacts leaf2535Box leaf2535Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2535Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717278208) }) = true
      norm_num [leaf2535Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2535CertificateValid :
    WideCertificateValid leaf2535Box leaf2535Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi176ValidityFacts
    leaf2535LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2535CoverageChecked :
    coverageCheck (innerAD leaf2535Box) leaf2535InnerLog = true := by
  rfl'

private theorem leaf2535InnerLogValid :
    leaf2535InnerLog.Valid 8 (innerAD leaf2535Box) :=
  wideLogDataValid_of_cachedCheck endpoint123PositiveFacts
    endpoint112PositiveFacts.valid leaf2535CoverageChecked

private noncomputable def leaf2535InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2535InputLogOnePlusV_eq :
    leaf2535InputLogOnePlusV = outerEnclosure 24
      (leaf2535Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2535RoundedFacts : LeafRoundedFacts 8
    leaf2535Certificate.logOnePlusV leaf2535InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2535InputLogOnePlusV_eq }

private noncomputable def leaf2535Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi176InputQChi innerPair412Input
    leaf2535InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2535LowerChecked :
    lowerCheck 24 leaf2535Box leaf2535Inputs = true := by
  rfl'

private theorem leaf2535CoversExact : CoversExact 8
    leaf2535Box leaf2535Certificate leaf2535InnerLog leaf2535Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi176RoundedFacts
    innerPair412RoundedFacts leaf2535RoundedFacts (by rfl)

private theorem leaf2535FlatSound : Sound leaf2535Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2535CertificateValid
    leaf2535InnerLogValid leaf2535CoversExact leaf2535LowerChecked

private noncomputable def leaf2536Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2536Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743463424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (803422021/536870912) }, upper := { exponent := 0, mantissa := (6205/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487162163/27486926848) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf2536InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2536LocalValidity :
    LeafFacts leaf2536Box leaf2536Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2536Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743463424) }) = true
      norm_num [leaf2536Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2536CertificateValid :
    WideCertificateValid leaf2536Box leaf2536Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi175ValidityFacts
    leaf2536LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2536CoverageChecked :
    coverageCheck (innerAD leaf2536Box) leaf2536InnerLog = true := by
  rfl'

private theorem leaf2536InnerLogValid :
    leaf2536InnerLog.Valid 8 (innerAD leaf2536Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2536CoverageChecked

private noncomputable def leaf2536InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2536InputLogOnePlusV_eq :
    leaf2536InputLogOnePlusV = outerEnclosure 24
      (leaf2536Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2536RoundedFacts : LeafRoundedFacts 8
    leaf2536Certificate.logOnePlusV leaf2536InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2536InputLogOnePlusV_eq }

private noncomputable def leaf2536Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi175InputQChi innerPair409Input
    leaf2536InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2536LowerChecked :
    lowerCheck 24 leaf2536Box leaf2536Inputs = true := by
  rfl'

private theorem leaf2536CoversExact : CoversExact 8
    leaf2536Box leaf2536Certificate leaf2536InnerLog leaf2536Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi175RoundedFacts
    innerPair409RoundedFacts leaf2536RoundedFacts (by rfl)

private theorem leaf2536FlatSound : Sound leaf2536Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2536CertificateValid
    leaf2536InnerLogValid leaf2536CoversExact leaf2536LowerChecked

private noncomputable def leaf2537Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2537Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162302464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1621687113/1073741824) }, upper := { exponent := 0, mantissa := (12505/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324763921/18324604928) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2537InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2537LocalValidity :
    LeafFacts leaf2537Box leaf2537Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2537Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162302464) }) = true
      norm_num [leaf2537Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2537CertificateValid :
    WideCertificateValid leaf2537Box leaf2537Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi176ValidityFacts
    leaf2537LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2537CoverageChecked :
    coverageCheck (innerAD leaf2537Box) leaf2537InnerLog = true := by
  rfl'

private theorem leaf2537InnerLogValid :
    leaf2537InnerLog.Valid 8 (innerAD leaf2537Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2537CoverageChecked

private noncomputable def leaf2537InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2537InputLogOnePlusV_eq :
    leaf2537InputLogOnePlusV = outerEnclosure 24
      (leaf2537Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2537RoundedFacts : LeafRoundedFacts 8
    leaf2537Certificate.logOnePlusV leaf2537InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2537InputLogOnePlusV_eq }

private noncomputable def leaf2537Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2537InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2537LowerChecked :
    lowerCheck 24 leaf2537Box leaf2537Inputs = true := by
  rfl'

private theorem leaf2537CoversExact : CoversExact 8
    leaf2537Box leaf2537Certificate leaf2537InnerLog leaf2537Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2537RoundedFacts (by rfl)

private theorem leaf2537FlatSound : Sound leaf2537Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2537CertificateValid
    leaf2537InnerLogValid leaf2537CoversExact leaf2537LowerChecked

private noncomputable def leaf2538Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2538Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434517504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1624111795/1073741824) }, upper := { exponent := 0, mantissa := (3131/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871439359/274869035008) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2538InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2538LocalValidity :
    LeafFacts leaf2538Box leaf2538Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2538Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434517504) }) = true
      norm_num [leaf2538Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2538CertificateValid :
    WideCertificateValid leaf2538Box leaf2538Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi176ValidityFacts
    leaf2538LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2538CoverageChecked :
    coverageCheck (innerAD leaf2538Box) leaf2538InnerLog = true := by
  rfl'

private theorem leaf2538InnerLogValid :
    leaf2538InnerLog.Valid 8 (innerAD leaf2538Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2538CoverageChecked

private noncomputable def leaf2538InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2538InputLogOnePlusV_eq :
    leaf2538InputLogOnePlusV = outerEnclosure 24
      (leaf2538Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2538RoundedFacts : LeafRoundedFacts 8
    leaf2538Certificate.logOnePlusV leaf2538InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2538InputLogOnePlusV_eq }

private noncomputable def leaf2538Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2538InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2538LowerChecked :
    lowerCheck 24 leaf2538Box leaf2538Inputs = true := by
  rfl'

private theorem leaf2538CoversExact : CoversExact 8
    leaf2538Box leaf2538Certificate leaf2538InnerLog leaf2538Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2538RoundedFacts (by rfl)

private theorem leaf2538FlatSound : Sound leaf2538Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2538CertificateValid
    leaf2538InnerLogValid leaf2538CoversExact leaf2538LowerChecked

private noncomputable def leaf2539Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2539Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717220352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (815742035/536870912) }, upper := { exponent := 0, mantissa := (12599/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435714047/137434440704) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf2539InnerLog : WideLogData :=
  innerPair473Data

set_option maxRecDepth 1000000 in
private theorem leaf2539LocalValidity :
    LeafFacts leaf2539Box leaf2539Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2539Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717220352) }) = true
      norm_num [leaf2539Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2539CertificateValid :
    WideCertificateValid leaf2539Box leaf2539Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi177ValidityFacts
    leaf2539LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2539CoverageChecked :
    coverageCheck (innerAD leaf2539Box) leaf2539InnerLog = true := by
  rfl'

private theorem leaf2539InnerLogValid :
    leaf2539InnerLog.Valid 8 (innerAD leaf2539Box) :=
  wideLogDataValid_of_cachedCheck endpoint192PositiveFacts
    endpoint193PositiveFacts.valid leaf2539CoverageChecked

private noncomputable def leaf2539InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2539InputLogOnePlusV_eq :
    leaf2539InputLogOnePlusV = outerEnclosure 24
      (leaf2539Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2539RoundedFacts : LeafRoundedFacts 8
    leaf2539Certificate.logOnePlusV leaf2539InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2539InputLogOnePlusV_eq }

private noncomputable def leaf2539Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi177InputQChi innerPair473Input
    leaf2539InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2539LowerChecked :
    lowerCheck 24 leaf2539Box leaf2539Inputs = true := by
  rfl'

private theorem leaf2539CoversExact : CoversExact 8
    leaf2539Box leaf2539Certificate leaf2539InnerLog leaf2539Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi177RoundedFacts
    innerPair473RoundedFacts leaf2539RoundedFacts (by rfl)

private theorem leaf2539FlatSound : Sound leaf2539Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2539CertificateValid
    leaf2539InnerLogValid leaf2539CoversExact leaf2539LowerChecked

private noncomputable def leaf2540Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2540Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742353/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434345472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1646196081/1073741824) }, upper := { exponent := 0, mantissa := (3173/2048) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871267327/274868690944) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2540InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2540LocalValidity :
    LeafFacts leaf2540Box leaf2540Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2540Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434345472) }) = true
      norm_num [leaf2540Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2540CertificateValid :
    WideCertificateValid leaf2540Box leaf2540Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi178ValidityFacts
    leaf2540LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2540CoverageChecked :
    coverageCheck (innerAD leaf2540Box) leaf2540InnerLog = true := by
  rfl'

private theorem leaf2540InnerLogValid :
    leaf2540InnerLog.Valid 8 (innerAD leaf2540Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2540CoverageChecked

private noncomputable def leaf2540InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2540InputLogOnePlusV_eq :
    leaf2540InputLogOnePlusV = outerEnclosure 24
      (leaf2540Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2540RoundedFacts : LeafRoundedFacts 8
    leaf2540Certificate.logOnePlusV leaf2540InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2540InputLogOnePlusV_eq }

private noncomputable def leaf2540Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi178InputQChi innerPair40Input
    leaf2540InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2540LowerChecked :
    lowerCheck 24 leaf2540Box leaf2540Inputs = true := by
  rfl'

private theorem leaf2540CoversExact : CoversExact 8
    leaf2540Box leaf2540Certificate leaf2540InnerLog leaf2540Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi178RoundedFacts
    innerPair40RoundedFacts leaf2540RoundedFacts (by rfl)

private theorem leaf2540FlatSound : Sound leaf2540Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2540CertificateValid
    leaf2540InnerLogValid leaf2540CoversExact leaf2540LowerChecked

private noncomputable def leaf2541Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2541Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811441664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1648751827/1073741824) }, upper := { exponent := 0, mantissa := (1589/1024) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623748949/91622883328) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2541InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2541LocalValidity :
    LeafFacts leaf2541Box leaf2541Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2541Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811441664) }) = true
      norm_num [leaf2541Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2541CertificateValid :
    WideCertificateValid leaf2541Box leaf2541Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi178ValidityFacts
    leaf2541LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2541CoverageChecked :
    coverageCheck (innerAD leaf2541Box) leaf2541InnerLog = true := by
  rfl'

private theorem leaf2541InnerLogValid :
    leaf2541InnerLog.Valid 8 (innerAD leaf2541Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2541CoverageChecked

private noncomputable def leaf2541InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2541InputLogOnePlusV_eq :
    leaf2541InputLogOnePlusV = outerEnclosure 24
      (leaf2541Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2541RoundedFacts : LeafRoundedFacts 8
    leaf2541Certificate.logOnePlusV leaf2541InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2541InputLogOnePlusV_eq }

private noncomputable def leaf2541Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi178InputQChi innerPair40Input
    leaf2541InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2541LowerChecked :
    lowerCheck 24 leaf2541Box leaf2541Inputs = true := by
  rfl'

private theorem leaf2541CoversExact : CoversExact 8
    leaf2541Box leaf2541Certificate leaf2541InnerLog leaf2541Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi178RoundedFacts
    innerPair40RoundedFacts leaf2541RoundedFacts (by rfl)

private theorem leaf2541FlatSound : Sound leaf2541Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2541CertificateValid
    leaf2541InnerLogValid leaf2541CoversExact leaf2541LowerChecked

private noncomputable def leaf2542Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2542Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434420736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1636497343/1073741824) }, upper := { exponent := 0, mantissa := (25237/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871342591/274868841472) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2542InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2542LocalValidity :
    LeafFacts leaf2542Box leaf2542Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2542Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434420736) }) = true
      norm_num [leaf2542Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2542CertificateValid :
    WideCertificateValid leaf2542Box leaf2542Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi177ValidityFacts
    leaf2542LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2542CoverageChecked :
    coverageCheck (innerAD leaf2542Box) leaf2542InnerLog = true := by
  rfl'

private theorem leaf2542InnerLogValid :
    leaf2542InnerLog.Valid 8 (innerAD leaf2542Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2542CoverageChecked

private noncomputable def leaf2542InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2542InputLogOnePlusV_eq :
    leaf2542InputLogOnePlusV = outerEnclosure 24
      (leaf2542Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2542RoundedFacts : LeafRoundedFacts 8
    leaf2542Certificate.logOnePlusV leaf2542InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2542InputLogOnePlusV_eq }

private noncomputable def leaf2542Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2542InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2542LowerChecked :
    lowerCheck 24 leaf2542Box leaf2542Inputs = true := by
  rfl'

private theorem leaf2542CoversExact : CoversExact 8
    leaf2542Box leaf2542Certificate leaf2542InnerLog leaf2542Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2542RoundedFacts (by rfl)

private theorem leaf2542FlatSound : Sound leaf2542Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2542CertificateValid
    leaf2542InnerLogValid leaf2542CoversExact leaf2542LowerChecked

private noncomputable def leaf2543Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2543Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434400768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1638987557/1073741824) }, upper := { exponent := 0, mantissa := (6319/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871322623/274868801536) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2543InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2543LocalValidity :
    LeafFacts leaf2543Box leaf2543Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2543Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434400768) }) = true
      norm_num [leaf2543Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2543CertificateValid :
    WideCertificateValid leaf2543Box leaf2543Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi177ValidityFacts
    leaf2543LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2543CoverageChecked :
    coverageCheck (innerAD leaf2543Box) leaf2543InnerLog = true := by
  rfl'

private theorem leaf2543InnerLogValid :
    leaf2543InnerLog.Valid 8 (innerAD leaf2543Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2543CoverageChecked

private noncomputable def leaf2543InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2543InputLogOnePlusV_eq :
    leaf2543InputLogOnePlusV = outerEnclosure 24
      (leaf2543Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2543RoundedFacts : LeafRoundedFacts 8
    leaf2543Certificate.logOnePlusV leaf2543InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2543InputLogOnePlusV_eq }

private noncomputable def leaf2543Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2543InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2543LowerChecked :
    lowerCheck 24 leaf2543Box leaf2543Inputs = true := by
  rfl'

private theorem leaf2543CoversExact : CoversExact 8
    leaf2543Box leaf2543Certificate leaf2543InnerLog leaf2543Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2543RoundedFacts (by rfl)

private theorem leaf2543FlatSound : Sound leaf2543Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2543CertificateValid
    leaf2543InnerLogValid leaf2543CoversExact leaf2543LowerChecked

private noncomputable def leaf2544Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2544Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434304512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1651307573/1073741824) }, upper := { exponent := 0, mantissa := (3183/2048) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871226367/274868609024) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2544InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2544LocalValidity :
    LeafFacts leaf2544Box leaf2544Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2544Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434304512) }) = true
      norm_num [leaf2544Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2544CertificateValid :
    WideCertificateValid leaf2544Box leaf2544Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi178ValidityFacts
    leaf2544LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2544CoverageChecked :
    coverageCheck (innerAD leaf2544Box) leaf2544InnerLog = true := by
  rfl'

private theorem leaf2544InnerLogValid :
    leaf2544InnerLog.Valid 8 (innerAD leaf2544Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2544CoverageChecked

private noncomputable def leaf2544InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2544InputLogOnePlusV_eq :
    leaf2544InputLogOnePlusV = outerEnclosure 24
      (leaf2544Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2544RoundedFacts : LeafRoundedFacts 8
    leaf2544Certificate.logOnePlusV leaf2544InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2544InputLogOnePlusV_eq }

private noncomputable def leaf2544Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi178InputQChi innerPair40Input
    leaf2544InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2544LowerChecked :
    lowerCheck 24 leaf2544Box leaf2544Inputs = true := by
  rfl'

private theorem leaf2544CoversExact : CoversExact 8
    leaf2544Box leaf2544Certificate leaf2544InnerLog leaf2544Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi178RoundedFacts
    innerPair40RoundedFacts leaf2544RoundedFacts (by rfl)

private theorem leaf2544FlatSound : Sound leaf2544Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2544CertificateValid
    leaf2544InnerLogValid leaf2544CoversExact leaf2544LowerChecked

private noncomputable def leaf2545Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2545Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434284032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1653863319/1073741824) }, upper := { exponent := 0, mantissa := (797/512) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871205887/274868568064) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2545InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2545LocalValidity :
    LeafFacts leaf2545Box leaf2545Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2545Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434284032) }) = true
      norm_num [leaf2545Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2545CertificateValid :
    WideCertificateValid leaf2545Box leaf2545Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi178ValidityFacts
    leaf2545LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2545CoverageChecked :
    coverageCheck (innerAD leaf2545Box) leaf2545InnerLog = true := by
  rfl'

private theorem leaf2545InnerLogValid :
    leaf2545InnerLog.Valid 8 (innerAD leaf2545Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2545CoverageChecked

private noncomputable def leaf2545InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2545InputLogOnePlusV_eq :
    leaf2545InputLogOnePlusV = outerEnclosure 24
      (leaf2545Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2545RoundedFacts : LeafRoundedFacts 8
    leaf2545Certificate.logOnePlusV leaf2545InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2545InputLogOnePlusV_eq }

private noncomputable def leaf2545Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi178InputQChi innerPair40Input
    leaf2545InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2545LowerChecked :
    lowerCheck 24 leaf2545Box leaf2545Inputs = true := by
  rfl'

private theorem leaf2545CoversExact : CoversExact 8
    leaf2545Box leaf2545Certificate leaf2545InnerLog leaf2545Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi178RoundedFacts
    innerPair40RoundedFacts leaf2545RoundedFacts (by rfl)

private theorem leaf2545FlatSound : Sound leaf2545Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2545CertificateValid
    leaf2545InnerLogValid leaf2545CoversExact leaf2545LowerChecked

private noncomputable def leaf2546Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2546Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811538432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1611595183/1073741824) }, upper := { exponent := 0, mantissa := (24857/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623845717/91623076864) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2546InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2546LocalValidity :
    LeafFacts leaf2546Box leaf2546Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2546Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811538432) }) = true
      norm_num [leaf2546Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2546CertificateValid :
    WideCertificateValid leaf2546Box leaf2546Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi175ValidityFacts
    leaf2546LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2546CoverageChecked :
    coverageCheck (innerAD leaf2546Box) leaf2546InnerLog = true := by
  rfl'

private theorem leaf2546InnerLogValid :
    leaf2546InnerLog.Valid 8 (innerAD leaf2546Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2546CoverageChecked

private noncomputable def leaf2546InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2546InputLogOnePlusV_eq :
    leaf2546InputLogOnePlusV = outerEnclosure 24
      (leaf2546Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2546RoundedFacts : LeafRoundedFacts 8
    leaf2546Certificate.logOnePlusV leaf2546InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2546InputLogOnePlusV_eq }

private noncomputable def leaf2546Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2546InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2546LowerChecked :
    lowerCheck 24 leaf2546Box leaf2546Inputs = true := by
  rfl'

private theorem leaf2546CoversExact : CoversExact 8
    leaf2546Box leaf2546Certificate leaf2546InnerLog leaf2546Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2546RoundedFacts (by rfl)

private theorem leaf2546FlatSound : Sound leaf2546Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2546CertificateValid
    leaf2546InnerLogValid leaf2546CoversExact leaf2546LowerChecked

private noncomputable def leaf2547Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2547Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434596352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1613954333/1073741824) }, upper := { exponent := 0, mantissa := (12447/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871518207/274869192704) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2547InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2547LocalValidity :
    LeafFacts leaf2547Box leaf2547Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2547Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434596352) }) = true
      norm_num [leaf2547Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2547CertificateValid :
    WideCertificateValid leaf2547Box leaf2547Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi175ValidityFacts
    leaf2547LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2547CoverageChecked :
    coverageCheck (innerAD leaf2547Box) leaf2547InnerLog = true := by
  rfl'

private theorem leaf2547InnerLogValid :
    leaf2547InnerLog.Valid 8 (innerAD leaf2547Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2547CoverageChecked

private noncomputable def leaf2547InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2547InputLogOnePlusV_eq :
    leaf2547InputLogOnePlusV = outerEnclosure 24
      (leaf2547Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2547RoundedFacts : LeafRoundedFacts 8
    leaf2547Certificate.logOnePlusV leaf2547InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2547InputLogOnePlusV_eq }

private noncomputable def leaf2547Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2547InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2547LowerChecked :
    lowerCheck 24 leaf2547Box leaf2547Inputs = true := by
  rfl'

private theorem leaf2547CoversExact : CoversExact 8
    leaf2547Box leaf2547Certificate leaf2547InnerLog leaf2547Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2547RoundedFacts (by rfl)

private theorem leaf2547FlatSound : Sound leaf2547Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2547CertificateValid
    leaf2547InnerLogValid leaf2547CoversExact leaf2547LowerChecked

private noncomputable def leaf2548Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2548Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434498048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1626536477/1073741824) }, upper := { exponent := 0, mantissa := (12543/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871419903/274868996096) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2548InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2548LocalValidity :
    LeafFacts leaf2548Box leaf2548Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2548Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434498048) }) = true
      norm_num [leaf2548Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2548CertificateValid :
    WideCertificateValid leaf2548Box leaf2548Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi176ValidityFacts
    leaf2548LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2548CoverageChecked :
    coverageCheck (innerAD leaf2548Box) leaf2548InnerLog = true := by
  rfl'

private theorem leaf2548InnerLogValid :
    leaf2548InnerLog.Valid 8 (innerAD leaf2548Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2548CoverageChecked

private noncomputable def leaf2548InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2548InputLogOnePlusV_eq :
    leaf2548InputLogOnePlusV = outerEnclosure 24
      (leaf2548Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2548RoundedFacts : LeafRoundedFacts 8
    leaf2548Certificate.logOnePlusV leaf2548InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2548InputLogOnePlusV_eq }

private noncomputable def leaf2548Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2548InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2548LowerChecked :
    lowerCheck 24 leaf2548Box leaf2548Inputs = true := by
  rfl'

private theorem leaf2548CoversExact : CoversExact 8
    leaf2548Box leaf2548Certificate leaf2548InnerLog leaf2548Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2548RoundedFacts (by rfl)

private theorem leaf2548FlatSound : Sound leaf2548Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2548CertificateValid
    leaf2548InnerLogValid leaf2548CoversExact leaf2548LowerChecked

private noncomputable def leaf2549Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2549Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811492864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1628961159/1073741824) }, upper := { exponent := 0, mantissa := (6281/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623800149/91622985728) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2549InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2549LocalValidity :
    LeafFacts leaf2549Box leaf2549Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2549Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811492864) }) = true
      norm_num [leaf2549Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2549CertificateValid :
    WideCertificateValid leaf2549Box leaf2549Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi176ValidityFacts
    leaf2549LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2549CoverageChecked :
    coverageCheck (innerAD leaf2549Box) leaf2549InnerLog = true := by
  rfl'

private theorem leaf2549InnerLogValid :
    leaf2549InnerLog.Valid 8 (innerAD leaf2549Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2549CoverageChecked

private noncomputable def leaf2549InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2549InputLogOnePlusV_eq :
    leaf2549InputLogOnePlusV = outerEnclosure 24
      (leaf2549Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2549RoundedFacts : LeafRoundedFacts 8
    leaf2549Certificate.logOnePlusV leaf2549InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2549InputLogOnePlusV_eq }

private noncomputable def leaf2549Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2549InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2549LowerChecked :
    lowerCheck 24 leaf2549Box leaf2549Inputs = true := by
  rfl'

private theorem leaf2549CoversExact : CoversExact 8
    leaf2549Box leaf2549Certificate leaf2549InnerLog leaf2549Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2549RoundedFacts (by rfl)

private theorem leaf2549FlatSound : Sound leaf2549Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2549CertificateValid
    leaf2549InnerLogValid leaf2549CoversExact leaf2549LowerChecked

private noncomputable def leaf2550Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2550Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434577408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1616313483/1073741824) }, upper := { exponent := 0, mantissa := (24931/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871499263/274869154816) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2550InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2550LocalValidity :
    LeafFacts leaf2550Box leaf2550Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2550Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434577408) }) = true
      norm_num [leaf2550Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2550CertificateValid :
    WideCertificateValid leaf2550Box leaf2550Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi175ValidityFacts
    leaf2550LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2550CoverageChecked :
    coverageCheck (innerAD leaf2550Box) leaf2550InnerLog = true := by
  rfl'

private theorem leaf2550InnerLogValid :
    leaf2550InnerLog.Valid 8 (innerAD leaf2550Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2550CoverageChecked

private noncomputable def leaf2550InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2550InputLogOnePlusV_eq :
    leaf2550InputLogOnePlusV = outerEnclosure 24
      (leaf2550Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2550RoundedFacts : LeafRoundedFacts 8
    leaf2550Certificate.logOnePlusV leaf2550InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2550InputLogOnePlusV_eq }

private noncomputable def leaf2550Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2550InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2550LowerChecked :
    lowerCheck 24 leaf2550Box leaf2550Inputs = true := by
  rfl'

private theorem leaf2550CoversExact : CoversExact 8
    leaf2550Box leaf2550Certificate leaf2550InnerLog leaf2550Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2550RoundedFacts (by rfl)

private theorem leaf2550FlatSound : Sound leaf2550Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2550CertificateValid
    leaf2550InnerLogValid leaf2550CoversExact leaf2550LowerChecked

private noncomputable def leaf2551Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2551Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (299426845/299421696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1618672633/1073741824) }, upper := { exponent := 0, mantissa := (3121/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (598848541/598843392) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2551InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2551LocalValidity :
    LeafFacts leaf2551Box leaf2551Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2551Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (299426845/299421696) }) = true
      norm_num [leaf2551Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2551CertificateValid :
    WideCertificateValid leaf2551Box leaf2551Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi175ValidityFacts
    leaf2551LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2551CoverageChecked :
    coverageCheck (innerAD leaf2551Box) leaf2551InnerLog = true := by
  rfl'

private theorem leaf2551InnerLogValid :
    leaf2551InnerLog.Valid 8 (innerAD leaf2551Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2551CoverageChecked

private noncomputable def leaf2551InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2551InputLogOnePlusV_eq :
    leaf2551InputLogOnePlusV = outerEnclosure 24
      (leaf2551Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2551RoundedFacts : LeafRoundedFacts 8
    leaf2551Certificate.logOnePlusV leaf2551InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2551InputLogOnePlusV_eq }

private noncomputable def leaf2551Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2551InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2551LowerChecked :
    lowerCheck 24 leaf2551Box leaf2551Inputs = true := by
  rfl'

private theorem leaf2551CoversExact : CoversExact 8
    leaf2551Box leaf2551Certificate leaf2551InnerLog leaf2551Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2551RoundedFacts (by rfl)

private theorem leaf2551FlatSound : Sound leaf2551Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2551CertificateValid
    leaf2551InnerLogValid leaf2551CoversExact leaf2551LowerChecked

private noncomputable def leaf2552Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2552Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434459136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1631385841/1073741824) }, upper := { exponent := 0, mantissa := (12581/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871380991/274868918272) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2552InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2552LocalValidity :
    LeafFacts leaf2552Box leaf2552Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2552Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434459136) }) = true
      norm_num [leaf2552Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2552CertificateValid :
    WideCertificateValid leaf2552Box leaf2552Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi176ValidityFacts
    leaf2552LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2552CoverageChecked :
    coverageCheck (innerAD leaf2552Box) leaf2552InnerLog = true := by
  rfl'

private theorem leaf2552InnerLogValid :
    leaf2552InnerLog.Valid 8 (innerAD leaf2552Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2552CoverageChecked

private noncomputable def leaf2552InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2552InputLogOnePlusV_eq :
    leaf2552InputLogOnePlusV = outerEnclosure 24
      (leaf2552Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2552RoundedFacts : LeafRoundedFacts 8
    leaf2552Certificate.logOnePlusV leaf2552InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2552InputLogOnePlusV_eq }

private noncomputable def leaf2552Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2552InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2552LowerChecked :
    lowerCheck 24 leaf2552Box leaf2552Inputs = true := by
  rfl'

private theorem leaf2552CoversExact : CoversExact 8
    leaf2552Box leaf2552Certificate leaf2552InnerLog leaf2552Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2552RoundedFacts (by rfl)

private theorem leaf2552FlatSound : Sound leaf2552Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2552CertificateValid
    leaf2552InnerLogValid leaf2552CoversExact leaf2552LowerChecked

private noncomputable def leaf2553Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2553Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (639241497/639229952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1633810523/1073741824) }, upper := { exponent := 0, mantissa := (1575/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1278471449/1278459904) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2553InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2553LocalValidity :
    LeafFacts leaf2553Box leaf2553Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2553Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (639241497/639229952) }) = true
      norm_num [leaf2553Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2553CertificateValid :
    WideCertificateValid leaf2553Box leaf2553Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi176ValidityFacts
    leaf2553LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2553CoverageChecked :
    coverageCheck (innerAD leaf2553Box) leaf2553InnerLog = true := by
  rfl'

private theorem leaf2553InnerLogValid :
    leaf2553InnerLog.Valid 8 (innerAD leaf2553Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2553CoverageChecked

private noncomputable def leaf2553InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2553InputLogOnePlusV_eq :
    leaf2553InputLogOnePlusV = outerEnclosure 24
      (leaf2553Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2553RoundedFacts : LeafRoundedFacts 8
    leaf2553Certificate.logOnePlusV leaf2553InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2553InputLogOnePlusV_eq }

private noncomputable def leaf2553Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi176InputQChi innerPair40Input
    leaf2553InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2553LowerChecked :
    lowerCheck 24 leaf2553Box leaf2553Inputs = true := by
  rfl'

private theorem leaf2553CoversExact : CoversExact 8
    leaf2553Box leaf2553Certificate leaf2553InnerLog leaf2553Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi176RoundedFacts
    innerPair40RoundedFacts leaf2553RoundedFacts (by rfl)

private theorem leaf2553FlatSound : Sound leaf2553Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2553CertificateValid
    leaf2553InnerLogValid leaf2553CoversExact leaf2553LowerChecked

private noncomputable def leaf2554Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2554Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486876160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1641477771/1073741824) }, upper := { exponent := 0, mantissa := (25315/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974260531/54973752320) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2554InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2554LocalValidity :
    LeafFacts leaf2554Box leaf2554Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2554Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486876160) }) = true
      norm_num [leaf2554Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2554CertificateValid :
    WideCertificateValid leaf2554Box leaf2554Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi177ValidityFacts
    leaf2554LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2554CoverageChecked :
    coverageCheck (innerAD leaf2554Box) leaf2554InnerLog = true := by
  rfl'

private theorem leaf2554InnerLogValid :
    leaf2554InnerLog.Valid 8 (innerAD leaf2554Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2554CoverageChecked

private noncomputable def leaf2554InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2554InputLogOnePlusV_eq :
    leaf2554InputLogOnePlusV = outerEnclosure 24
      (leaf2554Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2554RoundedFacts : LeafRoundedFacts 8
    leaf2554Certificate.logOnePlusV leaf2554InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2554InputLogOnePlusV_eq }

private noncomputable def leaf2554Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2554InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2554LowerChecked :
    lowerCheck 24 leaf2554Box leaf2554Inputs = true := by
  rfl'

private theorem leaf2554CoversExact : CoversExact 8
    leaf2554Box leaf2554Certificate leaf2554InnerLog leaf2554Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2554RoundedFacts (by rfl)

private theorem leaf2554FlatSound : Sound leaf2554Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2554CertificateValid
    leaf2554InnerLogValid leaf2554CoversExact leaf2554LowerChecked

private noncomputable def leaf2555Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2555Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434360832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1643967985/1073741824) }, upper := { exponent := 0, mantissa := (12677/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871282687/274868721664) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2555InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2555LocalValidity :
    LeafFacts leaf2555Box leaf2555Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2555Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434360832) }) = true
      norm_num [leaf2555Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2555CertificateValid :
    WideCertificateValid leaf2555Box leaf2555Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi177ValidityFacts
    leaf2555LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2555CoverageChecked :
    coverageCheck (innerAD leaf2555Box) leaf2555InnerLog = true := by
  rfl'

private theorem leaf2555InnerLogValid :
    leaf2555InnerLog.Valid 8 (innerAD leaf2555Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2555CoverageChecked

private noncomputable def leaf2555InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2555InputLogOnePlusV_eq :
    leaf2555InputLogOnePlusV = outerEnclosure 24
      (leaf2555Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2555RoundedFacts : LeafRoundedFacts 8
    leaf2555Certificate.logOnePlusV leaf2555InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2555InputLogOnePlusV_eq }

private noncomputable def leaf2555Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2555InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2555LowerChecked :
    lowerCheck 24 leaf2555Box leaf2555Inputs = true := by
  rfl'

private theorem leaf2555CoversExact : CoversExact 8
    leaf2555Box leaf2555Certificate leaf2555InnerLog leaf2555Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2555RoundedFacts (by rfl)

private theorem leaf2555FlatSound : Sound leaf2555Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2555CertificateValid
    leaf2555InnerLogValid leaf2555CoversExact leaf2555LowerChecked

private noncomputable def leaf2556Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2556Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (355134165/355127296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1656419065/1073741824) }, upper := { exponent := 0, mantissa := (3193/2048) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (710261461/710254592) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2556InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2556LocalValidity :
    LeafFacts leaf2556Box leaf2556Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2556Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (355134165/355127296) }) = true
      norm_num [leaf2556Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2556CertificateValid :
    WideCertificateValid leaf2556Box leaf2556Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi178ValidityFacts
    leaf2556LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2556CoverageChecked :
    coverageCheck (innerAD leaf2556Box) leaf2556InnerLog = true := by
  rfl'

private theorem leaf2556InnerLogValid :
    leaf2556InnerLog.Valid 8 (innerAD leaf2556Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2556CoverageChecked

private noncomputable def leaf2556InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2556InputLogOnePlusV_eq :
    leaf2556InputLogOnePlusV = outerEnclosure 24
      (leaf2556Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2556RoundedFacts : LeafRoundedFacts 8
    leaf2556Certificate.logOnePlusV leaf2556InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2556InputLogOnePlusV_eq }

private noncomputable def leaf2556Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi178InputQChi innerPair40Input
    leaf2556InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2556LowerChecked :
    lowerCheck 24 leaf2556Box leaf2556Inputs = true := by
  rfl'

private theorem leaf2556CoversExact : CoversExact 8
    leaf2556Box leaf2556Certificate leaf2556InnerLog leaf2556Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi178RoundedFacts
    innerPair40RoundedFacts leaf2556RoundedFacts (by rfl)

private theorem leaf2556FlatSound : Sound leaf2556Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2556CertificateValid
    leaf2556InnerLogValid leaf2556CoversExact leaf2556LowerChecked

private noncomputable def leaf2557Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2557Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434243072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1658974811/1073741824) }, upper := { exponent := 0, mantissa := (1599/1024) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871164927/274868486144) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2557InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2557LocalValidity :
    LeafFacts leaf2557Box leaf2557Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2557Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434243072) }) = true
      norm_num [leaf2557Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2557CertificateValid :
    WideCertificateValid leaf2557Box leaf2557Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi178ValidityFacts
    leaf2557LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2557CoverageChecked :
    coverageCheck (innerAD leaf2557Box) leaf2557InnerLog = true := by
  rfl'

private theorem leaf2557InnerLogValid :
    leaf2557InnerLog.Valid 8 (innerAD leaf2557Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2557CoverageChecked

private noncomputable def leaf2557InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2557InputLogOnePlusV_eq :
    leaf2557InputLogOnePlusV = outerEnclosure 24
      (leaf2557Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2557RoundedFacts : LeafRoundedFacts 8
    leaf2557Certificate.logOnePlusV leaf2557InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2557InputLogOnePlusV_eq }

private noncomputable def leaf2557Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi178InputQChi innerPair40Input
    leaf2557InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2557LowerChecked :
    lowerCheck 24 leaf2557Box leaf2557Inputs = true := by
  rfl'

private theorem leaf2557CoversExact : CoversExact 8
    leaf2557Box leaf2557Certificate leaf2557InnerLog leaf2557Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi178RoundedFacts
    innerPair40RoundedFacts leaf2557RoundedFacts (by rfl)

private theorem leaf2557FlatSound : Sound leaf2557Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2557CertificateValid
    leaf2557InnerLogValid leaf2557CoversExact leaf2557LowerChecked

private noncomputable def leaf2558Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2558Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084372992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1646458199/1073741824) }, upper := { exponent := 0, mantissa := (25393/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168897807/16168745984) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2558InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2558LocalValidity :
    LeafFacts leaf2558Box leaf2558Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2558Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084372992) }) = true
      norm_num [leaf2558Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2558CertificateValid :
    WideCertificateValid leaf2558Box leaf2558Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi177ValidityFacts
    leaf2558LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2558CoverageChecked :
    coverageCheck (innerAD leaf2558Box) leaf2558InnerLog = true := by
  rfl'

private theorem leaf2558InnerLogValid :
    leaf2558InnerLog.Valid 8 (innerAD leaf2558Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2558CoverageChecked

private noncomputable def leaf2558InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2558InputLogOnePlusV_eq :
    leaf2558InputLogOnePlusV = outerEnclosure 24
      (leaf2558Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2558RoundedFacts : LeafRoundedFacts 8
    leaf2558Certificate.logOnePlusV leaf2558InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2558InputLogOnePlusV_eq }

private noncomputable def leaf2558Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2558InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2558LowerChecked :
    lowerCheck 24 leaf2558Box leaf2558Inputs = true := by
  rfl'

private theorem leaf2558CoversExact : CoversExact 8
    leaf2558Box leaf2558Certificate leaf2558InnerLog leaf2558Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2558RoundedFacts (by rfl)

private theorem leaf2558FlatSound : Sound leaf2558Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2558CertificateValid
    leaf2558InnerLogValid leaf2558CoversExact leaf2558LowerChecked

private noncomputable def leaf2559Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2559Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434320896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1648948413/1073741824) }, upper := { exponent := 0, mantissa := (3179/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871242751/274868641792) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2559InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2559LocalValidity :
    LeafFacts leaf2559Box leaf2559Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2559Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434320896) }) = true
      norm_num [leaf2559Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2559CertificateValid :
    WideCertificateValid leaf2559Box leaf2559Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi177ValidityFacts
    leaf2559LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2559CoverageChecked :
    coverageCheck (innerAD leaf2559Box) leaf2559InnerLog = true := by
  rfl'

private theorem leaf2559InnerLogValid :
    leaf2559InnerLog.Valid 8 (innerAD leaf2559Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2559CoverageChecked

private noncomputable def leaf2559InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2559InputLogOnePlusV_eq :
    leaf2559InputLogOnePlusV = outerEnclosure 24
      (leaf2559Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2559RoundedFacts : LeafRoundedFacts 8
    leaf2559Certificate.logOnePlusV leaf2559InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2559InputLogOnePlusV_eq }

private noncomputable def leaf2559Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi177InputQChi innerPair40Input
    leaf2559InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2559LowerChecked :
    lowerCheck 24 leaf2559Box leaf2559Inputs = true := by
  rfl'

private theorem leaf2559CoversExact : CoversExact 8
    leaf2559Box leaf2559Certificate leaf2559InnerLog leaf2559Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi177RoundedFacts
    innerPair40RoundedFacts leaf2559RoundedFacts (by rfl)

private theorem leaf2559FlatSound : Sound leaf2559Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2559CertificateValid
    leaf2559InnerLogValid leaf2559CoversExact leaf2559LowerChecked

private noncomputable def leaf2560Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2560Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434222592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1661530557/1073741824) }, upper := { exponent := 0, mantissa := (3203/2048) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871144447/274868445184) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2560InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2560LocalValidity :
    LeafFacts leaf2560Box leaf2560Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2560Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434222592) }) = true
      norm_num [leaf2560Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2560CertificateValid :
    WideCertificateValid leaf2560Box leaf2560Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi178ValidityFacts
    leaf2560LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2560CoverageChecked :
    coverageCheck (innerAD leaf2560Box) leaf2560InnerLog = true := by
  rfl'

private theorem leaf2560InnerLogValid :
    leaf2560InnerLog.Valid 8 (innerAD leaf2560Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2560CoverageChecked

private noncomputable def leaf2560InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2560InputLogOnePlusV_eq :
    leaf2560InputLogOnePlusV = outerEnclosure 24
      (leaf2560Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2560RoundedFacts : LeafRoundedFacts 8
    leaf2560Certificate.logOnePlusV leaf2560InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2560InputLogOnePlusV_eq }

private noncomputable def leaf2560Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi178InputQChi innerPair41Input
    leaf2560InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2560LowerChecked :
    lowerCheck 24 leaf2560Box leaf2560Inputs = true := by
  rfl'

private theorem leaf2560CoversExact : CoversExact 8
    leaf2560Box leaf2560Certificate leaf2560InnerLog leaf2560Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi178RoundedFacts
    innerPair41RoundedFacts leaf2560RoundedFacts (by rfl)

private theorem leaf2560FlatSound : Sound leaf2560Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2560CertificateValid
    leaf2560InnerLogValid leaf2560CoversExact leaf2560LowerChecked

private noncomputable def leaf2561Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2561Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811400704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1664086303/1073741824) }, upper := { exponent := 0, mantissa := (401/256) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623707989/91622801408) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2561InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2561LocalValidity :
    LeafFacts leaf2561Box leaf2561Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2561Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811400704) }) = true
      norm_num [leaf2561Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2561CertificateValid :
    WideCertificateValid leaf2561Box leaf2561Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi178ValidityFacts
    leaf2561LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2561CoverageChecked :
    coverageCheck (innerAD leaf2561Box) leaf2561InnerLog = true := by
  rfl'

private theorem leaf2561InnerLogValid :
    leaf2561InnerLog.Valid 8 (innerAD leaf2561Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2561CoverageChecked

private noncomputable def leaf2561InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2561InputLogOnePlusV_eq :
    leaf2561InputLogOnePlusV = outerEnclosure 24
      (leaf2561Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2561RoundedFacts : LeafRoundedFacts 8
    leaf2561Certificate.logOnePlusV leaf2561InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2561InputLogOnePlusV_eq }

private noncomputable def leaf2561Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi178InputQChi innerPair41Input
    leaf2561InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2561LowerChecked :
    lowerCheck 24 leaf2561Box leaf2561Inputs = true := by
  rfl'

private theorem leaf2561CoversExact : CoversExact 8
    leaf2561Box leaf2561Certificate leaf2561InnerLog leaf2561Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi178RoundedFacts
    innerPair41RoundedFacts leaf2561RoundedFacts (by rfl)

private theorem leaf2561FlatSound : Sound leaf2561Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2561CertificateValid
    leaf2561InnerLogValid leaf2561CoversExact leaf2561LowerChecked

private noncomputable def component54Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node0_sound : Sound component54Node0Box :=
  sound_of_literal_split component54Node0Box leaf2517Box leaf2518Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2517FlatSound leaf2518FlatSound

private noncomputable def component54Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node1_sound : Sound component54Node1Box :=
  sound_of_literal_split component54Node1Box leaf2519Box leaf2520Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2519FlatSound leaf2520FlatSound

private noncomputable def component54Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node2_sound : Sound component54Node2Box :=
  sound_of_literal_split component54Node2Box component54Node0Box component54Node1Box
    .k (113/32) (by rfl) (by rfl)
    component54Node0_sound component54Node1_sound

private noncomputable def component54Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node3_sound : Sound component54Node3Box :=
  sound_of_literal_split component54Node3Box leaf2521Box leaf2522Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2521FlatSound leaf2522FlatSound

private noncomputable def component54Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node4_sound : Sound component54Node4Box :=
  sound_of_literal_split component54Node4Box leaf2523Box leaf2524Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2523FlatSound leaf2524FlatSound

private noncomputable def component54Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node5_sound : Sound component54Node5Box :=
  sound_of_literal_split component54Node5Box component54Node3Box component54Node4Box
    .k (113/32) (by rfl) (by rfl)
    component54Node3_sound component54Node4_sound

private noncomputable def component54Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node6_sound : Sound component54Node6Box :=
  sound_of_literal_split component54Node6Box component54Node2Box component54Node5Box
    .chi (17/128) (by rfl) (by rfl)
    component54Node2_sound component54Node5_sound

private noncomputable def component54Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node7_sound : Sound component54Node7Box :=
  sound_of_literal_split component54Node7Box leaf2525Box leaf2526Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2525FlatSound leaf2526FlatSound

private noncomputable def component54Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node8_sound : Sound component54Node8Box :=
  sound_of_literal_split component54Node8Box leaf2527Box leaf2528Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2527FlatSound leaf2528FlatSound

private noncomputable def component54Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node9_sound : Sound component54Node9Box :=
  sound_of_literal_split component54Node9Box component54Node7Box component54Node8Box
    .k (115/32) (by rfl) (by rfl)
    component54Node7_sound component54Node8_sound

private noncomputable def component54Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node10_sound : Sound component54Node10Box :=
  sound_of_literal_split component54Node10Box leaf2529Box leaf2530Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2529FlatSound leaf2530FlatSound

private noncomputable def component54Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node11_sound : Sound component54Node11Box :=
  sound_of_literal_split component54Node11Box leaf2532Box leaf2533Box
    .k (231/64) (by rfl) (by rfl)
    leaf2532FlatSound leaf2533FlatSound

private noncomputable def component54Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node12_sound : Sound component54Node12Box :=
  sound_of_literal_split component54Node12Box leaf2531Box component54Node11Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2531FlatSound component54Node11_sound

private noncomputable def component54Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node13_sound : Sound component54Node13Box :=
  sound_of_literal_split component54Node13Box component54Node10Box component54Node12Box
    .k (115/32) (by rfl) (by rfl)
    component54Node10_sound component54Node12_sound

private noncomputable def component54Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node14_sound : Sound component54Node14Box :=
  sound_of_literal_split component54Node14Box component54Node9Box component54Node13Box
    .chi (17/128) (by rfl) (by rfl)
    component54Node9_sound component54Node13_sound

private noncomputable def component54Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component54Node15_sound : Sound component54Node15Box :=
  sound_of_literal_split component54Node15Box component54Node6Box component54Node14Box
    .k (57/16) (by rfl) (by rfl)
    component54Node6_sound component54Node14_sound

private noncomputable def component54Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node16_sound : Sound component54Node16Box :=
  sound_of_literal_split component54Node16Box leaf2534Box leaf2535Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2534FlatSound leaf2535FlatSound

private noncomputable def component54Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node17_sound : Sound component54Node17Box :=
  sound_of_literal_split component54Node17Box leaf2537Box leaf2538Box
    .k (227/64) (by rfl) (by rfl)
    leaf2537FlatSound leaf2538FlatSound

private noncomputable def component54Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node18_sound : Sound component54Node18Box :=
  sound_of_literal_split component54Node18Box leaf2536Box component54Node17Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2536FlatSound component54Node17_sound

private noncomputable def component54Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node19_sound : Sound component54Node19Box :=
  sound_of_literal_split component54Node19Box component54Node16Box component54Node18Box
    .k (113/32) (by rfl) (by rfl)
    component54Node16_sound component54Node18_sound

private noncomputable def component54Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node20_sound : Sound component54Node20Box :=
  sound_of_literal_split component54Node20Box leaf2540Box leaf2541Box
    .k (225/64) (by rfl) (by rfl)
    leaf2540FlatSound leaf2541FlatSound

private noncomputable def component54Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node21_sound : Sound component54Node21Box :=
  sound_of_literal_split component54Node21Box leaf2539Box component54Node20Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2539FlatSound component54Node20_sound

private noncomputable def component54Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component54Node22_sound : Sound component54Node22Box :=
  sound_of_literal_split component54Node22Box leaf2542Box leaf2543Box
    .k (227/64) (by rfl) (by rfl)
    leaf2542FlatSound leaf2543FlatSound

private noncomputable def component54Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node23_sound : Sound component54Node23Box :=
  sound_of_literal_split component54Node23Box leaf2544Box leaf2545Box
    .k (227/64) (by rfl) (by rfl)
    leaf2544FlatSound leaf2545FlatSound

private noncomputable def component54Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node24_sound : Sound component54Node24Box :=
  sound_of_literal_split component54Node24Box component54Node22Box component54Node23Box
    .chi (39/256) (by rfl) (by rfl)
    component54Node22_sound component54Node23_sound

private noncomputable def component54Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node25_sound : Sound component54Node25Box :=
  sound_of_literal_split component54Node25Box component54Node21Box component54Node24Box
    .k (113/32) (by rfl) (by rfl)
    component54Node21_sound component54Node24_sound

private noncomputable def component54Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node26_sound : Sound component54Node26Box :=
  sound_of_literal_split component54Node26Box component54Node19Box component54Node25Box
    .chi (19/128) (by rfl) (by rfl)
    component54Node19_sound component54Node25_sound

private noncomputable def component54Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component54Node27_sound : Sound component54Node27Box :=
  sound_of_literal_split component54Node27Box leaf2546Box leaf2547Box
    .k (229/64) (by rfl) (by rfl)
    leaf2546FlatSound leaf2547FlatSound

private noncomputable def component54Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node28_sound : Sound component54Node28Box :=
  sound_of_literal_split component54Node28Box leaf2548Box leaf2549Box
    .k (229/64) (by rfl) (by rfl)
    leaf2548FlatSound leaf2549FlatSound

private noncomputable def component54Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node29_sound : Sound component54Node29Box :=
  sound_of_literal_split component54Node29Box component54Node27Box component54Node28Box
    .chi (37/256) (by rfl) (by rfl)
    component54Node27_sound component54Node28_sound

private noncomputable def component54Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component54Node30_sound : Sound component54Node30Box :=
  sound_of_literal_split component54Node30Box leaf2550Box leaf2551Box
    .k (231/64) (by rfl) (by rfl)
    leaf2550FlatSound leaf2551FlatSound

private noncomputable def component54Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node31_sound : Sound component54Node31Box :=
  sound_of_literal_split component54Node31Box leaf2552Box leaf2553Box
    .k (231/64) (by rfl) (by rfl)
    leaf2552FlatSound leaf2553FlatSound

private noncomputable def component54Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node32_sound : Sound component54Node32Box :=
  sound_of_literal_split component54Node32Box component54Node30Box component54Node31Box
    .chi (37/256) (by rfl) (by rfl)
    component54Node30_sound component54Node31_sound

private noncomputable def component54Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component54Node33_sound : Sound component54Node33Box :=
  sound_of_literal_split component54Node33Box component54Node29Box component54Node32Box
    .k (115/32) (by rfl) (by rfl)
    component54Node29_sound component54Node32_sound

private noncomputable def component54Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component54Node34_sound : Sound component54Node34Box :=
  sound_of_literal_split component54Node34Box leaf2554Box leaf2555Box
    .k (229/64) (by rfl) (by rfl)
    leaf2554FlatSound leaf2555FlatSound

private noncomputable def component54Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node35_sound : Sound component54Node35Box :=
  sound_of_literal_split component54Node35Box leaf2556Box leaf2557Box
    .k (229/64) (by rfl) (by rfl)
    leaf2556FlatSound leaf2557FlatSound

private noncomputable def component54Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node36_sound : Sound component54Node36Box :=
  sound_of_literal_split component54Node36Box component54Node34Box component54Node35Box
    .chi (39/256) (by rfl) (by rfl)
    component54Node34_sound component54Node35_sound

private noncomputable def component54Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component54Node37_sound : Sound component54Node37Box :=
  sound_of_literal_split component54Node37Box leaf2558Box leaf2559Box
    .k (231/64) (by rfl) (by rfl)
    leaf2558FlatSound leaf2559FlatSound

private noncomputable def component54Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node38_sound : Sound component54Node38Box :=
  sound_of_literal_split component54Node38Box leaf2560Box leaf2561Box
    .k (231/64) (by rfl) (by rfl)
    leaf2560FlatSound leaf2561FlatSound

private noncomputable def component54Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node39_sound : Sound component54Node39Box :=
  sound_of_literal_split component54Node39Box component54Node37Box component54Node38Box
    .chi (39/256) (by rfl) (by rfl)
    component54Node37_sound component54Node38_sound

private noncomputable def component54Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node40_sound : Sound component54Node40Box :=
  sound_of_literal_split component54Node40Box component54Node36Box component54Node39Box
    .k (115/32) (by rfl) (by rfl)
    component54Node36_sound component54Node39_sound

private noncomputable def component54Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node41_sound : Sound component54Node41Box :=
  sound_of_literal_split component54Node41Box component54Node33Box component54Node40Box
    .chi (19/128) (by rfl) (by rfl)
    component54Node33_sound component54Node40_sound

private noncomputable def component54Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component54Node42_sound : Sound component54Node42Box :=
  sound_of_literal_split component54Node42Box component54Node26Box component54Node41Box
    .k (57/16) (by rfl) (by rfl)
    component54Node26_sound component54Node41_sound

noncomputable def component54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
theorem component54_sound : Sound component54Box :=
  sound_of_literal_split component54Box component54Node15Box component54Node42Box
    .chi (9/64) (by rfl) (by rfl)
    component54Node15_sound component54Node42_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
