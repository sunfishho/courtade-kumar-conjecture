import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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

private noncomputable def leaf3660Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3660Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905645056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (209677647/134217728) }, upper := { exponent := 0, mantissa := (3289/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811809621/45811290112) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3660InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf3660LocalValidity :
    LeafFacts leaf3660Box leaf3660Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3660Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905645056) }) = true
      norm_num [leaf3660Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3660CertificateValid :
    WideCertificateValid leaf3660Box leaf3660Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi54ValidityFacts
    leaf3660LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3660CoverageChecked :
    coverageCheck (innerAD leaf3660Box) leaf3660InnerLog = true := by
  rfl'

private theorem leaf3660InnerLogValid :
    leaf3660InnerLog.Valid 8 (innerAD leaf3660Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf3660CoverageChecked

private noncomputable def leaf3660InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3660InputLogOnePlusV_eq :
    leaf3660InputLogOnePlusV = outerEnclosure 24
      (leaf3660Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3660RoundedFacts : LeafRoundedFacts 8
    leaf3660Certificate.logOnePlusV leaf3660InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3660InputLogOnePlusV_eq }

private noncomputable def leaf3660Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi54InputQChi innerPair41Input
    leaf3660InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3660LowerChecked :
    lowerCheck 24 leaf3660Box leaf3660Inputs = true := by
  rfl'

private theorem leaf3660CoversExact : CoversExact 8
    leaf3660Box leaf3660Certificate leaf3660InnerLog leaf3660Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi54RoundedFacts
    innerPair41RoundedFacts leaf3660RoundedFacts (by rfl)

private theorem leaf3660FlatSound : Sound leaf3660Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3660CertificateValid
    leaf3660InnerLogValid leaf3660CoversExact leaf3660LowerChecked

private noncomputable def leaf3661Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3661Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716900352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (210726157/134217728) }, upper := { exponent := 0, mantissa := (1653/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435394047/137433800704) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3661InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf3661LocalValidity :
    LeafFacts leaf3661Box leaf3661Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3661Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716900352) }) = true
      norm_num [leaf3661Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3661CertificateValid :
    WideCertificateValid leaf3661Box leaf3661Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi54ValidityFacts
    leaf3661LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3661CoverageChecked :
    coverageCheck (innerAD leaf3661Box) leaf3661InnerLog = true := by
  rfl'

private theorem leaf3661InnerLogValid :
    leaf3661InnerLog.Valid 8 (innerAD leaf3661Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf3661CoverageChecked

private noncomputable def leaf3661InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3661InputLogOnePlusV_eq :
    leaf3661InputLogOnePlusV = outerEnclosure 24
      (leaf3661Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3661RoundedFacts : LeafRoundedFacts 8
    leaf3661Certificate.logOnePlusV leaf3661InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3661InputLogOnePlusV_eq }

private noncomputable def leaf3661Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi54InputQChi innerPair50Input
    leaf3661InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3661LowerChecked :
    lowerCheck 24 leaf3661Box leaf3661Inputs = true := by
  rfl'

private theorem leaf3661CoversExact : CoversExact 8
    leaf3661Box leaf3661Certificate leaf3661InnerLog leaf3661Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi54RoundedFacts
    innerPair50RoundedFacts leaf3661RoundedFacts (by rfl)

private theorem leaf3661FlatSound : Sound leaf3661Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3661CertificateValid
    leaf3661InnerLogValid leaf3661CoversExact leaf3661LowerChecked

private noncomputable def leaf3662Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3662Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716785664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (214395949/134217728) }, upper := { exponent := 0, mantissa := (1681/1024) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435279359/137433571328) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3662InnerLog : WideLogData :=
  innerPair158Data

set_option maxRecDepth 1000000 in
private theorem leaf3662LocalValidity :
    LeafFacts leaf3662Box leaf3662Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3662Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716785664) }) = true
      norm_num [leaf3662Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3662CertificateValid :
    WideCertificateValid leaf3662Box leaf3662Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi55ValidityFacts
    leaf3662LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3662CoverageChecked :
    coverageCheck (innerAD leaf3662Box) leaf3662InnerLog = true := by
  rfl'

private theorem leaf3662InnerLogValid :
    leaf3662InnerLog.Valid 8 (innerAD leaf3662Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint48PositiveFacts.valid leaf3662CoverageChecked

private noncomputable def leaf3662InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3662InputLogOnePlusV_eq :
    leaf3662InputLogOnePlusV = outerEnclosure 24
      (leaf3662Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3662RoundedFacts : LeafRoundedFacts 8
    leaf3662Certificate.logOnePlusV leaf3662InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3662InputLogOnePlusV_eq }

private noncomputable def leaf3662Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi55InputQChi innerPair158Input
    leaf3662InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3662LowerChecked :
    lowerCheck 24 leaf3662Box leaf3662Inputs = true := by
  rfl'

private theorem leaf3662CoversExact : CoversExact 8
    leaf3662Box leaf3662Certificate leaf3662InnerLog leaf3662Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi55RoundedFacts
    innerPair158RoundedFacts leaf3662RoundedFacts (by rfl)

private theorem leaf3662FlatSound : Sound leaf3662Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3662CertificateValid
    leaf3662InnerLogValid leaf3662CoversExact leaf3662LowerChecked

private noncomputable def leaf3663Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3663Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743349760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (215509991/134217728) }, upper := { exponent := 0, mantissa := (845/512) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487048499/27486699520) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3663InnerLog : WideLogData :=
  innerPair158Data

set_option maxRecDepth 1000000 in
private theorem leaf3663LocalValidity :
    LeafFacts leaf3663Box leaf3663Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3663Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743349760) }) = true
      norm_num [leaf3663Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3663CertificateValid :
    WideCertificateValid leaf3663Box leaf3663Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi55ValidityFacts
    leaf3663LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3663CoverageChecked :
    coverageCheck (innerAD leaf3663Box) leaf3663InnerLog = true := by
  rfl'

private theorem leaf3663InnerLogValid :
    leaf3663InnerLog.Valid 8 (innerAD leaf3663Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint48PositiveFacts.valid leaf3663CoverageChecked

private noncomputable def leaf3663InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3663InputLogOnePlusV_eq :
    leaf3663InputLogOnePlusV = outerEnclosure 24
      (leaf3663Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3663RoundedFacts : LeafRoundedFacts 8
    leaf3663Certificate.logOnePlusV leaf3663InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3663InputLogOnePlusV_eq }

private noncomputable def leaf3663Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi55InputQChi innerPair158Input
    leaf3663InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3663LowerChecked :
    lowerCheck 24 leaf3663Box leaf3663Inputs = true := by
  rfl'

private theorem leaf3663CoversExact : CoversExact 8
    leaf3663Box leaf3663Certificate leaf3663InnerLog leaf3663Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi55RoundedFacts
    innerPair158RoundedFacts leaf3663RoundedFacts (by rfl)

private theorem leaf3663FlatSound : Sound leaf3663Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3663CertificateValid
    leaf3663InnerLogValid leaf3663CoversExact leaf3663LowerChecked

private noncomputable def leaf3664Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3664Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716865536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (211774667/134217728) }, upper := { exponent := 0, mantissa := (3323/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435359231/137433731072) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3664InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf3664LocalValidity :
    LeafFacts leaf3664Box leaf3664Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3664Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716865536) }) = true
      norm_num [leaf3664Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3664CertificateValid :
    WideCertificateValid leaf3664Box leaf3664Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi54ValidityFacts
    leaf3664LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3664CoverageChecked :
    coverageCheck (innerAD leaf3664Box) leaf3664InnerLog = true := by
  rfl'

private theorem leaf3664InnerLogValid :
    leaf3664InnerLog.Valid 8 (innerAD leaf3664Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf3664CoverageChecked

private noncomputable def leaf3664InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3664InputLogOnePlusV_eq :
    leaf3664InputLogOnePlusV = outerEnclosure 24
      (leaf3664Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3664RoundedFacts : LeafRoundedFacts 8
    leaf3664Certificate.logOnePlusV leaf3664InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3664InputLogOnePlusV_eq }

private noncomputable def leaf3664Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi54InputQChi innerPair50Input
    leaf3664InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3664LowerChecked :
    lowerCheck 24 leaf3664Box leaf3664Inputs = true := by
  rfl'

private theorem leaf3664CoversExact : CoversExact 8
    leaf3664Box leaf3664Certificate leaf3664InnerLog leaf3664Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi54RoundedFacts
    innerPair50RoundedFacts leaf3664RoundedFacts (by rfl)

private theorem leaf3664FlatSound : Sound leaf3664Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3664CertificateValid
    leaf3664InnerLogValid leaf3664CoversExact leaf3664LowerChecked

private noncomputable def leaf3665Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3665Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581122048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (212823177/134217728) }, upper := { exponent := 0, mantissa := (835/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162354961/9162244096) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3665InnerLog : WideLogData :=
  innerPair170Data

set_option maxRecDepth 1000000 in
private theorem leaf3665LocalValidity :
    LeafFacts leaf3665Box leaf3665Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3665Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581122048) }) = true
      norm_num [leaf3665Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3665CertificateValid :
    WideCertificateValid leaf3665Box leaf3665Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi54ValidityFacts
    leaf3665LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3665CoverageChecked :
    coverageCheck (innerAD leaf3665Box) leaf3665InnerLog = true := by
  rfl'

private theorem leaf3665InnerLogValid :
    leaf3665InnerLog.Valid 8 (innerAD leaf3665Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint45PositiveFacts.valid leaf3665CoverageChecked

private noncomputable def leaf3665InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3665InputLogOnePlusV_eq :
    leaf3665InputLogOnePlusV = outerEnclosure 24
      (leaf3665Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3665RoundedFacts : LeafRoundedFacts 8
    leaf3665Certificate.logOnePlusV leaf3665InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3665InputLogOnePlusV_eq }

private noncomputable def leaf3665Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi54InputQChi innerPair170Input
    leaf3665InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3665LowerChecked :
    lowerCheck 24 leaf3665Box leaf3665Inputs = true := by
  rfl'

private theorem leaf3665CoversExact : CoversExact 8
    leaf3665Box leaf3665Certificate leaf3665InnerLog leaf3665Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi54RoundedFacts
    innerPair170RoundedFacts leaf3665RoundedFacts (by rfl)

private theorem leaf3665FlatSound : Sound leaf3665Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3665CertificateValid
    leaf3665InnerLogValid leaf3665CoversExact leaf3665LowerChecked

private noncomputable def leaf3666Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3666Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716711936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (216624033/134217728) }, upper := { exponent := 0, mantissa := (1699/1024) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435205631/137433423872) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3666InnerLog : WideLogData :=
  innerPair168Data

set_option maxRecDepth 1000000 in
private theorem leaf3666LocalValidity :
    LeafFacts leaf3666Box leaf3666Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3666Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716711936) }) = true
      norm_num [leaf3666Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3666CertificateValid :
    WideCertificateValid leaf3666Box leaf3666Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi55ValidityFacts
    leaf3666LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3666CoverageChecked :
    coverageCheck (innerAD leaf3666Box) leaf3666InnerLog = true := by
  rfl'

private theorem leaf3666InnerLogValid :
    leaf3666InnerLog.Valid 8 (innerAD leaf3666Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint133PositiveFacts.valid leaf3666CoverageChecked

private noncomputable def leaf3666InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3666InputLogOnePlusV_eq :
    leaf3666InputLogOnePlusV = outerEnclosure 24
      (leaf3666Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3666RoundedFacts : LeafRoundedFacts 8
    leaf3666Certificate.logOnePlusV leaf3666InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3666InputLogOnePlusV_eq }

private noncomputable def leaf3666Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi55InputQChi innerPair168Input
    leaf3666InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3666LowerChecked :
    lowerCheck 24 leaf3666Box leaf3666Inputs = true := by
  rfl'

private theorem leaf3666CoversExact : CoversExact 8
    leaf3666Box leaf3666Certificate leaf3666InnerLog leaf3666Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi55RoundedFacts
    innerPair168RoundedFacts leaf3666RoundedFacts (by rfl)

private theorem leaf3666FlatSound : Sound leaf3666Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3666CertificateValid
    leaf3666InnerLogValid leaf3666CoversExact leaf3666LowerChecked

private noncomputable def leaf3667Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3667Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716675072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (217738075/134217728) }, upper := { exponent := 0, mantissa := (427/256) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435168767/137433350144) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3667InnerLog : WideLogData :=
  innerPair168Data

set_option maxRecDepth 1000000 in
private theorem leaf3667LocalValidity :
    LeafFacts leaf3667Box leaf3667Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3667Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716675072) }) = true
      norm_num [leaf3667Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3667CertificateValid :
    WideCertificateValid leaf3667Box leaf3667Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi55ValidityFacts
    leaf3667LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3667CoverageChecked :
    coverageCheck (innerAD leaf3667Box) leaf3667InnerLog = true := by
  rfl'

private theorem leaf3667InnerLogValid :
    leaf3667InnerLog.Valid 8 (innerAD leaf3667Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint133PositiveFacts.valid leaf3667CoverageChecked

private noncomputable def leaf3667InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3667InputLogOnePlusV_eq :
    leaf3667InputLogOnePlusV = outerEnclosure 24
      (leaf3667Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3667RoundedFacts : LeafRoundedFacts 8
    leaf3667Certificate.logOnePlusV leaf3667InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3667InputLogOnePlusV_eq }

private noncomputable def leaf3667Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi55InputQChi innerPair168Input
    leaf3667InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3667LowerChecked :
    lowerCheck 24 leaf3667Box leaf3667Inputs = true := by
  rfl'

private theorem leaf3667CoversExact : CoversExact 8
    leaf3667Box leaf3667Certificate leaf3667InnerLog leaf3667Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi55RoundedFacts
    innerPair168RoundedFacts leaf3667RoundedFacts (by rfl)

private theorem leaf3667FlatSound : Sound leaf3667Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3667CertificateValid
    leaf3667InnerLogValid leaf3667CoversExact leaf3667LowerChecked

private noncomputable def leaf3668Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3668Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743327232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (219114251/134217728) }, upper := { exponent := 0, mantissa := (3435/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487025971/27486654464) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3668InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3668LocalValidity :
    LeafFacts leaf3668Box leaf3668Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3668Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743327232) }) = true
      norm_num [leaf3668Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3668CertificateValid :
    WideCertificateValid leaf3668Box leaf3668Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi56ValidityFacts
    leaf3668LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3668CoverageChecked :
    coverageCheck (innerAD leaf3668Box) leaf3668InnerLog = true := by
  rfl'

private theorem leaf3668InnerLogValid :
    leaf3668InnerLog.Valid 8 (innerAD leaf3668Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3668CoverageChecked

private noncomputable def leaf3668InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3668InputLogOnePlusV_eq :
    leaf3668InputLogOnePlusV = outerEnclosure 24
      (leaf3668Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3668RoundedFacts : LeafRoundedFacts 8
    leaf3668Certificate.logOnePlusV leaf3668InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3668InputLogOnePlusV_eq }

private noncomputable def leaf3668Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi56InputQChi innerPair56Input
    leaf3668InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3668LowerChecked :
    lowerCheck 24 leaf3668Box leaf3668Inputs = true := by
  rfl'

private theorem leaf3668CoversExact : CoversExact 8
    leaf3668Box leaf3668Certificate leaf3668InnerLog leaf3668Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi56RoundedFacts
    innerPair56RoundedFacts leaf3668RoundedFacts (by rfl)

private theorem leaf3668FlatSound : Sound leaf3668Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3668CertificateValid
    leaf3668InnerLogValid leaf3668CoversExact leaf3668LowerChecked

private noncomputable def leaf3669Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3669Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905532416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (220293825/134217728) }, upper := { exponent := 0, mantissa := (1727/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811696981/45811064832) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3669InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3669LocalValidity :
    LeafFacts leaf3669Box leaf3669Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3669Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905532416) }) = true
      norm_num [leaf3669Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3669CertificateValid :
    WideCertificateValid leaf3669Box leaf3669Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi56ValidityFacts
    leaf3669LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3669CoverageChecked :
    coverageCheck (innerAD leaf3669Box) leaf3669InnerLog = true := by
  rfl'

private theorem leaf3669InnerLogValid :
    leaf3669InnerLog.Valid 8 (innerAD leaf3669Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3669CoverageChecked

private noncomputable def leaf3669InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf3669InputLogOnePlusV_eq :
    leaf3669InputLogOnePlusV = outerEnclosure 24
      (leaf3669Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3669RoundedFacts : LeafRoundedFacts 8
    leaf3669Certificate.logOnePlusV leaf3669InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3669InputLogOnePlusV_eq }

private noncomputable def leaf3669Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi56InputQChi innerPair56Input
    leaf3669InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3669LowerChecked :
    lowerCheck 24 leaf3669Box leaf3669Inputs = true := by
  rfl'

private theorem leaf3669CoversExact : CoversExact 8
    leaf3669Box leaf3669Certificate leaf3669InnerLog leaf3669Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi56RoundedFacts
    innerPair56RoundedFacts leaf3669RoundedFacts (by rfl)

private theorem leaf3669FlatSound : Sound leaf3669Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3669CertificateValid
    leaf3669InnerLogValid leaf3669CoversExact leaf3669LowerChecked

private noncomputable def leaf3670Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3670Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905495552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (223832553/134217728) }, upper := { exponent := 0, mantissa := (877/512) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811660117/45810991104) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3670InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3670LocalValidity :
    LeafFacts leaf3670Box leaf3670Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3670Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905495552) }) = true
      norm_num [leaf3670Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3670CertificateValid :
    WideCertificateValid leaf3670Box leaf3670Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi57ValidityFacts
    leaf3670LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3670CoverageChecked :
    coverageCheck (innerAD leaf3670Box) leaf3670InnerLog = true := by
  rfl'

private theorem leaf3670InnerLogValid :
    leaf3670InnerLog.Valid 8 (innerAD leaf3670Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3670CoverageChecked

private noncomputable def leaf3670InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3670InputLogOnePlusV_eq :
    leaf3670InputLogOnePlusV = outerEnclosure 24
      (leaf3670Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3670RoundedFacts : LeafRoundedFacts 8
    leaf3670Certificate.logOnePlusV leaf3670InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3670InputLogOnePlusV_eq }

private noncomputable def leaf3670Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi57InputQChi innerPair57Input
    leaf3670InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3670LowerChecked :
    lowerCheck 24 leaf3670Box leaf3670Inputs = true := by
  rfl'

private theorem leaf3670CoversExact : CoversExact 8
    leaf3670Box leaf3670Certificate leaf3670InnerLog leaf3670Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi57RoundedFacts
    innerPair57RoundedFacts leaf3670RoundedFacts (by rfl)

private theorem leaf3670FlatSound : Sound leaf3670Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3670CertificateValid
    leaf3670InnerLogValid leaf3670CoversExact leaf3670LowerChecked

private noncomputable def leaf3671Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3671Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716445696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (225077659/134217728) }, upper := { exponent := 0, mantissa := (441/256) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434939391/137432891392) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3671InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3671LocalValidity :
    LeafFacts leaf3671Box leaf3671Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3671Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716445696) }) = true
      norm_num [leaf3671Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3671CertificateValid :
    WideCertificateValid leaf3671Box leaf3671Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi57ValidityFacts
    leaf3671LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3671CoverageChecked :
    coverageCheck (innerAD leaf3671Box) leaf3671InnerLog = true := by
  rfl'

private theorem leaf3671InnerLogValid :
    leaf3671InnerLog.Valid 8 (innerAD leaf3671Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3671CoverageChecked

private noncomputable def leaf3671InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3671InputLogOnePlusV_eq :
    leaf3671InputLogOnePlusV = outerEnclosure 24
      (leaf3671Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3671RoundedFacts : LeafRoundedFacts 8
    leaf3671Certificate.logOnePlusV leaf3671InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3671InputLogOnePlusV_eq }

private noncomputable def leaf3671Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi57InputQChi innerPair57Input
    leaf3671InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3671LowerChecked :
    lowerCheck 24 leaf3671Box leaf3671Inputs = true := by
  rfl'

private theorem leaf3671CoversExact : CoversExact 8
    leaf3671Box leaf3671Certificate leaf3671InnerLog leaf3671Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi57RoundedFacts
    innerPair57RoundedFacts leaf3671RoundedFacts (by rfl)

private theorem leaf3671FlatSound : Sound leaf3671Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3671CertificateValid
    leaf3671InnerLogValid leaf3671CoversExact leaf3671LowerChecked

private noncomputable def leaf3672Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3672Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716558336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (221473399/134217728) }, upper := { exponent := 0, mantissa := (3473/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435052031/137433116672) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3672InnerLog : WideLogData :=
  innerPair160Data

set_option maxRecDepth 1000000 in
private theorem leaf3672LocalValidity :
    LeafFacts leaf3672Box leaf3672Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3672Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716558336) }) = true
      norm_num [leaf3672Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3672CertificateValid :
    WideCertificateValid leaf3672Box leaf3672Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi56ValidityFacts
    leaf3672LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3672CoverageChecked :
    coverageCheck (innerAD leaf3672Box) leaf3672InnerLog = true := by
  rfl'

private theorem leaf3672InnerLogValid :
    leaf3672InnerLog.Valid 8 (innerAD leaf3672Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint20PositiveFacts.valid leaf3672CoverageChecked

private noncomputable def leaf3672InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3672InputLogOnePlusV_eq :
    leaf3672InputLogOnePlusV = outerEnclosure 24
      (leaf3672Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3672RoundedFacts : LeafRoundedFacts 8
    leaf3672Certificate.logOnePlusV leaf3672InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3672InputLogOnePlusV_eq }

private noncomputable def leaf3672Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi56InputQChi innerPair160Input
    leaf3672InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3672LowerChecked :
    lowerCheck 24 leaf3672Box leaf3672Inputs = true := by
  rfl'

private theorem leaf3672CoversExact : CoversExact 8
    leaf3672Box leaf3672Certificate leaf3672InnerLog leaf3672Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi56RoundedFacts
    innerPair160RoundedFacts leaf3672RoundedFacts (by rfl)

private theorem leaf3672FlatSound : Sound leaf3672Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3672CertificateValid
    leaf3672InnerLogValid leaf3672CoversExact leaf3672LowerChecked

private noncomputable def leaf3673Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3673Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716519424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (222652973/134217728) }, upper := { exponent := 0, mantissa := (873/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435013119/137433038848) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3673InnerLog : WideLogData :=
  innerPair175Data

set_option maxRecDepth 1000000 in
private theorem leaf3673LocalValidity :
    LeafFacts leaf3673Box leaf3673Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3673Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716519424) }) = true
      norm_num [leaf3673Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3673CertificateValid :
    WideCertificateValid leaf3673Box leaf3673Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi56ValidityFacts
    leaf3673LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3673CoverageChecked :
    coverageCheck (innerAD leaf3673Box) leaf3673InnerLog = true := by
  rfl'

private theorem leaf3673InnerLogValid :
    leaf3673InnerLog.Valid 8 (innerAD leaf3673Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint62PositiveFacts.valid leaf3673CoverageChecked

private noncomputable def leaf3673InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3673InputLogOnePlusV_eq :
    leaf3673InputLogOnePlusV = outerEnclosure 24
      (leaf3673Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3673RoundedFacts : LeafRoundedFacts 8
    leaf3673Certificate.logOnePlusV leaf3673InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3673InputLogOnePlusV_eq }

private noncomputable def leaf3673Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi56InputQChi innerPair175Input
    leaf3673InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3673LowerChecked :
    lowerCheck 24 leaf3673Box leaf3673Inputs = true := by
  rfl'

private theorem leaf3673CoversExact : CoversExact 8
    leaf3673Box leaf3673Certificate leaf3673InnerLog leaf3673Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi56RoundedFacts
    innerPair175RoundedFacts leaf3673RoundedFacts (by rfl)

private theorem leaf3673FlatSound : Sound leaf3673Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3673CertificateValid
    leaf3673InnerLogValid leaf3673CoversExact leaf3673LowerChecked

private noncomputable def leaf3674Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3674Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716404736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (226322765/134217728) }, upper := { exponent := 0, mantissa := (887/512) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434898431/137432809472) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3674InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3674LocalValidity :
    LeafFacts leaf3674Box leaf3674Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3674Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716404736) }) = true
      norm_num [leaf3674Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3674CertificateValid :
    WideCertificateValid leaf3674Box leaf3674Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi57ValidityFacts
    leaf3674LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3674CoverageChecked :
    coverageCheck (innerAD leaf3674Box) leaf3674InnerLog = true := by
  rfl'

private theorem leaf3674InnerLogValid :
    leaf3674InnerLog.Valid 8 (innerAD leaf3674Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3674CoverageChecked

private noncomputable def leaf3674InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3674InputLogOnePlusV_eq :
    leaf3674InputLogOnePlusV = outerEnclosure 24
      (leaf3674Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3674RoundedFacts : LeafRoundedFacts 8
    leaf3674Certificate.logOnePlusV leaf3674InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3674InputLogOnePlusV_eq }

private noncomputable def leaf3674Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi57InputQChi innerPair57Input
    leaf3674InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3674LowerChecked :
    lowerCheck 24 leaf3674Box leaf3674Inputs = true := by
  rfl'

private theorem leaf3674CoversExact : CoversExact 8
    leaf3674Box leaf3674Certificate leaf3674InnerLog leaf3674Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi57RoundedFacts
    innerPair57RoundedFacts leaf3674RoundedFacts (by rfl)

private theorem leaf3674FlatSound : Sound leaf3674Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3674CertificateValid
    leaf3674InnerLogValid leaf3674CoversExact leaf3674LowerChecked

private noncomputable def leaf3675Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3675Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905454592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (227567871/134217728) }, upper := { exponent := 0, mantissa := (223/128) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811619157/45810909184) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3675InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3675LocalValidity :
    LeafFacts leaf3675Box leaf3675Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3675Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905454592) }) = true
      norm_num [leaf3675Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3675CertificateValid :
    WideCertificateValid leaf3675Box leaf3675Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi57ValidityFacts
    leaf3675LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3675CoverageChecked :
    coverageCheck (innerAD leaf3675Box) leaf3675InnerLog = true := by
  rfl'

private theorem leaf3675InnerLogValid :
    leaf3675InnerLog.Valid 8 (innerAD leaf3675Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3675CoverageChecked

private noncomputable def leaf3675InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3675InputLogOnePlusV_eq :
    leaf3675InputLogOnePlusV = outerEnclosure 24
      (leaf3675Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3675RoundedFacts : LeafRoundedFacts 8
    leaf3675Certificate.logOnePlusV leaf3675InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3675InputLogOnePlusV_eq }

private noncomputable def leaf3675Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi57InputQChi innerPair64Input
    leaf3675InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3675LowerChecked :
    lowerCheck 24 leaf3675Box leaf3675Inputs = true := by
  rfl'

private theorem leaf3675CoversExact : CoversExact 8
    leaf3675Box leaf3675Certificate leaf3675InnerLog leaf3675Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi57RoundedFacts
    innerPair64RoundedFacts leaf3675RoundedFacts (by rfl)

private theorem leaf3675FlatSound : Sound leaf3675Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3675CertificateValid
    leaf3675InnerLogValid leaf3675CoversExact leaf3675LowerChecked

private noncomputable def leaf3676Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf3676Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716795904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (213871687/134217728) }, upper := { exponent := 0, mantissa := (3357/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435289599/137433591808) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3676InnerLog : WideLogData :=
  innerPair170Data

set_option maxRecDepth 1000000 in
private theorem leaf3676LocalValidity :
    LeafFacts leaf3676Box leaf3676Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3676Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716795904) }) = true
      norm_num [leaf3676Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3676CertificateValid :
    WideCertificateValid leaf3676Box leaf3676Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi54ValidityFacts
    leaf3676LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3676CoverageChecked :
    coverageCheck (innerAD leaf3676Box) leaf3676InnerLog = true := by
  rfl'

private theorem leaf3676InnerLogValid :
    leaf3676InnerLog.Valid 8 (innerAD leaf3676Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint45PositiveFacts.valid leaf3676CoverageChecked

private noncomputable def leaf3676InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3676InputLogOnePlusV_eq :
    leaf3676InputLogOnePlusV = outerEnclosure 24
      (leaf3676Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3676RoundedFacts : LeafRoundedFacts 8
    leaf3676Certificate.logOnePlusV leaf3676InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3676InputLogOnePlusV_eq }

private noncomputable def leaf3676Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi54InputQChi innerPair170Input
    leaf3676InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3676LowerChecked :
    lowerCheck 24 leaf3676Box leaf3676Inputs = true := by
  rfl'

private theorem leaf3676CoversExact : CoversExact 8
    leaf3676Box leaf3676Certificate leaf3676InnerLog leaf3676Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi54RoundedFacts
    innerPair170RoundedFacts leaf3676RoundedFacts (by rfl)

private theorem leaf3676FlatSound : Sound leaf3676Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3676CertificateValid
    leaf3676InnerLogValid leaf3676CoversExact leaf3676LowerChecked

private noncomputable def leaf3677Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3677Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743368192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (429873317/268435456) }, upper := { exponent := 0, mantissa := (3335/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487066931/27486736384) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3677InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3677LocalValidity :
    LeafFacts leaf3677Box leaf3677Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3677Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743368192) }) = true
      norm_num [leaf3677Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3677CertificateValid :
    WideCertificateValid leaf3677Box leaf3677Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi241ValidityFacts
    leaf3677LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3677CoverageChecked :
    coverageCheck (innerAD leaf3677Box) leaf3677InnerLog = true := by
  rfl'

private theorem leaf3677InnerLogValid :
    leaf3677InnerLog.Valid 8 (innerAD leaf3677Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3677CoverageChecked

private noncomputable def leaf3677InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3677InputLogOnePlusV_eq :
    leaf3677InputLogOnePlusV = outerEnclosure 24
      (leaf3677Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3677RoundedFacts : LeafRoundedFacts 8
    leaf3677Certificate.logOnePlusV leaf3677InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3677InputLogOnePlusV_eq }

private noncomputable def leaf3677Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi241InputQChi innerPair51Input
    leaf3677InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3677LowerChecked :
    lowerCheck 24 leaf3677Box leaf3677Inputs = true := by
  rfl'

private theorem leaf3677CoversExact : CoversExact 8
    leaf3677Box leaf3677Certificate leaf3677InnerLog leaf3677Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi241RoundedFacts
    innerPair51RoundedFacts leaf3677RoundedFacts (by rfl)

private theorem leaf3677FlatSound : Sound leaf3677Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3677CertificateValid
    leaf3677InnerLogValid leaf3677CoversExact leaf3677LowerChecked

private noncomputable def leaf3678Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3678Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716761088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (434919279/268435456) }, upper := { exponent := 0, mantissa := (1687/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435254783/137433522176) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3678InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3678LocalValidity :
    LeafFacts leaf3678Box leaf3678Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3678Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716761088) }) = true
      norm_num [leaf3678Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3678CertificateValid :
    WideCertificateValid leaf3678Box leaf3678Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi242ValidityFacts
    leaf3678LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3678CoverageChecked :
    coverageCheck (innerAD leaf3678Box) leaf3678InnerLog = true := by
  rfl'

private theorem leaf3678InnerLogValid :
    leaf3678InnerLog.Valid 8 (innerAD leaf3678Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3678CoverageChecked

private noncomputable def leaf3678InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3678InputLogOnePlusV_eq :
    leaf3678InputLogOnePlusV = outerEnclosure 24
      (leaf3678Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3678RoundedFacts : LeafRoundedFacts 8
    leaf3678Certificate.logOnePlusV leaf3678InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3678InputLogOnePlusV_eq }

private noncomputable def leaf3678Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi242InputQChi innerPair51Input
    leaf3678InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3678LowerChecked :
    lowerCheck 24 leaf3678Box leaf3678Inputs = true := by
  rfl'

private theorem leaf3678CoversExact : CoversExact 8
    leaf3678Box leaf3678Certificate leaf3678InnerLog leaf3678Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi242RoundedFacts
    innerPair51RoundedFacts leaf3678RoundedFacts (by rfl)

private theorem leaf3678FlatSound : Sound leaf3678Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3678CertificateValid
    leaf3678InnerLogValid leaf3678CoversExact leaf3678LowerChecked

private noncomputable def leaf3679Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf3679Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716638208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (218852117/134217728) }, upper := { exponent := 0, mantissa := (1717/1024) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435131903/137433276416) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3679InnerLog : WideLogData :=
  innerPair416Data

set_option maxRecDepth 1000000 in
private theorem leaf3679LocalValidity :
    LeafFacts leaf3679Box leaf3679Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3679Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716638208) }) = true
      norm_num [leaf3679Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3679CertificateValid :
    WideCertificateValid leaf3679Box leaf3679Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi55ValidityFacts
    leaf3679LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3679CoverageChecked :
    coverageCheck (innerAD leaf3679Box) leaf3679InnerLog = true := by
  rfl'

private theorem leaf3679InnerLogValid :
    leaf3679InnerLog.Valid 8 (innerAD leaf3679Box) :=
  wideLogDataValid_of_cachedCheck endpoint126PositiveFacts
    endpoint59PositiveFacts.valid leaf3679CoverageChecked

private noncomputable def leaf3679InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3679InputLogOnePlusV_eq :
    leaf3679InputLogOnePlusV = outerEnclosure 24
      (leaf3679Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3679RoundedFacts : LeafRoundedFacts 8
    leaf3679Certificate.logOnePlusV leaf3679InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3679InputLogOnePlusV_eq }

private noncomputable def leaf3679Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi55InputQChi innerPair416Input
    leaf3679InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3679LowerChecked :
    lowerCheck 24 leaf3679Box leaf3679Inputs = true := by
  rfl'

private theorem leaf3679CoversExact : CoversExact 8
    leaf3679Box leaf3679Certificate leaf3679InnerLog leaf3679Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi55RoundedFacts
    innerPair416RoundedFacts leaf3679RoundedFacts (by rfl)

private theorem leaf3679FlatSound : Sound leaf3679Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3679CertificateValid
    leaf3679InnerLogValid leaf3679CoversExact leaf3679LowerChecked

private noncomputable def leaf3680Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3680Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716681216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (439965241/268435456) }, upper := { exponent := 0, mantissa := (3413/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435174911/137433362432) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3680InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3680LocalValidity :
    LeafFacts leaf3680Box leaf3680Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3680Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716681216) }) = true
      norm_num [leaf3680Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3680CertificateValid :
    WideCertificateValid leaf3680Box leaf3680Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi243ValidityFacts
    leaf3680LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3680CoverageChecked :
    coverageCheck (innerAD leaf3680Box) leaf3680InnerLog = true := by
  rfl'

private theorem leaf3680InnerLogValid :
    leaf3680InnerLog.Valid 8 (innerAD leaf3680Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3680CoverageChecked

private noncomputable def leaf3680InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3680InputLogOnePlusV_eq :
    leaf3680InputLogOnePlusV = outerEnclosure 24
      (leaf3680Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3680RoundedFacts : LeafRoundedFacts 8
    leaf3680Certificate.logOnePlusV leaf3680InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3680InputLogOnePlusV_eq }

private noncomputable def leaf3680Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi243InputQChi innerPair56Input
    leaf3680InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3680LowerChecked :
    lowerCheck 24 leaf3680Box leaf3680Inputs = true := by
  rfl'

private theorem leaf3680CoversExact : CoversExact 8
    leaf3680Box leaf3680Certificate leaf3680InnerLog leaf3680Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi243RoundedFacts
    innerPair56RoundedFacts leaf3680RoundedFacts (by rfl)

private theorem leaf3680FlatSound : Sound leaf3680Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3680CertificateValid
    leaf3680InnerLogValid leaf3680CoversExact leaf3680LowerChecked

private noncomputable def leaf3681Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3681Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716601344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (445011203/268435456) }, upper := { exponent := 0, mantissa := (863/512) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435095039/137433202688) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3681InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3681LocalValidity :
    LeafFacts leaf3681Box leaf3681Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3681Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716601344) }) = true
      norm_num [leaf3681Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3681CertificateValid :
    WideCertificateValid leaf3681Box leaf3681Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi244ValidityFacts
    leaf3681LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3681CoverageChecked :
    coverageCheck (innerAD leaf3681Box) leaf3681InnerLog = true := by
  rfl'

private theorem leaf3681InnerLogValid :
    leaf3681InnerLog.Valid 8 (innerAD leaf3681Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3681CoverageChecked

private noncomputable def leaf3681InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf3681InputLogOnePlusV_eq :
    leaf3681InputLogOnePlusV = outerEnclosure 24
      (leaf3681Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3681RoundedFacts : LeafRoundedFacts 8
    leaf3681Certificate.logOnePlusV leaf3681InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3681InputLogOnePlusV_eq }

private noncomputable def leaf3681Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi244InputQChi innerPair56Input
    leaf3681InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3681LowerChecked :
    lowerCheck 24 leaf3681Box leaf3681Inputs = true := by
  rfl'

private theorem leaf3681CoversExact : CoversExact 8
    leaf3681Box leaf3681Certificate leaf3681InnerLog leaf3681Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi244RoundedFacts
    innerPair56RoundedFacts leaf3681RoundedFacts (by rfl)

private theorem leaf3681FlatSound : Sound leaf3681Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3681CertificateValid
    leaf3681InnerLogValid leaf3681CoversExact leaf3681LowerChecked

private noncomputable def leaf3682Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3682Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716807168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (431970339/268435456) }, upper := { exponent := 0, mantissa := (6703/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435300863/137433614336) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3682InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3682LocalValidity :
    LeafFacts leaf3682Box leaf3682Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3682Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716807168) }) = true
      norm_num [leaf3682Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3682CertificateValid :
    WideCertificateValid leaf3682Box leaf3682Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi241ValidityFacts
    leaf3682LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3682CoverageChecked :
    coverageCheck (innerAD leaf3682Box) leaf3682InnerLog = true := by
  rfl'

private theorem leaf3682InnerLogValid :
    leaf3682InnerLog.Valid 8 (innerAD leaf3682Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3682CoverageChecked

private noncomputable def leaf3682InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3682InputLogOnePlusV_eq :
    leaf3682InputLogOnePlusV = outerEnclosure 24
      (leaf3682Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3682RoundedFacts : LeafRoundedFacts 8
    leaf3682Certificate.logOnePlusV leaf3682InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3682InputLogOnePlusV_eq }

private noncomputable def leaf3682Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi241InputQChi innerPair51Input
    leaf3682InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3682LowerChecked :
    lowerCheck 24 leaf3682Box leaf3682Inputs = true := by
  rfl'

private theorem leaf3682CoversExact : CoversExact 8
    leaf3682Box leaf3682Certificate leaf3682InnerLog leaf3682Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi241RoundedFacts
    innerPair51RoundedFacts leaf3682RoundedFacts (by rfl)

private theorem leaf3682FlatSound : Sound leaf3682Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3682CertificateValid
    leaf3682InnerLogValid leaf3682CoversExact leaf3682LowerChecked

private noncomputable def leaf3683Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3683Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905575424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (437081833/268435456) }, upper := { exponent := 0, mantissa := (3391/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811739989/45811150848) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3683InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3683LocalValidity :
    LeafFacts leaf3683Box leaf3683Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3683Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905575424) }) = true
      norm_num [leaf3683Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3683CertificateValid :
    WideCertificateValid leaf3683Box leaf3683Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi242ValidityFacts
    leaf3683LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3683CoverageChecked :
    coverageCheck (innerAD leaf3683Box) leaf3683InnerLog = true := by
  rfl'

private theorem leaf3683InnerLogValid :
    leaf3683InnerLog.Valid 8 (innerAD leaf3683Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3683CoverageChecked

private noncomputable def leaf3683InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3683InputLogOnePlusV_eq :
    leaf3683InputLogOnePlusV = outerEnclosure 24
      (leaf3683Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3683RoundedFacts : LeafRoundedFacts 8
    leaf3683Certificate.logOnePlusV leaf3683InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3683InputLogOnePlusV_eq }

private noncomputable def leaf3683Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi242InputQChi innerPair56Input
    leaf3683InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3683LowerChecked :
    lowerCheck 24 leaf3683Box leaf3683Inputs = true := by
  rfl'

private theorem leaf3683CoversExact : CoversExact 8
    leaf3683Box leaf3683Certificate leaf3683InnerLog leaf3683Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi242RoundedFacts
    innerPair56RoundedFacts leaf3683RoundedFacts (by rfl)

private theorem leaf3683FlatSound : Sound leaf3683Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3683CertificateValid
    leaf3683InnerLogValid leaf3683CoversExact leaf3683LowerChecked

private noncomputable def leaf3684Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (1/4), chiHi := (33/128) }

private noncomputable def leaf3684Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716773376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (434067361/268435456) }, upper := { exponent := 0, mantissa := (421/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi241LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435267071/137433546752) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3684InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf3684LocalValidity :
    LeafFacts leaf3684Box leaf3684Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3684Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716773376) }) = true
      norm_num [leaf3684Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3684CertificateValid :
    WideCertificateValid leaf3684Box leaf3684Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi241ValidityFacts
    leaf3684LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3684CoverageChecked :
    coverageCheck (innerAD leaf3684Box) leaf3684InnerLog = true := by
  rfl'

private theorem leaf3684InnerLogValid :
    leaf3684InnerLog.Valid 8 (innerAD leaf3684Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf3684CoverageChecked

private noncomputable def leaf3684InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3684InputLogOnePlusV_eq :
    leaf3684InputLogOnePlusV = outerEnclosure 24
      (leaf3684Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3684RoundedFacts : LeafRoundedFacts 8
    leaf3684Certificate.logOnePlusV leaf3684InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3684InputLogOnePlusV_eq }

private noncomputable def leaf3684Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi241InputQChi innerPair51Input
    leaf3684InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3684LowerChecked :
    lowerCheck 24 leaf3684Box leaf3684Inputs = true := by
  rfl'

private theorem leaf3684CoversExact : CoversExact 8
    leaf3684Box leaf3684Certificate leaf3684InnerLog leaf3684Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi241RoundedFacts
    innerPair51RoundedFacts leaf3684RoundedFacts (by rfl)

private theorem leaf3684FlatSound : Sound leaf3684Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3684CertificateValid
    leaf3684InnerLogValid leaf3684CoversExact leaf3684LowerChecked

private noncomputable def leaf3685Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (33/128), chiHi := (17/64) }

private noncomputable def leaf3685Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716691456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (439244387/268435456) }, upper := { exponent := 0, mantissa := (213/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi242LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435185151/137433382912) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3685InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3685LocalValidity :
    LeafFacts leaf3685Box leaf3685Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3685Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716691456) }) = true
      norm_num [leaf3685Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3685CertificateValid :
    WideCertificateValid leaf3685Box leaf3685Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi242ValidityFacts
    leaf3685LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3685CoverageChecked :
    coverageCheck (innerAD leaf3685Box) leaf3685InnerLog = true := by
  rfl'

private theorem leaf3685InnerLogValid :
    leaf3685InnerLog.Valid 8 (innerAD leaf3685Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3685CoverageChecked

private noncomputable def leaf3685InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3685InputLogOnePlusV_eq :
    leaf3685InputLogOnePlusV = outerEnclosure 24
      (leaf3685Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3685RoundedFacts : LeafRoundedFacts 8
    leaf3685Certificate.logOnePlusV leaf3685InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3685InputLogOnePlusV_eq }

private noncomputable def leaf3685Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi242InputQChi innerPair56Input
    leaf3685InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3685LowerChecked :
    lowerCheck 24 leaf3685Box leaf3685Inputs = true := by
  rfl'

private theorem leaf3685CoversExact : CoversExact 8
    leaf3685Box leaf3685Certificate leaf3685InnerLog leaf3685Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi242RoundedFacts
    innerPair56RoundedFacts leaf3685RoundedFacts (by rfl)

private theorem leaf3685FlatSound : Sound leaf3685Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3685CertificateValid
    leaf3685InnerLogValid leaf3685CoversExact leaf3685LowerChecked

private noncomputable def leaf3686Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3686Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716645376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (442193327/268435456) }, upper := { exponent := 0, mantissa := (6861/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435139071/137433290752) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3686InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3686LocalValidity :
    LeafFacts leaf3686Box leaf3686Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3686Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716645376) }) = true
      norm_num [leaf3686Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3686CertificateValid :
    WideCertificateValid leaf3686Box leaf3686Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi243ValidityFacts
    leaf3686LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3686CoverageChecked :
    coverageCheck (innerAD leaf3686Box) leaf3686InnerLog = true := by
  rfl'

private theorem leaf3686InnerLogValid :
    leaf3686InnerLog.Valid 8 (innerAD leaf3686Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3686CoverageChecked

private noncomputable def leaf3686InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3686InputLogOnePlusV_eq :
    leaf3686InputLogOnePlusV = outerEnclosure 24
      (leaf3686Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3686RoundedFacts : LeafRoundedFacts 8
    leaf3686Certificate.logOnePlusV leaf3686InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3686InputLogOnePlusV_eq }

private noncomputable def leaf3686Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi243InputQChi innerPair56Input
    leaf3686InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3686LowerChecked :
    lowerCheck 24 leaf3686Box leaf3686Inputs = true := by
  rfl'

private theorem leaf3686CoversExact : CoversExact 8
    leaf3686Box leaf3686Certificate leaf3686InnerLog leaf3686Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi243RoundedFacts
    innerPair56RoundedFacts leaf3686RoundedFacts (by rfl)

private theorem leaf3686FlatSound : Sound leaf3686Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3686CertificateValid
    leaf3686InnerLogValid leaf3686CoversExact leaf3686LowerChecked

private noncomputable def leaf3687Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3687Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743312896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (447304821/268435456) }, upper := { exponent := 0, mantissa := (1735/1024) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487011635/27486625792) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3687InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3687LocalValidity :
    LeafFacts leaf3687Box leaf3687Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3687Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743312896) }) = true
      norm_num [leaf3687Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3687CertificateValid :
    WideCertificateValid leaf3687Box leaf3687Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi244ValidityFacts
    leaf3687LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3687CoverageChecked :
    coverageCheck (innerAD leaf3687Box) leaf3687InnerLog = true := by
  rfl'

private theorem leaf3687InnerLogValid :
    leaf3687InnerLog.Valid 8 (innerAD leaf3687Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3687CoverageChecked

private noncomputable def leaf3687InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3687InputLogOnePlusV_eq :
    leaf3687InputLogOnePlusV = outerEnclosure 24
      (leaf3687Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3687RoundedFacts : LeafRoundedFacts 8
    leaf3687Certificate.logOnePlusV leaf3687InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3687InputLogOnePlusV_eq }

private noncomputable def leaf3687Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi244InputQChi innerPair57Input
    leaf3687InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3687LowerChecked :
    lowerCheck 24 leaf3687Box leaf3687Inputs = true := by
  rfl'

private theorem leaf3687CoversExact : CoversExact 8
    leaf3687Box leaf3687Certificate leaf3687InnerLog leaf3687Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi244RoundedFacts
    innerPair57RoundedFacts leaf3687RoundedFacts (by rfl)

private theorem leaf3687FlatSound : Sound leaf3687Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3687CertificateValid
    leaf3687InnerLogValid leaf3687CoversExact leaf3687LowerChecked

private noncomputable def leaf3688Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (17/64), chiHi := (35/128) }

private noncomputable def leaf3688Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905536512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (444421413/268435456) }, upper := { exponent := 0, mantissa := (431/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi243LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811701077/45811073024) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3688InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3688LocalValidity :
    LeafFacts leaf3688Box leaf3688Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3688Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905536512) }) = true
      norm_num [leaf3688Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3688CertificateValid :
    WideCertificateValid leaf3688Box leaf3688Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi243ValidityFacts
    leaf3688LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3688CoverageChecked :
    coverageCheck (innerAD leaf3688Box) leaf3688InnerLog = true := by
  rfl'

private theorem leaf3688InnerLogValid :
    leaf3688InnerLog.Valid 8 (innerAD leaf3688Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3688CoverageChecked

private noncomputable def leaf3688InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3688InputLogOnePlusV_eq :
    leaf3688InputLogOnePlusV = outerEnclosure 24
      (leaf3688Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3688RoundedFacts : LeafRoundedFacts 8
    leaf3688Certificate.logOnePlusV leaf3688InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3688InputLogOnePlusV_eq }

private noncomputable def leaf3688Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi243InputQChi innerPair56Input
    leaf3688InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3688LowerChecked :
    lowerCheck 24 leaf3688Box leaf3688Inputs = true := by
  rfl'

private theorem leaf3688CoversExact : CoversExact 8
    leaf3688Box leaf3688Certificate leaf3688InnerLog leaf3688Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi243RoundedFacts
    innerPair56RoundedFacts leaf3688RoundedFacts (by rfl)

private theorem leaf3688FlatSound : Sound leaf3688Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3688CertificateValid
    leaf3688InnerLogValid leaf3688CoversExact leaf3688LowerChecked

private noncomputable def leaf3689Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (35/128), chiHi := (9/32) }

private noncomputable def leaf3689Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716527616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (449598439/268435456) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi244LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435021311/137433055232) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3689InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3689LocalValidity :
    LeafFacts leaf3689Box leaf3689Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3689Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716527616) }) = true
      norm_num [leaf3689Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3689CertificateValid :
    WideCertificateValid leaf3689Box leaf3689Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi244ValidityFacts
    leaf3689LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3689CoverageChecked :
    coverageCheck (innerAD leaf3689Box) leaf3689InnerLog = true := by
  rfl'

private theorem leaf3689InnerLogValid :
    leaf3689InnerLog.Valid 8 (innerAD leaf3689Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3689CoverageChecked

private noncomputable def leaf3689InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3689InputLogOnePlusV_eq :
    leaf3689InputLogOnePlusV = outerEnclosure 24
      (leaf3689Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3689RoundedFacts : LeafRoundedFacts 8
    leaf3689Certificate.logOnePlusV leaf3689InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3689InputLogOnePlusV_eq }

private noncomputable def leaf3689Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi244InputQChi innerPair57Input
    leaf3689InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3689LowerChecked :
    lowerCheck 24 leaf3689Box leaf3689Inputs = true := by
  rfl'

private theorem leaf3689CoversExact : CoversExact 8
    leaf3689Box leaf3689Certificate leaf3689InnerLog leaf3689Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi244RoundedFacts
    innerPair57RoundedFacts leaf3689RoundedFacts (by rfl)

private theorem leaf3689FlatSound : Sound leaf3689Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3689CertificateValid
    leaf3689InnerLogValid leaf3689CoversExact leaf3689LowerChecked

private noncomputable def leaf3690Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3690Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905493504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (223832547/134217728) }, upper := { exponent := 0, mantissa := (3511/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811658069/45810987008) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3690InnerLog : WideLogData :=
  innerPair175Data

set_option maxRecDepth 1000000 in
private theorem leaf3690LocalValidity :
    LeafFacts leaf3690Box leaf3690Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3690Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905493504) }) = true
      norm_num [leaf3690Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3690CertificateValid :
    WideCertificateValid leaf3690Box leaf3690Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi56ValidityFacts
    leaf3690LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3690CoverageChecked :
    coverageCheck (innerAD leaf3690Box) leaf3690InnerLog = true := by
  rfl'

private theorem leaf3690InnerLogValid :
    leaf3690InnerLog.Valid 8 (innerAD leaf3690Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint62PositiveFacts.valid leaf3690CoverageChecked

private noncomputable def leaf3690InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3690InputLogOnePlusV_eq :
    leaf3690InputLogOnePlusV = outerEnclosure 24
      (leaf3690Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3690RoundedFacts : LeafRoundedFacts 8
    leaf3690Certificate.logOnePlusV leaf3690InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3690InputLogOnePlusV_eq }

private noncomputable def leaf3690Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi56InputQChi innerPair175Input
    leaf3690InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3690LowerChecked :
    lowerCheck 24 leaf3690Box leaf3690Inputs = true := by
  rfl'

private theorem leaf3690CoversExact : CoversExact 8
    leaf3690Box leaf3690Certificate leaf3690InnerLog leaf3690Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi56RoundedFacts
    innerPair175RoundedFacts leaf3690RoundedFacts (by rfl)

private theorem leaf3690FlatSound : Sound leaf3690Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3690CertificateValid
    leaf3690InnerLogValid leaf3690CoversExact leaf3690LowerChecked

private noncomputable def leaf3691Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf3691Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743288320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (225012121/134217728) }, upper := { exponent := 0, mantissa := (1765/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486987059/27486576640) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3691InnerLog : WideLogData :=
  innerPair191Data

set_option maxRecDepth 1000000 in
private theorem leaf3691LocalValidity :
    LeafFacts leaf3691Box leaf3691Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3691Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743288320) }) = true
      norm_num [leaf3691Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3691CertificateValid :
    WideCertificateValid leaf3691Box leaf3691Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi56ValidityFacts
    leaf3691LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3691CoverageChecked :
    coverageCheck (innerAD leaf3691Box) leaf3691InnerLog = true := by
  rfl'

private theorem leaf3691InnerLogValid :
    leaf3691InnerLog.Valid 8 (innerAD leaf3691Box) :=
  wideLogDataValid_of_cachedCheck endpoint56PositiveFacts
    endpoint138PositiveFacts.valid leaf3691CoverageChecked

private noncomputable def leaf3691InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3691InputLogOnePlusV_eq :
    leaf3691InputLogOnePlusV = outerEnclosure 24
      (leaf3691Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3691RoundedFacts : LeafRoundedFacts 8
    leaf3691Certificate.logOnePlusV leaf3691InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3691InputLogOnePlusV_eq }

private noncomputable def leaf3691Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi56InputQChi innerPair191Input
    leaf3691InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3691LowerChecked :
    lowerCheck 24 leaf3691Box leaf3691Inputs = true := by
  rfl'

private theorem leaf3691CoversExact : CoversExact 8
    leaf3691Box leaf3691Certificate leaf3691InnerLog leaf3691Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi56RoundedFacts
    innerPair191RoundedFacts leaf3691RoundedFacts (by rfl)

private theorem leaf3691FlatSound : Sound leaf3691Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3691CertificateValid
    leaf3691InnerLogValid leaf3691CoversExact leaf3691LowerChecked

private noncomputable def leaf3692Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3692Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (267387135/267378688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (228812977/134217728) }, upper := { exponent := 0, mantissa := (897/512) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (534765823/534757376) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3692InnerLog : WideLogData :=
  innerPair89Data

set_option maxRecDepth 1000000 in
private theorem leaf3692LocalValidity :
    LeafFacts leaf3692Box leaf3692Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3692Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (267387135/267378688) }) = true
      norm_num [leaf3692Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3692CertificateValid :
    WideCertificateValid leaf3692Box leaf3692Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi57ValidityFacts
    leaf3692LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3692CoverageChecked :
    coverageCheck (innerAD leaf3692Box) leaf3692InnerLog = true := by
  rfl'

private theorem leaf3692InnerLogValid :
    leaf3692InnerLog.Valid 8 (innerAD leaf3692Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint63PositiveFacts.valid leaf3692CoverageChecked

private noncomputable def leaf3692InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3692InputLogOnePlusV_eq :
    leaf3692InputLogOnePlusV = outerEnclosure 24
      (leaf3692Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3692RoundedFacts : LeafRoundedFacts 8
    leaf3692Certificate.logOnePlusV leaf3692InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3692InputLogOnePlusV_eq }

private noncomputable def leaf3692Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi57InputQChi innerPair89Input
    leaf3692InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3692LowerChecked :
    lowerCheck 24 leaf3692Box leaf3692Inputs = true := by
  rfl'

private theorem leaf3692CoversExact : CoversExact 8
    leaf3692Box leaf3692Certificate leaf3692InnerLog leaf3692Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi57RoundedFacts
    innerPair89RoundedFacts leaf3692RoundedFacts (by rfl)

private theorem leaf3692FlatSound : Sound leaf3692Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3692CertificateValid
    leaf3692InnerLogValid leaf3692CoversExact leaf3692LowerChecked

private noncomputable def leaf3693Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3693Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716281856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (230058083/134217728) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434775551/137432563712) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3693InnerLog : WideLogData :=
  innerPair89Data

set_option maxRecDepth 1000000 in
private theorem leaf3693LocalValidity :
    LeafFacts leaf3693Box leaf3693Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3693Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716281856) }) = true
      norm_num [leaf3693Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3693CertificateValid :
    WideCertificateValid leaf3693Box leaf3693Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi57ValidityFacts
    leaf3693LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3693CoverageChecked :
    coverageCheck (innerAD leaf3693Box) leaf3693InnerLog = true := by
  rfl'

private theorem leaf3693InnerLogValid :
    leaf3693InnerLog.Valid 8 (innerAD leaf3693Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint63PositiveFacts.valid leaf3693CoverageChecked

private noncomputable def leaf3693InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3693InputLogOnePlusV_eq :
    leaf3693InputLogOnePlusV = outerEnclosure 24
      (leaf3693Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3693RoundedFacts : LeafRoundedFacts 8
    leaf3693Certificate.logOnePlusV leaf3693InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3693InputLogOnePlusV_eq }

private noncomputable def leaf3693Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi57InputQChi innerPair89Input
    leaf3693InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3693LowerChecked :
    lowerCheck 24 leaf3693Box leaf3693Inputs = true := by
  rfl'

private theorem leaf3693CoversExact : CoversExact 8
    leaf3693Box leaf3693Certificate leaf3693InnerLog leaf3693Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi57RoundedFacts
    innerPair89RoundedFacts leaf3693RoundedFacts (by rfl)

private theorem leaf3693FlatSound : Sound leaf3693Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3693CertificateValid
    leaf3693InnerLogValid leaf3693CoversExact leaf3693LowerChecked

private noncomputable def leaf3694Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3694Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905494528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (452416315/268435456) }, upper := { exponent := 0, mantissa := (7019/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811659093/45810989056) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3694InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3694LocalValidity :
    LeafFacts leaf3694Box leaf3694Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3694Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905494528) }) = true
      norm_num [leaf3694Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3694CertificateValid :
    WideCertificateValid leaf3694Box leaf3694Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi245ValidityFacts
    leaf3694LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3694CoverageChecked :
    coverageCheck (innerAD leaf3694Box) leaf3694InnerLog = true := by
  rfl'

private theorem leaf3694InnerLogValid :
    leaf3694InnerLog.Valid 8 (innerAD leaf3694Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3694CoverageChecked

private noncomputable def leaf3694InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3694InputLogOnePlusV_eq :
    leaf3694InputLogOnePlusV = outerEnclosure 24
      (leaf3694Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3694RoundedFacts : LeafRoundedFacts 8
    leaf3694Certificate.logOnePlusV leaf3694InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3694InputLogOnePlusV_eq }

private noncomputable def leaf3694Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi245InputQChi innerPair57Input
    leaf3694InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3694LowerChecked :
    lowerCheck 24 leaf3694Box leaf3694Inputs = true := by
  rfl'

private theorem leaf3694CoversExact : CoversExact 8
    leaf3694Box leaf3694Certificate leaf3694InnerLog leaf3694Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi245RoundedFacts
    innerPair57RoundedFacts leaf3694RoundedFacts (by rfl)

private theorem leaf3694FlatSound : Sound leaf3694Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3694CertificateValid
    leaf3694InnerLogValid leaf3694CoversExact leaf3694LowerChecked

private noncomputable def leaf3695Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3695Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716402688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (457527809/268435456) }, upper := { exponent := 0, mantissa := (3549/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434896383/137432805376) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3695InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3695LocalValidity :
    LeafFacts leaf3695Box leaf3695Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3695Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716402688) }) = true
      norm_num [leaf3695Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3695CertificateValid :
    WideCertificateValid leaf3695Box leaf3695Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi246ValidityFacts
    leaf3695LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3695CoverageChecked :
    coverageCheck (innerAD leaf3695Box) leaf3695InnerLog = true := by
  rfl'

private theorem leaf3695InnerLogValid :
    leaf3695InnerLog.Valid 8 (innerAD leaf3695Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3695CoverageChecked

private noncomputable def leaf3695InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3695InputLogOnePlusV_eq :
    leaf3695InputLogOnePlusV = outerEnclosure 24
      (leaf3695Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3695RoundedFacts : LeafRoundedFacts 8
    leaf3695Certificate.logOnePlusV leaf3695InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3695InputLogOnePlusV_eq }

private noncomputable def leaf3695Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi246InputQChi innerPair64Input
    leaf3695InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3695LowerChecked :
    lowerCheck 24 leaf3695Box leaf3695Inputs = true := by
  rfl'

private theorem leaf3695CoversExact : CoversExact 8
    leaf3695Box leaf3695Certificate leaf3695InnerLog leaf3695Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi246RoundedFacts
    innerPair64RoundedFacts leaf3695RoundedFacts (by rfl)

private theorem leaf3695FlatSound : Sound leaf3695Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3695CertificateValid
    leaf3695InnerLogValid leaf3695CoversExact leaf3695LowerChecked

private noncomputable def leaf3696Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (9/32), chiHi := (37/128) }

private noncomputable def leaf3696Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716445696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (454775465/268435456) }, upper := { exponent := 0, mantissa := (441/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi245LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434939391/137432891392) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3696InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3696LocalValidity :
    LeafFacts leaf3696Box leaf3696Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3696Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716445696) }) = true
      norm_num [leaf3696Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3696CertificateValid :
    WideCertificateValid leaf3696Box leaf3696Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi245ValidityFacts
    leaf3696LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3696CoverageChecked :
    coverageCheck (innerAD leaf3696Box) leaf3696InnerLog = true := by
  rfl'

private theorem leaf3696InnerLogValid :
    leaf3696InnerLog.Valid 8 (innerAD leaf3696Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3696CoverageChecked

private noncomputable def leaf3696InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3696InputLogOnePlusV_eq :
    leaf3696InputLogOnePlusV = outerEnclosure 24
      (leaf3696Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3696RoundedFacts : LeafRoundedFacts 8
    leaf3696Certificate.logOnePlusV leaf3696InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3696InputLogOnePlusV_eq }

private noncomputable def leaf3696Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi245InputQChi innerPair64Input
    leaf3696InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3696LowerChecked :
    lowerCheck 24 leaf3696Box leaf3696Inputs = true := by
  rfl'

private theorem leaf3696CoversExact : CoversExact 8
    leaf3696Box leaf3696Certificate leaf3696InnerLog leaf3696Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi245RoundedFacts
    innerPair64RoundedFacts leaf3696RoundedFacts (by rfl)

private theorem leaf3696FlatSound : Sound leaf3696Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3696CertificateValid
    leaf3696InnerLogValid leaf3696CoversExact leaf3696LowerChecked

private noncomputable def leaf3697Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (37/128), chiHi := (19/64) }

private noncomputable def leaf3697Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905454592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (459952491/268435456) }, upper := { exponent := 0, mantissa := (223/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi246LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811619157/45810909184) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3697InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3697LocalValidity :
    LeafFacts leaf3697Box leaf3697Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3697Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905454592) }) = true
      norm_num [leaf3697Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3697CertificateValid :
    WideCertificateValid leaf3697Box leaf3697Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi246ValidityFacts
    leaf3697LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3697CoverageChecked :
    coverageCheck (innerAD leaf3697Box) leaf3697InnerLog = true := by
  rfl'

private theorem leaf3697InnerLogValid :
    leaf3697InnerLog.Valid 8 (innerAD leaf3697Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3697CoverageChecked

private noncomputable def leaf3697InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3697InputLogOnePlusV_eq :
    leaf3697InputLogOnePlusV = outerEnclosure 24
      (leaf3697Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3697RoundedFacts : LeafRoundedFacts 8
    leaf3697Certificate.logOnePlusV leaf3697InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3697InputLogOnePlusV_eq }

private noncomputable def leaf3697Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi246InputQChi innerPair64Input
    leaf3697InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3697LowerChecked :
    lowerCheck 24 leaf3697Box leaf3697Inputs = true := by
  rfl'

private theorem leaf3697CoversExact : CoversExact 8
    leaf3697Box leaf3697Certificate leaf3697InnerLog leaf3697Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi246RoundedFacts
    innerPair64RoundedFacts leaf3697RoundedFacts (by rfl)

private theorem leaf3697FlatSound : Sound leaf3697Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3697CertificateValid
    leaf3697InnerLogValid leaf3697CoversExact leaf3697LowerChecked

private noncomputable def leaf3698Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf3698Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905413632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (231303189/134217728) }, upper := { exponent := 0, mantissa := (907/512) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811578197/45810827264) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3698InnerLog : WideLogData :=
  innerPair461Data

set_option maxRecDepth 1000000 in
private theorem leaf3698LocalValidity :
    LeafFacts leaf3698Box leaf3698Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3698Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905413632) }) = true
      norm_num [leaf3698Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3698CertificateValid :
    WideCertificateValid leaf3698Box leaf3698Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi57ValidityFacts
    leaf3698LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3698CoverageChecked :
    coverageCheck (innerAD leaf3698Box) leaf3698InnerLog = true := by
  rfl'

private theorem leaf3698InnerLogValid :
    leaf3698InnerLog.Valid 8 (innerAD leaf3698Box) :=
  wideLogDataValid_of_cachedCheck endpoint179PositiveFacts
    endpoint217PositiveFacts.valid leaf3698CoverageChecked

private noncomputable def leaf3698InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3698InputLogOnePlusV_eq :
    leaf3698InputLogOnePlusV = outerEnclosure 24
      (leaf3698Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3698RoundedFacts : LeafRoundedFacts 8
    leaf3698Certificate.logOnePlusV leaf3698InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3698InputLogOnePlusV_eq }

private noncomputable def leaf3698Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi57InputQChi innerPair461Input
    leaf3698InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3698LowerChecked :
    lowerCheck 24 leaf3698Box leaf3698Inputs = true := by
  rfl'

private theorem leaf3698CoversExact : CoversExact 8
    leaf3698Box leaf3698Certificate leaf3698InnerLog leaf3698Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi57RoundedFacts
    innerPair461RoundedFacts leaf3698RoundedFacts (by rfl)

private theorem leaf3698FlatSound : Sound leaf3698Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3698CertificateValid
    leaf3698InnerLogValid leaf3698CoversExact leaf3698LowerChecked

private noncomputable def leaf3699Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (19/64), chiHi := (39/128) }

private noncomputable def leaf3699Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716281856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (465129517/268435456) }, upper := { exponent := 0, mantissa := (451/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi247LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434775551/137432563712) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3699InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3699LocalValidity :
    LeafFacts leaf3699Box leaf3699Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3699Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716281856) }) = true
      norm_num [leaf3699Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3699CertificateValid :
    WideCertificateValid leaf3699Box leaf3699Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi247ValidityFacts
    leaf3699LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3699CoverageChecked :
    coverageCheck (innerAD leaf3699Box) leaf3699InnerLog = true := by
  rfl'

private theorem leaf3699InnerLogValid :
    leaf3699InnerLog.Valid 8 (innerAD leaf3699Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3699CoverageChecked

private noncomputable def leaf3699InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3699InputLogOnePlusV_eq :
    leaf3699InputLogOnePlusV = outerEnclosure 24
      (leaf3699Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3699RoundedFacts : LeafRoundedFacts 8
    leaf3699Certificate.logOnePlusV leaf3699InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3699InputLogOnePlusV_eq }

private noncomputable def leaf3699Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi247InputQChi innerPair66Input
    leaf3699InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3699LowerChecked :
    lowerCheck 24 leaf3699Box leaf3699Inputs = true := by
  rfl'

private theorem leaf3699CoversExact : CoversExact 8
    leaf3699Box leaf3699Certificate leaf3699InnerLog leaf3699Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi247RoundedFacts
    innerPair66RoundedFacts leaf3699RoundedFacts (by rfl)

private theorem leaf3699FlatSound : Sound leaf3699Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3699CertificateValid
    leaf3699InnerLogValid leaf3699CoversExact leaf3699LowerChecked

private noncomputable def leaf3700Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (39/128), chiHi := (5/16) }

private noncomputable def leaf3700Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042129408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (470306543/268435456) }, upper := { exponent := 0, mantissa := (57/32) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi248LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084393743/8084258816) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3700InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3700LocalValidity :
    LeafFacts leaf3700Box leaf3700Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3700Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042129408) }) = true
      norm_num [leaf3700Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3700CertificateValid :
    WideCertificateValid leaf3700Box leaf3700Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi248ValidityFacts
    leaf3700LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3700CoverageChecked :
    coverageCheck (innerAD leaf3700Box) leaf3700InnerLog = true := by
  rfl'

private theorem leaf3700InnerLogValid :
    leaf3700InnerLog.Valid 8 (innerAD leaf3700Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3700CoverageChecked

private noncomputable def leaf3700InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3700InputLogOnePlusV_eq :
    leaf3700InputLogOnePlusV = outerEnclosure 24
      (leaf3700Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3700RoundedFacts : LeafRoundedFacts 8
    leaf3700Certificate.logOnePlusV leaf3700InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3700InputLogOnePlusV_eq }

private noncomputable def leaf3700Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi248InputQChi innerPair71Input
    leaf3700InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3700LowerChecked :
    lowerCheck 24 leaf3700Box leaf3700Inputs = true := by
  rfl'

private theorem leaf3700CoversExact : CoversExact 8
    leaf3700Box leaf3700Certificate leaf3700InnerLog leaf3700Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi248RoundedFacts
    innerPair71RoundedFacts leaf3700RoundedFacts (by rfl)

private theorem leaf3700FlatSound : Sound leaf3700Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3700CertificateValid
    leaf3700InnerLogValid leaf3700CoversExact leaf3700LowerChecked

private noncomputable def component75Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node0_sound : Sound component75Node0Box :=
  sound_of_literal_split component75Node0Box leaf3660Box leaf3661Box
    .k (73/32) (by rfl) (by rfl)
    leaf3660FlatSound leaf3661FlatSound

private noncomputable def component75Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node1_sound : Sound component75Node1Box :=
  sound_of_literal_split component75Node1Box leaf3662Box leaf3663Box
    .k (73/32) (by rfl) (by rfl)
    leaf3662FlatSound leaf3663FlatSound

private noncomputable def component75Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node2_sound : Sound component75Node2Box :=
  sound_of_literal_split component75Node2Box component75Node0Box component75Node1Box
    .chi (17/64) (by rfl) (by rfl)
    component75Node0_sound component75Node1_sound

private noncomputable def component75Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node3_sound : Sound component75Node3Box :=
  sound_of_literal_split component75Node3Box leaf3664Box leaf3665Box
    .k (75/32) (by rfl) (by rfl)
    leaf3664FlatSound leaf3665FlatSound

private noncomputable def component75Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node4_sound : Sound component75Node4Box :=
  sound_of_literal_split component75Node4Box leaf3666Box leaf3667Box
    .k (75/32) (by rfl) (by rfl)
    leaf3666FlatSound leaf3667FlatSound

private noncomputable def component75Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node5_sound : Sound component75Node5Box :=
  sound_of_literal_split component75Node5Box component75Node3Box component75Node4Box
    .chi (17/64) (by rfl) (by rfl)
    component75Node3_sound component75Node4_sound

private noncomputable def component75Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node6_sound : Sound component75Node6Box :=
  sound_of_literal_split component75Node6Box component75Node2Box component75Node5Box
    .k (37/16) (by rfl) (by rfl)
    component75Node2_sound component75Node5_sound

private noncomputable def component75Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node7_sound : Sound component75Node7Box :=
  sound_of_literal_split component75Node7Box leaf3668Box leaf3669Box
    .k (73/32) (by rfl) (by rfl)
    leaf3668FlatSound leaf3669FlatSound

private noncomputable def component75Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node8_sound : Sound component75Node8Box :=
  sound_of_literal_split component75Node8Box leaf3670Box leaf3671Box
    .k (73/32) (by rfl) (by rfl)
    leaf3670FlatSound leaf3671FlatSound

private noncomputable def component75Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node9_sound : Sound component75Node9Box :=
  sound_of_literal_split component75Node9Box component75Node7Box component75Node8Box
    .chi (19/64) (by rfl) (by rfl)
    component75Node7_sound component75Node8_sound

private noncomputable def component75Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node10_sound : Sound component75Node10Box :=
  sound_of_literal_split component75Node10Box leaf3672Box leaf3673Box
    .k (75/32) (by rfl) (by rfl)
    leaf3672FlatSound leaf3673FlatSound

private noncomputable def component75Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node11_sound : Sound component75Node11Box :=
  sound_of_literal_split component75Node11Box leaf3674Box leaf3675Box
    .k (75/32) (by rfl) (by rfl)
    leaf3674FlatSound leaf3675FlatSound

private noncomputable def component75Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node12_sound : Sound component75Node12Box :=
  sound_of_literal_split component75Node12Box component75Node10Box component75Node11Box
    .chi (19/64) (by rfl) (by rfl)
    component75Node10_sound component75Node11_sound

private noncomputable def component75Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node13_sound : Sound component75Node13Box :=
  sound_of_literal_split component75Node13Box component75Node9Box component75Node12Box
    .k (37/16) (by rfl) (by rfl)
    component75Node9_sound component75Node12_sound

private noncomputable def component75Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node14_sound : Sound component75Node14Box :=
  sound_of_literal_split component75Node14Box component75Node6Box component75Node13Box
    .chi (9/32) (by rfl) (by rfl)
    component75Node6_sound component75Node13_sound

private noncomputable def component75Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node15_sound : Sound component75Node15Box :=
  sound_of_literal_split component75Node15Box leaf3677Box leaf3678Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3677FlatSound leaf3678FlatSound

private noncomputable def component75Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node16_sound : Sound component75Node16Box :=
  sound_of_literal_split component75Node16Box leaf3676Box component75Node15Box
    .k (77/32) (by rfl) (by rfl)
    leaf3676FlatSound component75Node15_sound

private noncomputable def component75Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node17_sound : Sound component75Node17Box :=
  sound_of_literal_split component75Node17Box leaf3680Box leaf3681Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3680FlatSound leaf3681FlatSound

private noncomputable def component75Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node18_sound : Sound component75Node18Box :=
  sound_of_literal_split component75Node18Box leaf3679Box component75Node17Box
    .k (77/32) (by rfl) (by rfl)
    leaf3679FlatSound component75Node17_sound

private noncomputable def component75Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node19_sound : Sound component75Node19Box :=
  sound_of_literal_split component75Node19Box component75Node16Box component75Node18Box
    .chi (17/64) (by rfl) (by rfl)
    component75Node16_sound component75Node18_sound

private noncomputable def component75Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node20_sound : Sound component75Node20Box :=
  sound_of_literal_split component75Node20Box leaf3682Box leaf3683Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3682FlatSound leaf3683FlatSound

private noncomputable def component75Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node21_sound : Sound component75Node21Box :=
  sound_of_literal_split component75Node21Box leaf3684Box leaf3685Box
    .chi (33/128) (by rfl) (by rfl)
    leaf3684FlatSound leaf3685FlatSound

private noncomputable def component75Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node22_sound : Sound component75Node22Box :=
  sound_of_literal_split component75Node22Box component75Node20Box component75Node21Box
    .k (79/32) (by rfl) (by rfl)
    component75Node20_sound component75Node21_sound

private noncomputable def component75Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node23_sound : Sound component75Node23Box :=
  sound_of_literal_split component75Node23Box leaf3686Box leaf3687Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3686FlatSound leaf3687FlatSound

private noncomputable def component75Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node24_sound : Sound component75Node24Box :=
  sound_of_literal_split component75Node24Box leaf3688Box leaf3689Box
    .chi (35/128) (by rfl) (by rfl)
    leaf3688FlatSound leaf3689FlatSound

private noncomputable def component75Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node25_sound : Sound component75Node25Box :=
  sound_of_literal_split component75Node25Box component75Node23Box component75Node24Box
    .k (79/32) (by rfl) (by rfl)
    component75Node23_sound component75Node24_sound

private noncomputable def component75Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node26_sound : Sound component75Node26Box :=
  sound_of_literal_split component75Node26Box component75Node22Box component75Node25Box
    .chi (17/64) (by rfl) (by rfl)
    component75Node22_sound component75Node25_sound

private noncomputable def component75Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component75Node27_sound : Sound component75Node27Box :=
  sound_of_literal_split component75Node27Box component75Node19Box component75Node26Box
    .k (39/16) (by rfl) (by rfl)
    component75Node19_sound component75Node26_sound

private noncomputable def component75Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node28_sound : Sound component75Node28Box :=
  sound_of_literal_split component75Node28Box leaf3690Box leaf3691Box
    .k (77/32) (by rfl) (by rfl)
    leaf3690FlatSound leaf3691FlatSound

private noncomputable def component75Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node29_sound : Sound component75Node29Box :=
  sound_of_literal_split component75Node29Box leaf3692Box leaf3693Box
    .k (77/32) (by rfl) (by rfl)
    leaf3692FlatSound leaf3693FlatSound

private noncomputable def component75Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node30_sound : Sound component75Node30Box :=
  sound_of_literal_split component75Node30Box component75Node28Box component75Node29Box
    .chi (19/64) (by rfl) (by rfl)
    component75Node28_sound component75Node29_sound

private noncomputable def component75Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node31_sound : Sound component75Node31Box :=
  sound_of_literal_split component75Node31Box leaf3694Box leaf3695Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3694FlatSound leaf3695FlatSound

private noncomputable def component75Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node32_sound : Sound component75Node32Box :=
  sound_of_literal_split component75Node32Box leaf3696Box leaf3697Box
    .chi (37/128) (by rfl) (by rfl)
    leaf3696FlatSound leaf3697FlatSound

private noncomputable def component75Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component75Node33_sound : Sound component75Node33Box :=
  sound_of_literal_split component75Node33Box component75Node31Box component75Node32Box
    .k (79/32) (by rfl) (by rfl)
    component75Node31_sound component75Node32_sound

private noncomputable def component75Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node34_sound : Sound component75Node34Box :=
  sound_of_literal_split component75Node34Box leaf3699Box leaf3700Box
    .chi (39/128) (by rfl) (by rfl)
    leaf3699FlatSound leaf3700FlatSound

private noncomputable def component75Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node35_sound : Sound component75Node35Box :=
  sound_of_literal_split component75Node35Box leaf3698Box component75Node34Box
    .k (79/32) (by rfl) (by rfl)
    leaf3698FlatSound component75Node34_sound

private noncomputable def component75Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node36_sound : Sound component75Node36Box :=
  sound_of_literal_split component75Node36Box component75Node33Box component75Node35Box
    .chi (19/64) (by rfl) (by rfl)
    component75Node33_sound component75Node35_sound

private noncomputable def component75Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node37_sound : Sound component75Node37Box :=
  sound_of_literal_split component75Node37Box component75Node30Box component75Node36Box
    .k (39/16) (by rfl) (by rfl)
    component75Node30_sound component75Node36_sound

private noncomputable def component75Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component75Node38_sound : Sound component75Node38Box :=
  sound_of_literal_split component75Node38Box component75Node27Box component75Node37Box
    .chi (9/32) (by rfl) (by rfl)
    component75Node27_sound component75Node37_sound

noncomputable def component75Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
theorem component75_sound : Sound component75Box :=
  sound_of_literal_split component75Box component75Node14Box component75Node38Box
    .k (19/8) (by rfl) (by rfl)
    component75Node14_sound component75Node38_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
