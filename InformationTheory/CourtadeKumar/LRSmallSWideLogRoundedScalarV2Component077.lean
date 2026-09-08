import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0
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

private noncomputable def leaf3733Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3733Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905382912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (234841935/134217728) }, upper := { exponent := 0, mantissa := (3673/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811547477/45810765824) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3733InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3733LocalValidity :
    LeafFacts leaf3733Box leaf3733Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3733Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905382912) }) = true
      norm_num [leaf3733Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3733CertificateValid :
    WideCertificateValid leaf3733Box leaf3733Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi62ValidityFacts
    leaf3733LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3733CoverageChecked :
    coverageCheck (innerAD leaf3733Box) leaf3733InnerLog = true := by
  rfl'

private theorem leaf3733InnerLogValid :
    leaf3733InnerLog.Valid 8 (innerAD leaf3733Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3733CoverageChecked

private noncomputable def leaf3733InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3733InputLogOnePlusV_eq :
    leaf3733InputLogOnePlusV = outerEnclosure 24
      (leaf3733Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3733RoundedFacts : LeafRoundedFacts 8
    leaf3733Certificate.logOnePlusV leaf3733InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3733InputLogOnePlusV_eq }

private noncomputable def leaf3733Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi62InputQChi innerPair66Input
    leaf3733InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3733LowerChecked :
    lowerCheck 24 leaf3733Box leaf3733Inputs = true := by
  rfl'

private theorem leaf3733CoversExact : CoversExact 8
    leaf3733Box leaf3733Certificate leaf3733InnerLog leaf3733Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi62RoundedFacts
    innerPair66RoundedFacts leaf3733RoundedFacts (by rfl)

private theorem leaf3733FlatSound : Sound leaf3733Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3733CertificateValid
    leaf3733InnerLogValid leaf3733CoversExact leaf3733LowerChecked

private noncomputable def leaf3734Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3734Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716097536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (236414701/134217728) }, upper := { exponent := 0, mantissa := (1849/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434591231/137432195072) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3734InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3734LocalValidity :
    LeafFacts leaf3734Box leaf3734Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3734Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716097536) }) = true
      norm_num [leaf3734Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3734CertificateValid :
    WideCertificateValid leaf3734Box leaf3734Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi62ValidityFacts
    leaf3734LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3734CoverageChecked :
    coverageCheck (innerAD leaf3734Box) leaf3734InnerLog = true := by
  rfl'

private theorem leaf3734InnerLogValid :
    leaf3734InnerLog.Valid 8 (innerAD leaf3734Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3734CoverageChecked

private noncomputable def leaf3734InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3734InputLogOnePlusV_eq :
    leaf3734InputLogOnePlusV = outerEnclosure 24
      (leaf3734Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3734RoundedFacts : LeafRoundedFacts 8
    leaf3734Certificate.logOnePlusV leaf3734InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3734InputLogOnePlusV_eq }

private noncomputable def leaf3734Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi62InputQChi innerPair71Input
    leaf3734InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3734LowerChecked :
    lowerCheck 24 leaf3734Box leaf3734Inputs = true := by
  rfl'

private theorem leaf3734CoversExact : CoversExact 8
    leaf3734Box leaf3734Certificate leaf3734InnerLog leaf3734Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi62RoundedFacts
    innerPair71RoundedFacts leaf3734RoundedFacts (by rfl)

private theorem leaf3734FlatSound : Sound leaf3734Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3734CertificateValid
    leaf3734InnerLogValid leaf3734CoversExact leaf3734LowerChecked

private noncomputable def leaf3735Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3735Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716015616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (239035981/134217728) }, upper := { exponent := 0, mantissa := (1869/1024) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434509311/137432031232) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3735InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3735LocalValidity :
    LeafFacts leaf3735Box leaf3735Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3735Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716015616) }) = true
      norm_num [leaf3735Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3735CertificateValid :
    WideCertificateValid leaf3735Box leaf3735Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi63ValidityFacts
    leaf3735LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3735CoverageChecked :
    coverageCheck (innerAD leaf3735Box) leaf3735InnerLog = true := by
  rfl'

private theorem leaf3735InnerLogValid :
    leaf3735InnerLog.Valid 8 (innerAD leaf3735Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3735CoverageChecked

private noncomputable def leaf3735InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3735InputLogOnePlusV_eq :
    leaf3735InputLogOnePlusV = outerEnclosure 24
      (leaf3735Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3735RoundedFacts : LeafRoundedFacts 8
    leaf3735Certificate.logOnePlusV leaf3735InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3735InputLogOnePlusV_eq }

private noncomputable def leaf3735Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi63InputQChi innerPair72Input
    leaf3735InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3735LowerChecked :
    lowerCheck 24 leaf3735Box leaf3735Inputs = true := by
  rfl'

private theorem leaf3735CoversExact : CoversExact 8
    leaf3735Box leaf3735Certificate leaf3735InnerLog leaf3735Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi63RoundedFacts
    innerPair72RoundedFacts leaf3735RoundedFacts (by rfl)

private theorem leaf3735FlatSound : Sound leaf3735Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3735CertificateValid
    leaf3735InnerLogValid leaf3735CoversExact leaf3735LowerChecked

private noncomputable def leaf3736Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3736Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715962368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (240674279/134217728) }, upper := { exponent := 0, mantissa := (941/512) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434456063/137431924736) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3736InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3736LocalValidity :
    LeafFacts leaf3736Box leaf3736Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3736Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715962368) }) = true
      norm_num [leaf3736Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3736CertificateValid :
    WideCertificateValid leaf3736Box leaf3736Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi63ValidityFacts
    leaf3736LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3736CoverageChecked :
    coverageCheck (innerAD leaf3736Box) leaf3736InnerLog = true := by
  rfl'

private theorem leaf3736InnerLogValid :
    leaf3736InnerLog.Valid 8 (innerAD leaf3736Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3736CoverageChecked

private noncomputable def leaf3736InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3736InputLogOnePlusV_eq :
    leaf3736InputLogOnePlusV = outerEnclosure 24
      (leaf3736Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3736RoundedFacts : LeafRoundedFacts 8
    leaf3736Certificate.logOnePlusV leaf3736InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3736InputLogOnePlusV_eq }

private noncomputable def leaf3736Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi63InputQChi innerPair72Input
    leaf3736InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3736LowerChecked :
    lowerCheck 24 leaf3736Box leaf3736Inputs = true := by
  rfl'

private theorem leaf3736CoversExact : CoversExact 8
    leaf3736Box leaf3736Certificate leaf3736InnerLog leaf3736Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi63RoundedFacts
    innerPair72RoundedFacts leaf3736RoundedFacts (by rfl)

private theorem leaf3736FlatSound : Sound leaf3736Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3736CertificateValid
    leaf3736InnerLogValid leaf3736CoversExact leaf3736LowerChecked

private noncomputable def leaf3737Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3737Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716046336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (237987467/134217728) }, upper := { exponent := 0, mantissa := (3723/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434540031/137432092672) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3737InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3737LocalValidity :
    LeafFacts leaf3737Box leaf3737Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3737Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716046336) }) = true
      norm_num [leaf3737Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3737CertificateValid :
    WideCertificateValid leaf3737Box leaf3737Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi62ValidityFacts
    leaf3737LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3737CoverageChecked :
    coverageCheck (innerAD leaf3737Box) leaf3737InnerLog = true := by
  rfl'

private theorem leaf3737InnerLogValid :
    leaf3737InnerLog.Valid 8 (innerAD leaf3737Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3737CoverageChecked

private noncomputable def leaf3737InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3737InputLogOnePlusV_eq :
    leaf3737InputLogOnePlusV = outerEnclosure 24
      (leaf3737Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3737RoundedFacts : LeafRoundedFacts 8
    leaf3737Certificate.logOnePlusV leaf3737InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3737InputLogOnePlusV_eq }

private noncomputable def leaf3737Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi62InputQChi innerPair72Input
    leaf3737InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3737LowerChecked :
    lowerCheck 24 leaf3737Box leaf3737Inputs = true := by
  rfl'

private theorem leaf3737CoversExact : CoversExact 8
    leaf3737Box leaf3737Certificate leaf3737InnerLog leaf3737Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi62RoundedFacts
    innerPair72RoundedFacts leaf3737RoundedFacts (by rfl)

private theorem leaf3737FlatSound : Sound leaf3737Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3737CertificateValid
    leaf3737InnerLogValid leaf3737CoversExact leaf3737LowerChecked

private noncomputable def leaf3738Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3738Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905331712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (239560233/134217728) }, upper := { exponent := 0, mantissa := (937/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811496277/45810663424) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3738InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3738LocalValidity :
    LeafFacts leaf3738Box leaf3738Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3738Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905331712) }) = true
      norm_num [leaf3738Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3738CertificateValid :
    WideCertificateValid leaf3738Box leaf3738Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi62ValidityFacts
    leaf3738LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3738CoverageChecked :
    coverageCheck (innerAD leaf3738Box) leaf3738InnerLog = true := by
  rfl'

private theorem leaf3738InnerLogValid :
    leaf3738InnerLog.Valid 8 (innerAD leaf3738Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3738CoverageChecked

private noncomputable def leaf3738InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3738InputLogOnePlusV_eq :
    leaf3738InputLogOnePlusV = outerEnclosure 24
      (leaf3738Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3738RoundedFacts : LeafRoundedFacts 8
    leaf3738Certificate.logOnePlusV leaf3738InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3738InputLogOnePlusV_eq }

private noncomputable def leaf3738Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi62InputQChi innerPair72Input
    leaf3738InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3738LowerChecked :
    lowerCheck 24 leaf3738Box leaf3738Inputs = true := by
  rfl'

private theorem leaf3738CoversExact : CoversExact 8
    leaf3738Box leaf3738Certificate leaf3738InnerLog leaf3738Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi62RoundedFacts
    innerPair72RoundedFacts leaf3738RoundedFacts (by rfl)

private theorem leaf3738FlatSound : Sound leaf3738Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3738CertificateValid
    leaf3738InnerLogValid leaf3738CoversExact leaf3738LowerChecked

private noncomputable def leaf3739Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3739Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581060608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (242312577/134217728) }, upper := { exponent := 0, mantissa := (1895/1024) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162293521/9162121216) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3739InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3739LocalValidity :
    LeafFacts leaf3739Box leaf3739Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3739Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581060608) }) = true
      norm_num [leaf3739Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3739CertificateValid :
    WideCertificateValid leaf3739Box leaf3739Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi63ValidityFacts
    leaf3739LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3739CoverageChecked :
    coverageCheck (innerAD leaf3739Box) leaf3739InnerLog = true := by
  rfl'

private theorem leaf3739InnerLogValid :
    leaf3739InnerLog.Valid 8 (innerAD leaf3739Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3739CoverageChecked

private noncomputable def leaf3739InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3739InputLogOnePlusV_eq :
    leaf3739InputLogOnePlusV = outerEnclosure 24
      (leaf3739Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3739RoundedFacts : LeafRoundedFacts 8
    leaf3739Certificate.logOnePlusV leaf3739InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3739InputLogOnePlusV_eq }

private noncomputable def leaf3739Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi63InputQChi innerPair72Input
    leaf3739InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3739LowerChecked :
    lowerCheck 24 leaf3739Box leaf3739Inputs = true := by
  rfl'

private theorem leaf3739CoversExact : CoversExact 8
    leaf3739Box leaf3739Certificate leaf3739InnerLog leaf3739Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi63RoundedFacts
    innerPair72RoundedFacts leaf3739RoundedFacts (by rfl)

private theorem leaf3739FlatSound : Sound leaf3739Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3739CertificateValid
    leaf3739InnerLogValid leaf3739CoversExact leaf3739LowerChecked

private noncomputable def leaf3740Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3740Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715855872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (243950875/134217728) }, upper := { exponent := 0, mantissa := (477/256) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434349567/137431711744) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3740InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3740LocalValidity :
    LeafFacts leaf3740Box leaf3740Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3740Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715855872) }) = true
      norm_num [leaf3740Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3740CertificateValid :
    WideCertificateValid leaf3740Box leaf3740Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi63ValidityFacts
    leaf3740LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3740CoverageChecked :
    coverageCheck (innerAD leaf3740Box) leaf3740InnerLog = true := by
  rfl'

private theorem leaf3740InnerLogValid :
    leaf3740InnerLog.Valid 8 (innerAD leaf3740Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3740CoverageChecked

private noncomputable def leaf3740InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3740InputLogOnePlusV_eq :
    leaf3740InputLogOnePlusV = outerEnclosure 24
      (leaf3740Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3740RoundedFacts : LeafRoundedFacts 8
    leaf3740Certificate.logOnePlusV leaf3740InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3740InputLogOnePlusV_eq }

private noncomputable def leaf3740Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi63InputQChi innerPair91Input
    leaf3740InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3740LowerChecked :
    lowerCheck 24 leaf3740Box leaf3740Inputs = true := by
  rfl'

private theorem leaf3740CoversExact : CoversExact 8
    leaf3740Box leaf3740Certificate leaf3740InnerLog leaf3740Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi63RoundedFacts
    innerPair91RoundedFacts leaf3740RoundedFacts (by rfl)

private theorem leaf3740FlatSound : Sound leaf3740Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3740CertificateValid
    leaf3740InnerLogValid leaf3740CoversExact leaf3740LowerChecked

private noncomputable def leaf3741Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3741Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715882496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (243230027/134217728) }, upper := { exponent := 0, mantissa := (3803/2048) } }, logOuter := sk71LogOuterCertificate, logK := sk71LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434376191/137431764992) } }, logDArg := sk71LogDArgCertificate }

private noncomputable def leaf3741InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3741LocalValidity :
    LeafFacts leaf3741Box leaf3741Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3741Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715882496) }) = true
      norm_num [leaf3741Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3741CertificateValid :
    WideCertificateValid leaf3741Box leaf3741Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk71ValidityFacts chi64ValidityFacts
    leaf3741LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3741CoverageChecked :
    coverageCheck (innerAD leaf3741Box) leaf3741InnerLog = true := by
  rfl'

private theorem leaf3741InnerLogValid :
    leaf3741InnerLog.Valid 8 (innerAD leaf3741Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3741CoverageChecked

private noncomputable def leaf3741InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3741InputLogOnePlusV_eq :
    leaf3741InputLogOnePlusV = outerEnclosure 24
      (leaf3741Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3741RoundedFacts : LeafRoundedFacts 8
    leaf3741Certificate.logOnePlusV leaf3741InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3741InputLogOnePlusV_eq }

private noncomputable def leaf3741Inputs : Inputs :=
  inputsOfCaches globalInput sk71RoundedInputs
    chi64InputQChi innerPair72Input
    leaf3741InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3741LowerChecked :
    lowerCheck 24 leaf3741Box leaf3741Inputs = true := by
  rfl'

private theorem leaf3741CoversExact : CoversExact 8
    leaf3741Box leaf3741Certificate leaf3741InnerLog leaf3741Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk71RoundedFacts chi64RoundedFacts
    innerPair72RoundedFacts leaf3741RoundedFacts (by rfl)

private theorem leaf3741FlatSound : Sound leaf3741Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3741CertificateValid
    leaf3741InnerLogValid leaf3741CoversExact leaf3741LowerChecked

private noncomputable def leaf3742Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3742Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743165440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (244933857/134217728) }, upper := { exponent := 0, mantissa := (1915/1024) } }, logOuter := sk72LogOuterCertificate, logK := sk72LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486864179/27486330880) } }, logDArg := sk72LogDArgCertificate }

private noncomputable def leaf3742InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3742LocalValidity :
    LeafFacts leaf3742Box leaf3742Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3742Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743165440) }) = true
      norm_num [leaf3742Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3742CertificateValid :
    WideCertificateValid leaf3742Box leaf3742Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk72ValidityFacts chi64ValidityFacts
    leaf3742LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3742CoverageChecked :
    coverageCheck (innerAD leaf3742Box) leaf3742InnerLog = true := by
  rfl'

private theorem leaf3742InnerLogValid :
    leaf3742InnerLog.Valid 8 (innerAD leaf3742Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3742CoverageChecked

private noncomputable def leaf3742InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3742InputLogOnePlusV_eq :
    leaf3742InputLogOnePlusV = outerEnclosure 24
      (leaf3742Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3742RoundedFacts : LeafRoundedFacts 8
    leaf3742Certificate.logOnePlusV leaf3742InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3742InputLogOnePlusV_eq }

private noncomputable def leaf3742Inputs : Inputs :=
  inputsOfCaches globalInput sk72RoundedInputs
    chi64InputQChi innerPair91Input
    leaf3742InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3742LowerChecked :
    lowerCheck 24 leaf3742Box leaf3742Inputs = true := by
  rfl'

private theorem leaf3742CoversExact : CoversExact 8
    leaf3742Box leaf3742Certificate leaf3742InnerLog leaf3742Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk72RoundedFacts chi64RoundedFacts
    innerPair91RoundedFacts leaf3742RoundedFacts (by rfl)

private theorem leaf3742FlatSound : Sound leaf3742Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3742CertificateValid
    leaf3742InnerLogValid leaf3742CoversExact leaf3742LowerChecked

private noncomputable def leaf3743Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3743Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108985/67108864) }, vSqrt := { lower := (65531/65536), upper := (34359279615/34357846016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (123695625/67108864) }, upper := { exponent := 0, mantissa := (487/256) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68717125631/68715692032) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf3743InnerLog : WideLogData :=
  innerPair508Data

set_option maxRecDepth 1000000 in
private theorem leaf3743LocalValidity :
    LeafFacts leaf3743Box leaf3743Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3743Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34359279615/34357846016) }) = true
      norm_num [leaf3743Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3743CertificateValid :
    WideCertificateValid leaf3743Box leaf3743Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi65ValidityFacts
    leaf3743LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3743CoverageChecked :
    coverageCheck (innerAD leaf3743Box) leaf3743InnerLog = true := by
  rfl'

private theorem leaf3743InnerLogValid :
    leaf3743InnerLog.Valid 8 (innerAD leaf3743Box) :=
  wideLogDataValid_of_cachedCheck endpoint236PositiveFacts
    endpoint247PositiveFacts.valid leaf3743CoverageChecked

private noncomputable def leaf3743InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3743InputLogOnePlusV_eq :
    leaf3743InputLogOnePlusV = outerEnclosure 24
      (leaf3743Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3743RoundedFacts : LeafRoundedFacts 8
    leaf3743Certificate.logOnePlusV leaf3743InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3743InputLogOnePlusV_eq }

private noncomputable def leaf3743Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi65InputQChi innerPair508Input
    leaf3743InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3743LowerChecked :
    lowerCheck 24 leaf3743Box leaf3743Inputs = true := by
  rfl'

private theorem leaf3743CoversExact : CoversExact 8
    leaf3743Box leaf3743Certificate leaf3743InnerLog leaf3743Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi65RoundedFacts
    innerPair508RoundedFacts leaf3743RoundedFacts (by rfl)

private theorem leaf3743FlatSound : Sound leaf3743Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3743CertificateValid
    leaf3743InnerLogValid leaf3743CoversExact leaf3743LowerChecked

private noncomputable def leaf3744Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3744Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715771904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (246637687/134217728) }, upper := { exponent := 0, mantissa := (3857/2048) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434265599/137431543808) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3744InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3744LocalValidity :
    LeafFacts leaf3744Box leaf3744Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3744Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715771904) }) = true
      norm_num [leaf3744Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3744CertificateValid :
    WideCertificateValid leaf3744Box leaf3744Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi64ValidityFacts
    leaf3744LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3744CoverageChecked :
    coverageCheck (innerAD leaf3744Box) leaf3744InnerLog = true := by
  rfl'

private theorem leaf3744InnerLogValid :
    leaf3744InnerLog.Valid 8 (innerAD leaf3744Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3744CoverageChecked

private noncomputable def leaf3744InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3744InputLogOnePlusV_eq :
    leaf3744InputLogOnePlusV = outerEnclosure 24
      (leaf3744Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3744RoundedFacts : LeafRoundedFacts 8
    leaf3744Certificate.logOnePlusV leaf3744InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3744InputLogOnePlusV_eq }

private noncomputable def leaf3744Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi64InputQChi innerPair92Input
    leaf3744InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3744LowerChecked :
    lowerCheck 24 leaf3744Box leaf3744Inputs = true := by
  rfl'

private theorem leaf3744CoversExact : CoversExact 8
    leaf3744Box leaf3744Certificate leaf3744InnerLog leaf3744Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi64RoundedFacts
    innerPair92RoundedFacts leaf3744RoundedFacts (by rfl)

private theorem leaf3744FlatSound : Sound leaf3744Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3744CertificateValid
    leaf3744InnerLogValid leaf3744CoversExact leaf3744LowerChecked

private noncomputable def leaf3745Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3745Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715716608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (248341517/134217728) }, upper := { exponent := 0, mantissa := (971/512) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434210303/137431433216) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3745InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3745LocalValidity :
    LeafFacts leaf3745Box leaf3745Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3745Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715716608) }) = true
      norm_num [leaf3745Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3745CertificateValid :
    WideCertificateValid leaf3745Box leaf3745Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi64ValidityFacts
    leaf3745LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3745CoverageChecked :
    coverageCheck (innerAD leaf3745Box) leaf3745InnerLog = true := by
  rfl'

private theorem leaf3745InnerLogValid :
    leaf3745InnerLog.Valid 8 (innerAD leaf3745Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3745CoverageChecked

private noncomputable def leaf3745InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3745InputLogOnePlusV_eq :
    leaf3745InputLogOnePlusV = outerEnclosure 24
      (leaf3745Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3745RoundedFacts : LeafRoundedFacts 8
    leaf3745Certificate.logOnePlusV leaf3745InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3745InputLogOnePlusV_eq }

private noncomputable def leaf3745Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi64InputQChi innerPair92Input
    leaf3745InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3745LowerChecked :
    lowerCheck 24 leaf3745Box leaf3745Inputs = true := by
  rfl'

private theorem leaf3745CoversExact : CoversExact 8
    leaf3745Box leaf3745Certificate leaf3745InnerLog leaf3745Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi64RoundedFacts
    innerPair92RoundedFacts leaf3745RoundedFacts (by rfl)

private theorem leaf3745FlatSound : Sound leaf3745Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3745CertificateValid
    leaf3745InnerLogValid leaf3745CoversExact leaf3745LowerChecked

private noncomputable def leaf3746Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3746Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715634688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (250962797/134217728) }, upper := { exponent := 0, mantissa := (981/512) } }, logOuter := sk73LogOuterCertificate, logK := sk73LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434128383/137431269376) } }, logDArg := sk73LogDArgCertificate }

private noncomputable def leaf3746InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3746LocalValidity :
    LeafFacts leaf3746Box leaf3746Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3746Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715634688) }) = true
      norm_num [leaf3746Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3746CertificateValid :
    WideCertificateValid leaf3746Box leaf3746Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk73ValidityFacts chi65ValidityFacts
    leaf3746LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3746CoverageChecked :
    coverageCheck (innerAD leaf3746Box) leaf3746InnerLog = true := by
  rfl'

private theorem leaf3746InnerLogValid :
    leaf3746InnerLog.Valid 8 (innerAD leaf3746Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3746CoverageChecked

private noncomputable def leaf3746InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814715/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3746InputLogOnePlusV_eq :
    leaf3746InputLogOnePlusV = outerEnclosure 24
      (leaf3746Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3746RoundedFacts : LeafRoundedFacts 8
    leaf3746Certificate.logOnePlusV leaf3746InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3746InputLogOnePlusV_eq }

private noncomputable def leaf3746Inputs : Inputs :=
  inputsOfCaches globalInput sk73RoundedInputs
    chi65InputQChi innerPair92Input
    leaf3746InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3746LowerChecked :
    lowerCheck 24 leaf3746Box leaf3746Inputs = true := by
  rfl'

private theorem leaf3746CoversExact : CoversExact 8
    leaf3746Box leaf3746Certificate leaf3746InnerLog leaf3746Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk73RoundedFacts chi65RoundedFacts
    innerPair92RoundedFacts leaf3746RoundedFacts (by rfl)

private theorem leaf3746FlatSound : Sound leaf3746Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3746CertificateValid
    leaf3746InnerLogValid leaf3746CoversExact leaf3746LowerChecked

private noncomputable def leaf3747Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3747Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905192448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (252732159/134217728) }, upper := { exponent := 0, mantissa := (247/128) } }, logOuter := sk74LogOuterCertificate, logK := sk74LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811357013/45810384896) } }, logDArg := sk74LogDArgCertificate }

private noncomputable def leaf3747InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3747LocalValidity :
    LeafFacts leaf3747Box leaf3747Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3747Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905192448) }) = true
      norm_num [leaf3747Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3747CertificateValid :
    WideCertificateValid leaf3747Box leaf3747Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk74ValidityFacts chi65ValidityFacts
    leaf3747LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3747CoverageChecked :
    coverageCheck (innerAD leaf3747Box) leaf3747InnerLog = true := by
  rfl'

private theorem leaf3747InnerLogValid :
    leaf3747InnerLog.Valid 8 (innerAD leaf3747Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3747CoverageChecked

private noncomputable def leaf3747InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3747InputLogOnePlusV_eq :
    leaf3747InputLogOnePlusV = outerEnclosure 24
      (leaf3747Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3747RoundedFacts : LeafRoundedFacts 8
    leaf3747Certificate.logOnePlusV leaf3747InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3747InputLogOnePlusV_eq }

private noncomputable def leaf3747Inputs : Inputs :=
  inputsOfCaches globalInput sk74RoundedInputs
    chi65InputQChi innerPair100Input
    leaf3747InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3747LowerChecked :
    lowerCheck 24 leaf3747Box leaf3747Inputs = true := by
  rfl'

private theorem leaf3747CoversExact : CoversExact 8
    leaf3747Box leaf3747Certificate leaf3747InnerLog leaf3747Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk74RoundedFacts chi65RoundedFacts
    innerPair100RoundedFacts leaf3747RoundedFacts (by rfl)

private theorem leaf3747FlatSound : Sound leaf3747Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3747CertificateValid
    leaf3747InnerLogValid leaf3747CoversExact leaf3747LowerChecked

private noncomputable def leaf3748Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3748Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715943936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (241132999/134217728) }, upper := { exponent := 0, mantissa := (3773/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434437631/137431887872) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3748InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3748LocalValidity :
    LeafFacts leaf3748Box leaf3748Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3748Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715943936) }) = true
      norm_num [leaf3748Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3748CertificateValid :
    WideCertificateValid leaf3748Box leaf3748Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi62ValidityFacts
    leaf3748LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3748CoverageChecked :
    coverageCheck (innerAD leaf3748Box) leaf3748InnerLog = true := by
  rfl'

private theorem leaf3748InnerLogValid :
    leaf3748InnerLog.Valid 8 (innerAD leaf3748Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3748CoverageChecked

private noncomputable def leaf3748InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3748InputLogOnePlusV_eq :
    leaf3748InputLogOnePlusV = outerEnclosure 24
      (leaf3748Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3748RoundedFacts : LeafRoundedFacts 8
    leaf3748Certificate.logOnePlusV leaf3748InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3748InputLogOnePlusV_eq }

private noncomputable def leaf3748Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi62InputQChi innerPair72Input
    leaf3748InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3748LowerChecked :
    lowerCheck 24 leaf3748Box leaf3748Inputs = true := by
  rfl'

private theorem leaf3748CoversExact : CoversExact 8
    leaf3748Box leaf3748Certificate leaf3748InnerLog leaf3748Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi62RoundedFacts
    innerPair72RoundedFacts leaf3748RoundedFacts (by rfl)

private theorem leaf3748FlatSound : Sound leaf3748Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3748CertificateValid
    leaf3748InnerLogValid leaf3748CoversExact leaf3748LowerChecked

private noncomputable def leaf3749Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3749Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715892736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (242705765/134217728) }, upper := { exponent := 0, mantissa := (1899/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434386431/137431785472) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3749InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3749LocalValidity :
    LeafFacts leaf3749Box leaf3749Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3749Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715892736) }) = true
      norm_num [leaf3749Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3749CertificateValid :
    WideCertificateValid leaf3749Box leaf3749Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi62ValidityFacts
    leaf3749LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3749CoverageChecked :
    coverageCheck (innerAD leaf3749Box) leaf3749InnerLog = true := by
  rfl'

private theorem leaf3749InnerLogValid :
    leaf3749InnerLog.Valid 8 (innerAD leaf3749Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3749CoverageChecked

private noncomputable def leaf3749InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3749InputLogOnePlusV_eq :
    leaf3749InputLogOnePlusV = outerEnclosure 24
      (leaf3749Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3749RoundedFacts : LeafRoundedFacts 8
    leaf3749Certificate.logOnePlusV leaf3749InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3749InputLogOnePlusV_eq }

private noncomputable def leaf3749Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi62InputQChi innerPair72Input
    leaf3749InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3749LowerChecked :
    lowerCheck 24 leaf3749Box leaf3749Inputs = true := by
  rfl'

private theorem leaf3749CoversExact : CoversExact 8
    leaf3749Box leaf3749Certificate leaf3749InnerLog leaf3749Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi62RoundedFacts
    innerPair72RoundedFacts leaf3749RoundedFacts (by rfl)

private theorem leaf3749FlatSound : Sound leaf3749Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3749CertificateValid
    leaf3749InnerLogValid leaf3749CoversExact leaf3749LowerChecked

private noncomputable def leaf3750Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3750Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715802624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (245589173/134217728) }, upper := { exponent := 0, mantissa := (1921/1024) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434296319/137431605248) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3750InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3750LocalValidity :
    LeafFacts leaf3750Box leaf3750Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3750Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715802624) }) = true
      norm_num [leaf3750Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3750CertificateValid :
    WideCertificateValid leaf3750Box leaf3750Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi63ValidityFacts
    leaf3750LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3750CoverageChecked :
    coverageCheck (innerAD leaf3750Box) leaf3750InnerLog = true := by
  rfl'

private theorem leaf3750InnerLogValid :
    leaf3750InnerLog.Valid 8 (innerAD leaf3750Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3750CoverageChecked

private noncomputable def leaf3750InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3750InputLogOnePlusV_eq :
    leaf3750InputLogOnePlusV = outerEnclosure 24
      (leaf3750Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3750RoundedFacts : LeafRoundedFacts 8
    leaf3750Certificate.logOnePlusV leaf3750InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3750InputLogOnePlusV_eq }

private noncomputable def leaf3750Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi63InputQChi innerPair92Input
    leaf3750InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3750LowerChecked :
    lowerCheck 24 leaf3750Box leaf3750Inputs = true := by
  rfl'

private theorem leaf3750CoversExact : CoversExact 8
    leaf3750Box leaf3750Certificate leaf3750InnerLog leaf3750Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi63RoundedFacts
    innerPair92RoundedFacts leaf3750RoundedFacts (by rfl)

private theorem leaf3750FlatSound : Sound leaf3750Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3750CertificateValid
    leaf3750InnerLogValid leaf3750CoversExact leaf3750LowerChecked

private noncomputable def leaf3751Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3751Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905249792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (247227471/134217728) }, upper := { exponent := 0, mantissa := (967/512) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811414357/45810499584) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3751InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3751LocalValidity :
    LeafFacts leaf3751Box leaf3751Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3751Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905249792) }) = true
      norm_num [leaf3751Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3751CertificateValid :
    WideCertificateValid leaf3751Box leaf3751Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi63ValidityFacts
    leaf3751LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3751CoverageChecked :
    coverageCheck (innerAD leaf3751Box) leaf3751InnerLog = true := by
  rfl'

private theorem leaf3751InnerLogValid :
    leaf3751InnerLog.Valid 8 (innerAD leaf3751Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3751CoverageChecked

private noncomputable def leaf3751InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3751InputLogOnePlusV_eq :
    leaf3751InputLogOnePlusV = outerEnclosure 24
      (leaf3751Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3751RoundedFacts : LeafRoundedFacts 8
    leaf3751Certificate.logOnePlusV leaf3751InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3751InputLogOnePlusV_eq }

private noncomputable def leaf3751Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi63InputQChi innerPair92Input
    leaf3751InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3751LowerChecked :
    lowerCheck 24 leaf3751Box leaf3751Inputs = true := by
  rfl'

private theorem leaf3751CoversExact : CoversExact 8
    leaf3751Box leaf3751Certificate leaf3751InnerLog leaf3751Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi63RoundedFacts
    innerPair92RoundedFacts leaf3751RoundedFacts (by rfl)

private theorem leaf3751FlatSound : Sound leaf3751Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3751CertificateValid
    leaf3751InnerLogValid leaf3751CoversExact leaf3751LowerChecked

private noncomputable def leaf3752Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3752Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905280512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (244278531/134217728) }, upper := { exponent := 0, mantissa := (3823/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811445077/45810561024) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3752InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3752LocalValidity :
    LeafFacts leaf3752Box leaf3752Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3752Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905280512) }) = true
      norm_num [leaf3752Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3752CertificateValid :
    WideCertificateValid leaf3752Box leaf3752Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi62ValidityFacts
    leaf3752LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3752CoverageChecked :
    coverageCheck (innerAD leaf3752Box) leaf3752InnerLog = true := by
  rfl'

private theorem leaf3752InnerLogValid :
    leaf3752InnerLog.Valid 8 (innerAD leaf3752Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3752CoverageChecked

private noncomputable def leaf3752InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3752InputLogOnePlusV_eq :
    leaf3752InputLogOnePlusV = outerEnclosure 24
      (leaf3752Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3752RoundedFacts : LeafRoundedFacts 8
    leaf3752Certificate.logOnePlusV leaf3752InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3752InputLogOnePlusV_eq }

private noncomputable def leaf3752Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi62InputQChi innerPair91Input
    leaf3752InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3752LowerChecked :
    lowerCheck 24 leaf3752Box leaf3752Inputs = true := by
  rfl'

private theorem leaf3752CoversExact : CoversExact 8
    leaf3752Box leaf3752Certificate leaf3752InnerLog leaf3752Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi62RoundedFacts
    innerPair91RoundedFacts leaf3752RoundedFacts (by rfl)

private theorem leaf3752FlatSound : Sound leaf3752Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3752CertificateValid
    leaf3752InnerLogValid leaf3752CoversExact leaf3752LowerChecked

private noncomputable def leaf3753Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (3/8), chiHi := (25/64) }

private noncomputable def leaf3753Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715790336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (245851297/134217728) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi62LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434284031/137431580672) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3753InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3753LocalValidity :
    LeafFacts leaf3753Box leaf3753Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3753Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715790336) }) = true
      norm_num [leaf3753Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3753CertificateValid :
    WideCertificateValid leaf3753Box leaf3753Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi62ValidityFacts
    leaf3753LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3753CoverageChecked :
    coverageCheck (innerAD leaf3753Box) leaf3753InnerLog = true := by
  rfl'

private theorem leaf3753InnerLogValid :
    leaf3753InnerLog.Valid 8 (innerAD leaf3753Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3753CoverageChecked

private noncomputable def leaf3753InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3753InputLogOnePlusV_eq :
    leaf3753InputLogOnePlusV = outerEnclosure 24
      (leaf3753Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3753RoundedFacts : LeafRoundedFacts 8
    leaf3753Certificate.logOnePlusV leaf3753InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3753InputLogOnePlusV_eq }

private noncomputable def leaf3753Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi62InputQChi innerPair92Input
    leaf3753InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3753LowerChecked :
    lowerCheck 24 leaf3753Box leaf3753Inputs = true := by
  rfl'

private theorem leaf3753CoversExact : CoversExact 8
    leaf3753Box leaf3753Certificate leaf3753InnerLog leaf3753Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi62RoundedFacts
    innerPair92RoundedFacts leaf3753RoundedFacts (by rfl)

private theorem leaf3753FlatSound : Sound leaf3753Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3753CertificateValid
    leaf3753InnerLogValid leaf3753CoversExact leaf3753LowerChecked

private noncomputable def leaf3754Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3754Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715696128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (248865769/134217728) }, upper := { exponent := 0, mantissa := (1947/1024) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434189823/137431392256) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3754InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3754LocalValidity :
    LeafFacts leaf3754Box leaf3754Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3754Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715696128) }) = true
      norm_num [leaf3754Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3754CertificateValid :
    WideCertificateValid leaf3754Box leaf3754Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi63ValidityFacts
    leaf3754LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3754CoverageChecked :
    coverageCheck (innerAD leaf3754Box) leaf3754InnerLog = true := by
  rfl'

private theorem leaf3754InnerLogValid :
    leaf3754InnerLog.Valid 8 (innerAD leaf3754Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3754CoverageChecked

private noncomputable def leaf3754InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3754InputLogOnePlusV_eq :
    leaf3754InputLogOnePlusV = outerEnclosure 24
      (leaf3754Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3754RoundedFacts : LeafRoundedFacts 8
    leaf3754Certificate.logOnePlusV leaf3754InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3754InputLogOnePlusV_eq }

private noncomputable def leaf3754Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi63InputQChi innerPair92Input
    leaf3754InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3754LowerChecked :
    lowerCheck 24 leaf3754Box leaf3754Inputs = true := by
  rfl'

private theorem leaf3754CoversExact : CoversExact 8
    leaf3754Box leaf3754Certificate leaf3754InnerLog leaf3754Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi63RoundedFacts
    innerPair92RoundedFacts leaf3754RoundedFacts (by rfl)

private theorem leaf3754FlatSound : Sound leaf3754Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3754CertificateValid
    leaf3754InnerLogValid leaf3754CoversExact leaf3754LowerChecked

private noncomputable def leaf3755Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (25/64), chiHi := (13/32) }

private noncomputable def leaf3755Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (808452867/808419328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (250504067/134217728) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi63LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1616872195/1616838656) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3755InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3755LocalValidity :
    LeafFacts leaf3755Box leaf3755Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3755Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (808452867/808419328) }) = true
      norm_num [leaf3755Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3755CertificateValid :
    WideCertificateValid leaf3755Box leaf3755Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi63ValidityFacts
    leaf3755LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3755CoverageChecked :
    coverageCheck (innerAD leaf3755Box) leaf3755InnerLog = true := by
  rfl'

private theorem leaf3755InnerLogValid :
    leaf3755InnerLog.Valid 8 (innerAD leaf3755Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3755CoverageChecked

private noncomputable def leaf3755InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3755InputLogOnePlusV_eq :
    leaf3755InputLogOnePlusV = outerEnclosure 24
      (leaf3755Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3755RoundedFacts : LeafRoundedFacts 8
    leaf3755Certificate.logOnePlusV leaf3755InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3755InputLogOnePlusV_eq }

private noncomputable def leaf3755Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi63InputQChi innerPair92Input
    leaf3755InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3755LowerChecked :
    lowerCheck 24 leaf3755Box leaf3755Inputs = true := by
  rfl'

private theorem leaf3755CoversExact : CoversExact 8
    leaf3755Box leaf3755Certificate leaf3755InnerLog leaf3755Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi63RoundedFacts
    innerPair92RoundedFacts leaf3755RoundedFacts (by rfl)

private theorem leaf3755FlatSound : Sound leaf3755Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3755CertificateValid
    leaf3755InnerLogValid leaf3755CoversExact leaf3755LowerChecked

private noncomputable def leaf3756Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3756Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715661312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (250045347/134217728) }, upper := { exponent := 0, mantissa := (3911/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434155007/137431322624) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3756InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3756LocalValidity :
    LeafFacts leaf3756Box leaf3756Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3756Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715661312) }) = true
      norm_num [leaf3756Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3756CertificateValid :
    WideCertificateValid leaf3756Box leaf3756Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi64ValidityFacts
    leaf3756LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3756CoverageChecked :
    coverageCheck (innerAD leaf3756Box) leaf3756InnerLog = true := by
  rfl'

private theorem leaf3756InnerLogValid :
    leaf3756InnerLog.Valid 8 (innerAD leaf3756Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3756CoverageChecked

private noncomputable def leaf3756InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3756InputLogOnePlusV_eq :
    leaf3756InputLogOnePlusV = outerEnclosure 24
      (leaf3756Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3756RoundedFacts : LeafRoundedFacts 8
    leaf3756Certificate.logOnePlusV leaf3756InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3756InputLogOnePlusV_eq }

private noncomputable def leaf3756Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi64InputQChi innerPair92Input
    leaf3756InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3756LowerChecked :
    lowerCheck 24 leaf3756Box leaf3756Inputs = true := by
  rfl'

private theorem leaf3756CoversExact : CoversExact 8
    leaf3756Box leaf3756Certificate leaf3756InnerLog leaf3756Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi64RoundedFacts
    innerPair92RoundedFacts leaf3756RoundedFacts (by rfl)

private theorem leaf3756FlatSound : Sound leaf3756Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3756CertificateValid
    leaf3756InnerLogValid leaf3756CoversExact leaf3756LowerChecked

private noncomputable def leaf3757Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3757Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715606016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (251749177/134217728) }, upper := { exponent := 0, mantissa := (1969/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434099711/137431212032) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3757InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3757LocalValidity :
    LeafFacts leaf3757Box leaf3757Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3757Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715606016) }) = true
      norm_num [leaf3757Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3757CertificateValid :
    WideCertificateValid leaf3757Box leaf3757Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi64ValidityFacts
    leaf3757LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3757CoverageChecked :
    coverageCheck (innerAD leaf3757Box) leaf3757InnerLog = true := by
  rfl'

private theorem leaf3757InnerLogValid :
    leaf3757InnerLog.Valid 8 (innerAD leaf3757Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3757CoverageChecked

private noncomputable def leaf3757InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3757InputLogOnePlusV_eq :
    leaf3757InputLogOnePlusV = outerEnclosure 24
      (leaf3757Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3757RoundedFacts : LeafRoundedFacts 8
    leaf3757Certificate.logOnePlusV leaf3757InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3757InputLogOnePlusV_eq }

private noncomputable def leaf3757Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi64InputQChi innerPair100Input
    leaf3757InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3757LowerChecked :
    lowerCheck 24 leaf3757Box leaf3757Inputs = true := by
  rfl'

private theorem leaf3757CoversExact : CoversExact 8
    leaf3757Box leaf3757Certificate leaf3757InnerLog leaf3757Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi64RoundedFacts
    innerPair100RoundedFacts leaf3757RoundedFacts (by rfl)

private theorem leaf3757FlatSound : Sound leaf3757Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3757CertificateValid
    leaf3757InnerLogValid leaf3757CoversExact leaf3757LowerChecked

private noncomputable def leaf3758Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3758Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743104000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (254501521/134217728) }, upper := { exponent := 0, mantissa := (995/512) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486802739/27486208000) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3758InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3758LocalValidity :
    LeafFacts leaf3758Box leaf3758Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3758Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743104000) }) = true
      norm_num [leaf3758Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3758CertificateValid :
    WideCertificateValid leaf3758Box leaf3758Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi65ValidityFacts
    leaf3758LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3758CoverageChecked :
    coverageCheck (innerAD leaf3758Box) leaf3758InnerLog = true := by
  rfl'

private theorem leaf3758InnerLogValid :
    leaf3758InnerLog.Valid 8 (innerAD leaf3758Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3758CoverageChecked

private noncomputable def leaf3758InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3758InputLogOnePlusV_eq :
    leaf3758InputLogOnePlusV = outerEnclosure 24
      (leaf3758Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3758RoundedFacts : LeafRoundedFacts 8
    leaf3758Certificate.logOnePlusV leaf3758InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3758InputLogOnePlusV_eq }

private noncomputable def leaf3758Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi65InputQChi innerPair101Input
    leaf3758InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3758LowerChecked :
    lowerCheck 24 leaf3758Box leaf3758Inputs = true := by
  rfl'

private theorem leaf3758CoversExact : CoversExact 8
    leaf3758Box leaf3758Certificate leaf3758InnerLog leaf3758Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi65RoundedFacts
    innerPair101RoundedFacts leaf3758RoundedFacts (by rfl)

private theorem leaf3758FlatSound : Sound leaf3758Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3758CertificateValid
    leaf3758InnerLogValid leaf3758CoversExact leaf3758LowerChecked

private noncomputable def leaf3759Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3759Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715462656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (256270883/134217728) }, upper := { exponent := 0, mantissa := (501/256) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433956351/137430925312) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3759InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3759LocalValidity :
    LeafFacts leaf3759Box leaf3759Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3759Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715462656) }) = true
      norm_num [leaf3759Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3759CertificateValid :
    WideCertificateValid leaf3759Box leaf3759Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi65ValidityFacts
    leaf3759LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3759CoverageChecked :
    coverageCheck (innerAD leaf3759Box) leaf3759InnerLog = true := by
  rfl'

private theorem leaf3759InnerLogValid :
    leaf3759InnerLog.Valid 8 (innerAD leaf3759Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3759CoverageChecked

private noncomputable def leaf3759InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3759InputLogOnePlusV_eq :
    leaf3759InputLogOnePlusV = outerEnclosure 24
      (leaf3759Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3759RoundedFacts : LeafRoundedFacts 8
    leaf3759Certificate.logOnePlusV leaf3759InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3759InputLogOnePlusV_eq }

private noncomputable def leaf3759Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi65InputQChi innerPair101Input
    leaf3759InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3759LowerChecked :
    lowerCheck 24 leaf3759Box leaf3759Inputs = true := by
  rfl'

private theorem leaf3759CoversExact : CoversExact 8
    leaf3759Box leaf3759Certificate leaf3759InnerLog leaf3759Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi65RoundedFacts
    innerPair101RoundedFacts leaf3759RoundedFacts (by rfl)

private theorem leaf3759FlatSound : Sound leaf3759Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3759CertificateValid
    leaf3759InnerLogValid leaf3759CoversExact leaf3759LowerChecked

private noncomputable def leaf3760Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3760Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743110144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (253453007/134217728) }, upper := { exponent := 0, mantissa := (3965/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486808883/27486220288) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3760InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3760LocalValidity :
    LeafFacts leaf3760Box leaf3760Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3760Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743110144) }) = true
      norm_num [leaf3760Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3760CertificateValid :
    WideCertificateValid leaf3760Box leaf3760Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi64ValidityFacts
    leaf3760LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3760CoverageChecked :
    coverageCheck (innerAD leaf3760Box) leaf3760InnerLog = true := by
  rfl'

private theorem leaf3760InnerLogValid :
    leaf3760InnerLog.Valid 8 (innerAD leaf3760Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3760CoverageChecked

private noncomputable def leaf3760InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf3760InputLogOnePlusV_eq :
    leaf3760InputLogOnePlusV = outerEnclosure 24
      (leaf3760Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3760RoundedFacts : LeafRoundedFacts 8
    leaf3760Certificate.logOnePlusV leaf3760InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3760InputLogOnePlusV_eq }

private noncomputable def leaf3760Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi64InputQChi innerPair100Input
    leaf3760InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3760LowerChecked :
    lowerCheck 24 leaf3760Box leaf3760Inputs = true := by
  rfl'

private theorem leaf3760CoversExact : CoversExact 8
    leaf3760Box leaf3760Certificate leaf3760InnerLog leaf3760Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi64RoundedFacts
    innerPair100RoundedFacts leaf3760RoundedFacts (by rfl)

private theorem leaf3760FlatSound : Sound leaf3760Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3760CertificateValid
    leaf3760InnerLogValid leaf3760CoversExact leaf3760LowerChecked

private noncomputable def leaf3761Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (13/32), chiHi := (27/64) }

private noncomputable def leaf3761Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715495424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (255156837/134217728) }, upper := { exponent := 0, mantissa := (499/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi64LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433989119/137430990848) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3761InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3761LocalValidity :
    LeafFacts leaf3761Box leaf3761Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3761Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715495424) }) = true
      norm_num [leaf3761Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3761CertificateValid :
    WideCertificateValid leaf3761Box leaf3761Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi64ValidityFacts
    leaf3761LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3761CoverageChecked :
    coverageCheck (innerAD leaf3761Box) leaf3761InnerLog = true := by
  rfl'

private theorem leaf3761InnerLogValid :
    leaf3761InnerLog.Valid 8 (innerAD leaf3761Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3761CoverageChecked

private noncomputable def leaf3761InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3761InputLogOnePlusV_eq :
    leaf3761InputLogOnePlusV = outerEnclosure 24
      (leaf3761Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3761RoundedFacts : LeafRoundedFacts 8
    leaf3761Certificate.logOnePlusV leaf3761InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3761InputLogOnePlusV_eq }

private noncomputable def leaf3761Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi64InputQChi innerPair101Input
    leaf3761InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3761LowerChecked :
    lowerCheck 24 leaf3761Box leaf3761Inputs = true := by
  rfl'

private theorem leaf3761CoversExact : CoversExact 8
    leaf3761Box leaf3761Certificate leaf3761InnerLog leaf3761Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi64RoundedFacts
    innerPair101RoundedFacts leaf3761RoundedFacts (by rfl)

private theorem leaf3761FlatSound : Sound leaf3761Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3761CertificateValid
    leaf3761InnerLogValid leaf3761CoversExact leaf3761LowerChecked

private noncomputable def leaf3762Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3762Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905135104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (258040245/134217728) }, upper := { exponent := 0, mantissa := (1009/512) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811299669/45810270208) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3762InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3762LocalValidity :
    LeafFacts leaf3762Box leaf3762Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3762Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905135104) }) = true
      norm_num [leaf3762Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3762CertificateValid :
    WideCertificateValid leaf3762Box leaf3762Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi65ValidityFacts
    leaf3762LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3762CoverageChecked :
    coverageCheck (innerAD leaf3762Box) leaf3762InnerLog = true := by
  rfl'

private theorem leaf3762InnerLogValid :
    leaf3762InnerLog.Valid 8 (innerAD leaf3762Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3762CoverageChecked

private noncomputable def leaf3762InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3762InputLogOnePlusV_eq :
    leaf3762InputLogOnePlusV = outerEnclosure 24
      (leaf3762Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3762RoundedFacts : LeafRoundedFacts 8
    leaf3762Certificate.logOnePlusV leaf3762InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3762InputLogOnePlusV_eq }

private noncomputable def leaf3762Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi65InputQChi innerPair101Input
    leaf3762InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3762LowerChecked :
    lowerCheck 24 leaf3762Box leaf3762Inputs = true := by
  rfl'

private theorem leaf3762CoversExact : CoversExact 8
    leaf3762Box leaf3762Certificate leaf3762InnerLog leaf3762Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi65RoundedFacts
    innerPair101RoundedFacts leaf3762RoundedFacts (by rfl)

private theorem leaf3762FlatSound : Sound leaf3762Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3762CertificateValid
    leaf3762InnerLogValid leaf3762CoversExact leaf3762LowerChecked

private noncomputable def leaf3763Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (27/64), chiHi := (7/16) }

private noncomputable def leaf3763Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (1108345889/1108312064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (259809607/134217728) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi65LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2216657953/2216624128) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3763InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3763LocalValidity :
    LeafFacts leaf3763Box leaf3763Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3763Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1108345889/1108312064) }) = true
      norm_num [leaf3763Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3763CertificateValid :
    WideCertificateValid leaf3763Box leaf3763Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi65ValidityFacts
    leaf3763LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3763CoverageChecked :
    coverageCheck (innerAD leaf3763Box) leaf3763InnerLog = true := by
  rfl'

private theorem leaf3763InnerLogValid :
    leaf3763InnerLog.Valid 8 (innerAD leaf3763Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3763CoverageChecked

private noncomputable def leaf3763InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3763InputLogOnePlusV_eq :
    leaf3763InputLogOnePlusV = outerEnclosure 24
      (leaf3763Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3763RoundedFacts : LeafRoundedFacts 8
    leaf3763Certificate.logOnePlusV leaf3763InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3763InputLogOnePlusV_eq }

private noncomputable def leaf3763Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi65InputQChi innerPair101Input
    leaf3763InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3763LowerChecked :
    lowerCheck 24 leaf3763Box leaf3763Inputs = true := by
  rfl'

private theorem leaf3763CoversExact : CoversExact 8
    leaf3763Box leaf3763Certificate leaf3763InnerLog leaf3763Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi65RoundedFacts
    innerPair101RoundedFacts leaf3763RoundedFacts (by rfl)

private theorem leaf3763FlatSound : Sound leaf3763Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3763CertificateValid
    leaf3763InnerLogValid leaf3763CoversExact leaf3763LowerChecked

private noncomputable def leaf3764Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3764Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108987/67108864) }, vSqrt := { lower := (65531/65536), upper := (34359279615/34357778432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (125792647/67108864) }, upper := { exponent := 0, mantissa := (1981/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68717058047/68715556864) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf3764InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3764LocalValidity :
    LeafFacts leaf3764Box leaf3764Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3764Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34359279615/34357778432) }) = true
      norm_num [leaf3764Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3764CertificateValid :
    WideCertificateValid leaf3764Box leaf3764Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi66ValidityFacts
    leaf3764LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3764CoverageChecked :
    coverageCheck (innerAD leaf3764Box) leaf3764InnerLog = true := by
  rfl'

private theorem leaf3764InnerLogValid :
    leaf3764InnerLog.Valid 8 (innerAD leaf3764Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3764CoverageChecked

private noncomputable def leaf3764InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3764InputLogOnePlusV_eq :
    leaf3764InputLogOnePlusV = outerEnclosure 24
      (leaf3764Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3764RoundedFacts : LeafRoundedFacts 8
    leaf3764Certificate.logOnePlusV leaf3764InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3764InputLogOnePlusV_eq }

private noncomputable def leaf3764Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi66InputQChi innerPair92Input
    leaf3764InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3764LowerChecked :
    lowerCheck 24 leaf3764Box leaf3764Inputs = true := by
  rfl'

private theorem leaf3764CoversExact : CoversExact 8
    leaf3764Box leaf3764Certificate leaf3764InnerLog leaf3764Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi66RoundedFacts
    innerPair92RoundedFacts leaf3764RoundedFacts (by rfl)

private theorem leaf3764FlatSound : Sound leaf3764Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3764CertificateValid
    leaf3764InnerLogValid leaf3764CoversExact leaf3764LowerChecked

private noncomputable def leaf3765Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3765Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108989/67108864) }, vSqrt := { lower := (65531/65536), upper := (34359279615/34357710848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (127889669/67108864) }, upper := { exponent := 0, mantissa := (1007/512) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716990463/68715421696) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf3765InnerLog : WideLogData :=
  innerPair230Data

set_option maxRecDepth 1000000 in
private theorem leaf3765LocalValidity :
    LeafFacts leaf3765Box leaf3765Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3765Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34359279615/34357710848) }) = true
      norm_num [leaf3765Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3765CertificateValid :
    WideCertificateValid leaf3765Box leaf3765Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi67ValidityFacts
    leaf3765LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3765CoverageChecked :
    coverageCheck (innerAD leaf3765Box) leaf3765InnerLog = true := by
  rfl'

private theorem leaf3765InnerLogValid :
    leaf3765InnerLog.Valid 8 (innerAD leaf3765Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint85PositiveFacts.valid leaf3765CoverageChecked

private noncomputable def leaf3765InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3765InputLogOnePlusV_eq :
    leaf3765InputLogOnePlusV = outerEnclosure 24
      (leaf3765Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3765RoundedFacts : LeafRoundedFacts 8
    leaf3765Certificate.logOnePlusV leaf3765InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3765InputLogOnePlusV_eq }

private noncomputable def leaf3765Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi67InputQChi innerPair230Input
    leaf3765InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3765LowerChecked :
    lowerCheck 24 leaf3765Box leaf3765Inputs = true := by
  rfl'

private theorem leaf3765CoversExact : CoversExact 8
    leaf3765Box leaf3765Certificate leaf3765InnerLog leaf3765Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi67RoundedFacts
    innerPair230RoundedFacts leaf3765RoundedFacts (by rfl)

private theorem leaf3765FlatSound : Sound leaf3765Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3765CertificateValid
    leaf3765InnerLogValid leaf3765CoversExact leaf3765LowerChecked

private noncomputable def leaf3766Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3766Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108989/67108864) }, vSqrt := { lower := (65531/65536), upper := (6871855923/6871543808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (127627541/67108864) }, upper := { exponent := 0, mantissa := (1005/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (13743399731/13743087616) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf3766InnerLog : WideLogData :=
  innerPair546Data

set_option maxRecDepth 1000000 in
private theorem leaf3766LocalValidity :
    LeafFacts leaf3766Box leaf3766Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3766Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (6871855923/6871543808) }) = true
      norm_num [leaf3766Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3766CertificateValid :
    WideCertificateValid leaf3766Box leaf3766Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi66ValidityFacts
    leaf3766LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3766CoverageChecked :
    coverageCheck (innerAD leaf3766Box) leaf3766InnerLog = true := by
  rfl'

private theorem leaf3766InnerLogValid :
    leaf3766InnerLog.Valid 8 (innerAD leaf3766Box) :=
  wideLogDataValid_of_cachedCheck endpoint280PositiveFacts
    endpoint281PositiveFacts.valid leaf3766CoverageChecked

private noncomputable def leaf3766InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3766InputLogOnePlusV_eq :
    leaf3766InputLogOnePlusV = outerEnclosure 24
      (leaf3766Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3766RoundedFacts : LeafRoundedFacts 8
    leaf3766Certificate.logOnePlusV leaf3766InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3766InputLogOnePlusV_eq }

private noncomputable def leaf3766Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi66InputQChi innerPair546Input
    leaf3766InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3766LowerChecked :
    lowerCheck 24 leaf3766Box leaf3766Inputs = true := by
  rfl'

private theorem leaf3766CoversExact : CoversExact 8
    leaf3766Box leaf3766Certificate leaf3766InnerLog leaf3766Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi66RoundedFacts
    innerPair546RoundedFacts leaf3766RoundedFacts (by rfl)

private theorem leaf3766FlatSound : Sound leaf3766Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3766CertificateValid
    leaf3766InnerLogValid leaf3766CoversExact leaf3766LowerChecked

private noncomputable def leaf3767Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3767Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108991/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178824704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (129790095/67108864) }, upper := { exponent := 0, mantissa := (511/256) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358202367/34357649408) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf3767InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3767LocalValidity :
    LeafFacts leaf3767Box leaf3767Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3767Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178824704) }) = true
      norm_num [leaf3767Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3767CertificateValid :
    WideCertificateValid leaf3767Box leaf3767Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi67ValidityFacts
    leaf3767LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3767CoverageChecked :
    coverageCheck (innerAD leaf3767Box) leaf3767InnerLog = true := by
  rfl'

private theorem leaf3767InnerLogValid :
    leaf3767InnerLog.Valid 8 (innerAD leaf3767Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3767CoverageChecked

private noncomputable def leaf3767InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3767InputLogOnePlusV_eq :
    leaf3767InputLogOnePlusV = outerEnclosure 24
      (leaf3767Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3767RoundedFacts : LeafRoundedFacts 8
    leaf3767Certificate.logOnePlusV leaf3767InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3767InputLogOnePlusV_eq }

private noncomputable def leaf3767Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi67InputQChi innerPair101Input
    leaf3767InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3767LowerChecked :
    lowerCheck 24 leaf3767Box leaf3767Inputs = true := by
  rfl'

private theorem leaf3767CoversExact : CoversExact 8
    leaf3767Box leaf3767Certificate leaf3767InnerLog leaf3767Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi67RoundedFacts
    innerPair101RoundedFacts leaf3767RoundedFacts (by rfl)

private theorem leaf3767FlatSound : Sound leaf3767Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3767CertificateValid
    leaf3767InnerLogValid leaf3767CoversExact leaf3767LowerChecked

private noncomputable def leaf3768Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3768Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108991/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454117376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (129986691/67108864) }, upper := { exponent := 0, mantissa := (2047/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908314185/4908234752) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf3768InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3768LocalValidity :
    LeafFacts leaf3768Box leaf3768Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3768Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454117376) }) = true
      norm_num [leaf3768Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3768CertificateValid :
    WideCertificateValid leaf3768Box leaf3768Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi68ValidityFacts
    leaf3768LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3768CoverageChecked :
    coverageCheck (innerAD leaf3768Box) leaf3768InnerLog = true := by
  rfl'

private theorem leaf3768InnerLogValid :
    leaf3768InnerLog.Valid 8 (innerAD leaf3768Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3768CoverageChecked

private noncomputable def leaf3768InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3768InputLogOnePlusV_eq :
    leaf3768InputLogOnePlusV = outerEnclosure 24
      (leaf3768Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3768RoundedFacts : LeafRoundedFacts 8
    leaf3768Certificate.logOnePlusV leaf3768InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3768InputLogOnePlusV_eq }

private noncomputable def leaf3768Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi68InputQChi innerPair101Input
    leaf3768InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3768LowerChecked :
    lowerCheck 24 leaf3768Box leaf3768Inputs = true := by
  rfl'

private theorem leaf3768CoversExact : CoversExact 8
    leaf3768Box leaf3768Certificate leaf3768InnerLog leaf3768Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi68RoundedFacts
    innerPair101RoundedFacts leaf3768RoundedFacts (by rfl)

private theorem leaf3768FlatSound : Sound leaf3768Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3768CertificateValid
    leaf3768InnerLogValid leaf3768CoversExact leaf3768LowerChecked

private noncomputable def leaf3769Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3769Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108993/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178787840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (132083713/67108864) }, upper := { exponent := 1, mantissa := (65/64) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358165503/34357575680) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf3769InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3769LocalValidity :
    LeafFacts leaf3769Box leaf3769Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3769Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178787840) }) = true
      norm_num [leaf3769Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3769CertificateValid :
    WideCertificateValid leaf3769Box leaf3769Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi69ValidityFacts
    leaf3769LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3769CoverageChecked :
    coverageCheck (innerAD leaf3769Box) leaf3769InnerLog = true := by
  rfl'

private theorem leaf3769InnerLogValid :
    leaf3769InnerLog.Valid 8 (innerAD leaf3769Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3769CoverageChecked

private noncomputable def leaf3769InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3769InputLogOnePlusV_eq :
    leaf3769InputLogOnePlusV = outerEnclosure 24
      (leaf3769Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3769RoundedFacts : LeafRoundedFacts 8
    leaf3769Certificate.logOnePlusV leaf3769InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3769InputLogOnePlusV_eq }

private noncomputable def leaf3769Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi69InputQChi innerPair110Input
    leaf3769InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3769LowerChecked :
    lowerCheck 24 leaf3769Box leaf3769Inputs = true := by
  rfl'

private theorem leaf3769CoversExact : CoversExact 8
    leaf3769Box leaf3769Certificate leaf3769InnerLog leaf3769Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi69RoundedFacts
    innerPair110RoundedFacts leaf3769RoundedFacts (by rfl)

private theorem leaf3769FlatSound : Sound leaf3769Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3769CertificateValid
    leaf3769InnerLogValid leaf3769CoversExact leaf3769LowerChecked

private noncomputable def leaf3770Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3770Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108993/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726263296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (131952649/67108864) }, upper := { exponent := 1, mantissa := (1039/1024) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452722517/11452526592) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf3770InnerLog : WideLogData :=
  innerPair237Data

set_option maxRecDepth 1000000 in
private theorem leaf3770LocalValidity :
    LeafFacts leaf3770Box leaf3770Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3770Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726263296) }) = true
      norm_num [leaf3770Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3770CertificateValid :
    WideCertificateValid leaf3770Box leaf3770Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi68ValidityFacts
    leaf3770LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3770CoverageChecked :
    coverageCheck (innerAD leaf3770Box) leaf3770InnerLog = true := by
  rfl'

private theorem leaf3770InnerLogValid :
    leaf3770InnerLog.Valid 8 (innerAD leaf3770Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint82PositiveFacts.valid leaf3770CoverageChecked

private noncomputable def leaf3770InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3770InputLogOnePlusV_eq :
    leaf3770InputLogOnePlusV = outerEnclosure 24
      (leaf3770Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3770RoundedFacts : LeafRoundedFacts 8
    leaf3770Certificate.logOnePlusV leaf3770InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3770InputLogOnePlusV_eq }

private noncomputable def leaf3770Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi68InputQChi innerPair237Input
    leaf3770InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3770LowerChecked :
    lowerCheck 24 leaf3770Box leaf3770Inputs = true := by
  rfl'

private theorem leaf3770CoversExact : CoversExact 8
    leaf3770Box leaf3770Certificate leaf3770InnerLog leaf3770Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi68RoundedFacts
    innerPair237RoundedFacts leaf3770RoundedFacts (by rfl)

private theorem leaf3770FlatSound : Sound leaf3770Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3770CertificateValid
    leaf3770InnerLogValid leaf3770CoversExact leaf3770LowerChecked

private noncomputable def leaf3771Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3771Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108995/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178755072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (134115203/67108864) }, upper := { exponent := 1, mantissa := (33/32) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358132735/34357510144) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf3771InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3771LocalValidity :
    LeafFacts leaf3771Box leaf3771Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3771Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178755072) }) = true
      norm_num [leaf3771Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3771CertificateValid :
    WideCertificateValid leaf3771Box leaf3771Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi69ValidityFacts
    leaf3771LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3771CoverageChecked :
    coverageCheck (innerAD leaf3771Box) leaf3771InnerLog = true := by
  rfl'

private theorem leaf3771InnerLogValid :
    leaf3771InnerLog.Valid 8 (innerAD leaf3771Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3771CoverageChecked

private noncomputable def leaf3771InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3771InputLogOnePlusV_eq :
    leaf3771InputLogOnePlusV = outerEnclosure 24
      (leaf3771Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3771RoundedFacts : LeafRoundedFacts 8
    leaf3771Certificate.logOnePlusV leaf3771InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3771InputLogOnePlusV_eq }

private noncomputable def leaf3771Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi69InputQChi innerPair110Input
    leaf3771InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3771LowerChecked :
    lowerCheck 24 leaf3771Box leaf3771Inputs = true := by
  rfl'

private theorem leaf3771CoversExact : CoversExact 8
    leaf3771Box leaf3771Certificate leaf3771InnerLog leaf3771Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi69RoundedFacts
    innerPair110RoundedFacts leaf3771RoundedFacts (by rfl)

private theorem leaf3771FlatSound : Sound leaf3771Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3771CertificateValid
    leaf3771InnerLogValid leaf3771CoversExact leaf3771LowerChecked

private noncomputable def leaf3772Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3772Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715378688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (258957695/134217728) }, upper := { exponent := 0, mantissa := (4049/2048) } }, logOuter := sk75LogOuterCertificate, logK := sk75LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137433872383/137430757376) } }, logDArg := sk75LogDArgCertificate }

private noncomputable def leaf3772InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3772LocalValidity :
    LeafFacts leaf3772Box leaf3772Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3772Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715378688) }) = true
      norm_num [leaf3772Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3772CertificateValid :
    WideCertificateValid leaf3772Box leaf3772Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk75ValidityFacts chi66ValidityFacts
    leaf3772LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3772CoverageChecked :
    coverageCheck (innerAD leaf3772Box) leaf3772InnerLog = true := by
  rfl'

private theorem leaf3772InnerLogValid :
    leaf3772InnerLog.Valid 8 (innerAD leaf3772Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3772CoverageChecked

private noncomputable def leaf3772InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3772InputLogOnePlusV_eq :
    leaf3772InputLogOnePlusV = outerEnclosure 24
      (leaf3772Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3772RoundedFacts : LeafRoundedFacts 8
    leaf3772Certificate.logOnePlusV leaf3772InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3772InputLogOnePlusV_eq }

private noncomputable def leaf3772Inputs : Inputs :=
  inputsOfCaches globalInput sk75RoundedInputs
    chi66InputQChi innerPair101Input
    leaf3772InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3772LowerChecked :
    lowerCheck 24 leaf3772Box leaf3772Inputs = true := by
  rfl'

private theorem leaf3772CoversExact : CoversExact 8
    leaf3772Box leaf3772Certificate leaf3772InnerLog leaf3772Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk75RoundedFacts chi66RoundedFacts
    innerPair101RoundedFacts leaf3772RoundedFacts (by rfl)

private theorem leaf3772FlatSound : Sound leaf3772Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3772CertificateValid
    leaf3772InnerLogValid leaf3772CoversExact leaf3772LowerChecked

private noncomputable def leaf3773Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3773Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357659648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (260792589/134217728) }, upper := { exponent := 0, mantissa := (2039/1024) } }, logOuter := sk76LogOuterCertificate, logK := sk76LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716382207/68715319296) } }, logDArg := sk76LogDArgCertificate }

private noncomputable def leaf3773InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3773LocalValidity :
    LeafFacts leaf3773Box leaf3773Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3773Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357659648) }) = true
      norm_num [leaf3773Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3773CertificateValid :
    WideCertificateValid leaf3773Box leaf3773Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk76ValidityFacts chi66ValidityFacts
    leaf3773LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3773CoverageChecked :
    coverageCheck (innerAD leaf3773Box) leaf3773InnerLog = true := by
  rfl'

private theorem leaf3773InnerLogValid :
    leaf3773InnerLog.Valid 8 (innerAD leaf3773Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3773CoverageChecked

private noncomputable def leaf3773InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3773InputLogOnePlusV_eq :
    leaf3773InputLogOnePlusV = outerEnclosure 24
      (leaf3773Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3773RoundedFacts : LeafRoundedFacts 8
    leaf3773Certificate.logOnePlusV leaf3773InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3773InputLogOnePlusV_eq }

private noncomputable def leaf3773Inputs : Inputs :=
  inputsOfCaches globalInput sk76RoundedInputs
    chi66InputQChi innerPair108Input
    leaf3773InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3773LowerChecked :
    lowerCheck 24 leaf3773Box leaf3773Inputs = true := by
  rfl'

private theorem leaf3773CoversExact : CoversExact 8
    leaf3773Box leaf3773Certificate leaf3773InnerLog leaf3773Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk76RoundedFacts chi66RoundedFacts
    innerPair108RoundedFacts leaf3773RoundedFacts (by rfl)

private theorem leaf3773FlatSound : Sound leaf3773Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3773CertificateValid
    leaf3773InnerLogValid leaf3773CoversExact leaf3773LowerChecked

private noncomputable def leaf3774Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3774Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108993/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178793984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (131690521/67108864) }, upper := { exponent := 1, mantissa := (1037/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358171647/34357587968) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf3774InnerLog : WideLogData :=
  innerPair537Data

set_option maxRecDepth 1000000 in
private theorem leaf3774LocalValidity :
    LeafFacts leaf3774Box leaf3774Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3774Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178793984) }) = true
      norm_num [leaf3774Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3774CertificateValid :
    WideCertificateValid leaf3774Box leaf3774Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi67ValidityFacts
    leaf3774LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3774CoverageChecked :
    coverageCheck (innerAD leaf3774Box) leaf3774InnerLog = true := by
  rfl'

private theorem leaf3774InnerLogValid :
    leaf3774InnerLog.Valid 8 (innerAD leaf3774Box) :=
  wideLogDataValid_of_cachedCheck endpoint272PositiveFacts
    endpoint282PositiveFacts.valid leaf3774CoverageChecked

private noncomputable def leaf3774InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3774InputLogOnePlusV_eq :
    leaf3774InputLogOnePlusV = outerEnclosure 24
      (leaf3774Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3774RoundedFacts : LeafRoundedFacts 8
    leaf3774Certificate.logOnePlusV leaf3774InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3774InputLogOnePlusV_eq }

private noncomputable def leaf3774Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi67InputQChi innerPair537Input
    leaf3774InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3774LowerChecked :
    lowerCheck 24 leaf3774Box leaf3774Inputs = true := by
  rfl'

private theorem leaf3774CoversExact : CoversExact 8
    leaf3774Box leaf3774Certificate leaf3774InnerLog leaf3774Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi67RoundedFacts
    innerPair537RoundedFacts leaf3774RoundedFacts (by rfl)

private theorem leaf3774FlatSound : Sound leaf3774Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3774CertificateValid
    leaf3774InnerLogValid leaf3774CoversExact leaf3774LowerChecked

private noncomputable def leaf3775Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3775Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (2021101327/2021037056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (262627483/134217728) }, upper := { exponent := 1, mantissa := (4107/4096) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4042138383/4042074112) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3775InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3775LocalValidity :
    LeafFacts leaf3775Box leaf3775Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3775Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2021101327/2021037056) }) = true
      norm_num [leaf3775Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3775CertificateValid :
    WideCertificateValid leaf3775Box leaf3775Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi66ValidityFacts
    leaf3775LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3775CoverageChecked :
    coverageCheck (innerAD leaf3775Box) leaf3775InnerLog = true := by
  rfl'

private theorem leaf3775InnerLogValid :
    leaf3775InnerLog.Valid 8 (innerAD leaf3775Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3775CoverageChecked

private noncomputable def leaf3775InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3775InputLogOnePlusV_eq :
    leaf3775InputLogOnePlusV = outerEnclosure 24
      (leaf3775Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3775RoundedFacts : LeafRoundedFacts 8
    leaf3775Certificate.logOnePlusV leaf3775InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3775InputLogOnePlusV_eq }

private noncomputable def leaf3775Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi66InputQChi innerPair110Input
    leaf3775InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3775LowerChecked :
    lowerCheck 24 leaf3775Box leaf3775Inputs = true := by
  rfl'

private theorem leaf3775CoversExact : CoversExact 8
    leaf3775Box leaf3775Certificate leaf3775InnerLog leaf3775Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi66RoundedFacts
    innerPair110RoundedFacts leaf3775RoundedFacts (by rfl)

private theorem leaf3775FlatSound : Sound leaf3775Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3775CertificateValid
    leaf3775InnerLogValid leaf3775CoversExact leaf3775LowerChecked

private noncomputable def leaf3776Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf3776Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (4908388937/4908228608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (264462377/134217728) }, upper := { exponent := 1, mantissa := (517/512) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9816617545/9816457216) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3776InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3776LocalValidity :
    LeafFacts leaf3776Box leaf3776Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3776Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4908388937/4908228608) }) = true
      norm_num [leaf3776Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3776CertificateValid :
    WideCertificateValid leaf3776Box leaf3776Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi66ValidityFacts
    leaf3776LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3776CoverageChecked :
    coverageCheck (innerAD leaf3776Box) leaf3776InnerLog = true := by
  rfl'

private theorem leaf3776InnerLogValid :
    leaf3776InnerLog.Valid 8 (innerAD leaf3776Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3776CoverageChecked

private noncomputable def leaf3776InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3776InputLogOnePlusV_eq :
    leaf3776InputLogOnePlusV = outerEnclosure 24
      (leaf3776Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3776RoundedFacts : LeafRoundedFacts 8
    leaf3776Certificate.logOnePlusV leaf3776InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3776InputLogOnePlusV_eq }

private noncomputable def leaf3776Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi66InputQChi innerPair110Input
    leaf3776InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3776LowerChecked :
    lowerCheck 24 leaf3776Box leaf3776Inputs = true := by
  rfl'

private theorem leaf3776CoversExact : CoversExact 8
    leaf3776Box leaf3776Certificate leaf3776InnerLog leaf3776Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi66RoundedFacts
    innerPair110RoundedFacts leaf3776RoundedFacts (by rfl)

private theorem leaf3776FlatSound : Sound leaf3776Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3776CertificateValid
    leaf3776InnerLogValid leaf3776CoversExact leaf3776LowerChecked

private noncomputable def leaf3777Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3777Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (4908388937/4908222464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (267214721/134217728) }, upper := { exponent := 1, mantissa := (2089/2048) } }, logOuter := sk77LogOuterCertificate, logK := sk77LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9816611401/9816444928) } }, logDArg := sk77LogDArgCertificate }

private noncomputable def leaf3777InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3777LocalValidity :
    LeafFacts leaf3777Box leaf3777Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3777Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4908388937/4908222464) }) = true
      norm_num [leaf3777Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3777CertificateValid :
    WideCertificateValid leaf3777Box leaf3777Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk77ValidityFacts chi67ValidityFacts
    leaf3777LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3777CoverageChecked :
    coverageCheck (innerAD leaf3777Box) leaf3777InnerLog = true := by
  rfl'

private theorem leaf3777InnerLogValid :
    leaf3777InnerLog.Valid 8 (innerAD leaf3777Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3777CoverageChecked

private noncomputable def leaf3777InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3777InputLogOnePlusV_eq :
    leaf3777InputLogOnePlusV = outerEnclosure 24
      (leaf3777Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3777RoundedFacts : LeafRoundedFacts 8
    leaf3777Certificate.logOnePlusV leaf3777InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3777InputLogOnePlusV_eq }

private noncomputable def leaf3777Inputs : Inputs :=
  inputsOfCaches globalInput sk77RoundedInputs
    chi67InputQChi innerPair110Input
    leaf3777InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3777LowerChecked :
    lowerCheck 24 leaf3777Box leaf3777Inputs = true := by
  rfl'

private theorem leaf3777CoversExact : CoversExact 8
    leaf3777Box leaf3777Certificate leaf3777InnerLog leaf3777Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk77RoundedFacts chi67RoundedFacts
    innerPair110RoundedFacts leaf3777RoundedFacts (by rfl)

private theorem leaf3777FlatSound : Sound leaf3777Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3777CertificateValid
    leaf3777InnerLogValid leaf3777CoversExact leaf3777LowerChecked

private noncomputable def leaf3778Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf3778Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357526528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (269115147/268435456) }, upper := { exponent := 1, mantissa := (263/256) } }, logOuter := sk78LogOuterCertificate, logK := sk78LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68716249087/68715053056) } }, logDArg := sk78LogDArgCertificate }

private noncomputable def leaf3778InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf3778LocalValidity :
    LeafFacts leaf3778Box leaf3778Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3778Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357526528) }) = true
      norm_num [leaf3778Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3778CertificateValid :
    WideCertificateValid leaf3778Box leaf3778Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk78ValidityFacts chi67ValidityFacts
    leaf3778LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3778CoverageChecked :
    coverageCheck (innerAD leaf3778Box) leaf3778InnerLog = true := by
  rfl'

private theorem leaf3778InnerLogValid :
    leaf3778InnerLog.Valid 8 (innerAD leaf3778Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf3778CoverageChecked

private noncomputable def leaf3778InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3778InputLogOnePlusV_eq :
    leaf3778InputLogOnePlusV = outerEnclosure 24
      (leaf3778Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3778RoundedFacts : LeafRoundedFacts 8
    leaf3778Certificate.logOnePlusV leaf3778InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3778InputLogOnePlusV_eq }

private noncomputable def leaf3778Inputs : Inputs :=
  inputsOfCaches globalInput sk78RoundedInputs
    chi67InputQChi innerPair116Input
    leaf3778InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3778LowerChecked :
    lowerCheck 24 leaf3778Box leaf3778Inputs = true := by
  rfl'

private theorem leaf3778CoversExact : CoversExact 8
    leaf3778Box leaf3778Certificate leaf3778InnerLog leaf3778Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk78RoundedFacts chi67RoundedFacts
    innerPair116RoundedFacts leaf3778RoundedFacts (by rfl)

private theorem leaf3778FlatSound : Sound leaf3778Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3778CertificateValid
    leaf3778InnerLogValid leaf3778CoversExact leaf3778LowerChecked

private noncomputable def leaf3779Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3779Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108995/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178758144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (133918607/67108864) }, upper := { exponent := 1, mantissa := (2109/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358135807/34357516288) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf3779InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3779LocalValidity :
    LeafFacts leaf3779Box leaf3779Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3779Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178758144) }) = true
      norm_num [leaf3779Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3779CertificateValid :
    WideCertificateValid leaf3779Box leaf3779Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi68ValidityFacts
    leaf3779LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3779CoverageChecked :
    coverageCheck (innerAD leaf3779Box) leaf3779InnerLog = true := by
  rfl'

private theorem leaf3779InnerLogValid :
    leaf3779InnerLog.Valid 8 (innerAD leaf3779Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3779CoverageChecked

private noncomputable def leaf3779InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3779InputLogOnePlusV_eq :
    leaf3779InputLogOnePlusV = outerEnclosure 24
      (leaf3779Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3779RoundedFacts : LeafRoundedFacts 8
    leaf3779Certificate.logOnePlusV leaf3779InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3779InputLogOnePlusV_eq }

private noncomputable def leaf3779Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi68InputQChi innerPair110Input
    leaf3779InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3779LowerChecked :
    lowerCheck 24 leaf3779Box leaf3779Inputs = true := by
  rfl'

private theorem leaf3779CoversExact : CoversExact 8
    leaf3779Box leaf3779Certificate leaf3779InnerLog leaf3779Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi68RoundedFacts
    innerPair110RoundedFacts leaf3779RoundedFacts (by rfl)

private theorem leaf3779FlatSound : Sound leaf3779Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3779CertificateValid
    leaf3779InnerLogValid leaf3779CoversExact leaf3779LowerChecked

private noncomputable def leaf3780Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3780Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108997/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726240768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (136146693/134217728) }, upper := { exponent := 1, mantissa := (67/64) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452699989/11452481536) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf3780InnerLog : WideLogData :=
  innerPair549Data

set_option maxRecDepth 1000000 in
private theorem leaf3780LocalValidity :
    LeafFacts leaf3780Box leaf3780Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3780Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726240768) }) = true
      norm_num [leaf3780Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3780CertificateValid :
    WideCertificateValid leaf3780Box leaf3780Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi69ValidityFacts
    leaf3780LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3780CoverageChecked :
    coverageCheck (innerAD leaf3780Box) leaf3780InnerLog = true := by
  rfl'

private theorem leaf3780InnerLogValid :
    leaf3780InnerLog.Valid 8 (innerAD leaf3780Box) :=
  wideLogDataValid_of_cachedCheck endpoint283PositiveFacts
    endpoint284PositiveFacts.valid leaf3780CoverageChecked

private noncomputable def leaf3780InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3780InputLogOnePlusV_eq :
    leaf3780InputLogOnePlusV = outerEnclosure 24
      (leaf3780Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3780RoundedFacts : LeafRoundedFacts 8
    leaf3780Certificate.logOnePlusV leaf3780InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3780InputLogOnePlusV_eq }

private noncomputable def leaf3780Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi69InputQChi innerPair549Input
    leaf3780InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3780LowerChecked :
    lowerCheck 24 leaf3780Box leaf3780Inputs = true := by
  rfl'

private theorem leaf3780CoversExact : CoversExact 8
    leaf3780Box leaf3780Certificate leaf3780InnerLog leaf3780Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi69RoundedFacts
    innerPair549RoundedFacts leaf3780RoundedFacts (by rfl)

private theorem leaf3780FlatSound : Sound leaf3780Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3780CertificateValid
    leaf3780InnerLogValid leaf3780CoversExact leaf3780LowerChecked

private noncomputable def leaf3781Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf3781Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108997/67108864) }, vSqrt := { lower := (65531/65536), upper := (113770713/113766400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (135884565/134217728) }, upper := { exponent := 1, mantissa := (535/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (227537113/227532800) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf3781InnerLog : WideLogData :=
  innerPair552Data

set_option maxRecDepth 1000000 in
private theorem leaf3781LocalValidity :
    LeafFacts leaf3781Box leaf3781Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3781Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (113770713/113766400) }) = true
      norm_num [leaf3781Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3781CertificateValid :
    WideCertificateValid leaf3781Box leaf3781Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi68ValidityFacts
    leaf3781LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3781CoverageChecked :
    coverageCheck (innerAD leaf3781Box) leaf3781InnerLog = true := by
  rfl'

private theorem leaf3781InnerLogValid :
    leaf3781InnerLog.Valid 8 (innerAD leaf3781Box) :=
  wideLogDataValid_of_cachedCheck endpoint285PositiveFacts
    endpoint286PositiveFacts.valid leaf3781CoverageChecked

private noncomputable def leaf3781InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3781InputLogOnePlusV_eq :
    leaf3781InputLogOnePlusV = outerEnclosure 24
      (leaf3781Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3781RoundedFacts : LeafRoundedFacts 8
    leaf3781Certificate.logOnePlusV leaf3781InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3781InputLogOnePlusV_eq }

private noncomputable def leaf3781Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi68InputQChi innerPair552Input
    leaf3781InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3781LowerChecked :
    lowerCheck 24 leaf3781Box leaf3781Inputs = true := by
  rfl'

private theorem leaf3781CoversExact : CoversExact 8
    leaf3781Box leaf3781Certificate leaf3781InnerLog leaf3781Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi68RoundedFacts
    innerPair552RoundedFacts leaf3781RoundedFacts (by rfl)

private theorem leaf3781FlatSound : Sound leaf3781Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3781CertificateValid
    leaf3781InnerLogValid leaf3781CoversExact leaf3781LowerChecked

private noncomputable def leaf3782Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf3782Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108999/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178689536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (138178183/134217728) }, upper := { exponent := 1, mantissa := (17/16) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358067199/34357379072) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf3782InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf3782LocalValidity :
    LeafFacts leaf3782Box leaf3782Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3782Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178689536) }) = true
      norm_num [leaf3782Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3782CertificateValid :
    WideCertificateValid leaf3782Box leaf3782Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi69ValidityFacts
    leaf3782LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3782CoverageChecked :
    coverageCheck (innerAD leaf3782Box) leaf3782InnerLog = true := by
  rfl'

private theorem leaf3782InnerLogValid :
    leaf3782InnerLog.Valid 8 (innerAD leaf3782Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf3782CoverageChecked

private noncomputable def leaf3782InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3782InputLogOnePlusV_eq :
    leaf3782InputLogOnePlusV = outerEnclosure 24
      (leaf3782Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3782RoundedFacts : LeafRoundedFacts 8
    leaf3782Certificate.logOnePlusV leaf3782InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3782InputLogOnePlusV_eq }

private noncomputable def leaf3782Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi69InputQChi innerPair117Input
    leaf3782InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3782LowerChecked :
    lowerCheck 24 leaf3782Box leaf3782Inputs = true := by
  rfl'

private theorem leaf3782CoversExact : CoversExact 8
    leaf3782Box leaf3782Certificate leaf3782InnerLog leaf3782Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi69RoundedFacts
    innerPair117RoundedFacts leaf3782RoundedFacts (by rfl)

private theorem leaf3782FlatSound : Sound leaf3782Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3782CertificateValid
    leaf3782InnerLogValid leaf3782CoversExact leaf3782LowerChecked

private noncomputable def component77Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node0_sound : Sound component77Node0Box :=
  sound_of_literal_split component77Node0Box leaf3733Box leaf3734Box
    .k (65/32) (by rfl) (by rfl)
    leaf3733FlatSound leaf3734FlatSound

private noncomputable def component77Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node1_sound : Sound component77Node1Box :=
  sound_of_literal_split component77Node1Box leaf3735Box leaf3736Box
    .k (65/32) (by rfl) (by rfl)
    leaf3735FlatSound leaf3736FlatSound

private noncomputable def component77Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node2_sound : Sound component77Node2Box :=
  sound_of_literal_split component77Node2Box component77Node0Box component77Node1Box
    .chi (25/64) (by rfl) (by rfl)
    component77Node0_sound component77Node1_sound

private noncomputable def component77Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node3_sound : Sound component77Node3Box :=
  sound_of_literal_split component77Node3Box leaf3737Box leaf3738Box
    .k (67/32) (by rfl) (by rfl)
    leaf3737FlatSound leaf3738FlatSound

private noncomputable def component77Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node4_sound : Sound component77Node4Box :=
  sound_of_literal_split component77Node4Box leaf3739Box leaf3740Box
    .k (67/32) (by rfl) (by rfl)
    leaf3739FlatSound leaf3740FlatSound

private noncomputable def component77Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node5_sound : Sound component77Node5Box :=
  sound_of_literal_split component77Node5Box component77Node3Box component77Node4Box
    .chi (25/64) (by rfl) (by rfl)
    component77Node3_sound component77Node4_sound

private noncomputable def component77Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node6_sound : Sound component77Node6Box :=
  sound_of_literal_split component77Node6Box component77Node2Box component77Node5Box
    .k (33/16) (by rfl) (by rfl)
    component77Node2_sound component77Node5_sound

private noncomputable def component77Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node7_sound : Sound component77Node7Box :=
  sound_of_literal_split component77Node7Box leaf3741Box leaf3742Box
    .k (65/32) (by rfl) (by rfl)
    leaf3741FlatSound leaf3742FlatSound

private noncomputable def component77Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node8_sound : Sound component77Node8Box :=
  sound_of_literal_split component77Node8Box component77Node7Box leaf3743Box
    .chi (27/64) (by rfl) (by rfl)
    component77Node7_sound leaf3743FlatSound

private noncomputable def component77Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node9_sound : Sound component77Node9Box :=
  sound_of_literal_split component77Node9Box leaf3744Box leaf3745Box
    .k (67/32) (by rfl) (by rfl)
    leaf3744FlatSound leaf3745FlatSound

private noncomputable def component77Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node10_sound : Sound component77Node10Box :=
  sound_of_literal_split component77Node10Box leaf3746Box leaf3747Box
    .k (67/32) (by rfl) (by rfl)
    leaf3746FlatSound leaf3747FlatSound

private noncomputable def component77Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node11_sound : Sound component77Node11Box :=
  sound_of_literal_split component77Node11Box component77Node9Box component77Node10Box
    .chi (27/64) (by rfl) (by rfl)
    component77Node9_sound component77Node10_sound

private noncomputable def component77Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node12_sound : Sound component77Node12Box :=
  sound_of_literal_split component77Node12Box component77Node8Box component77Node11Box
    .k (33/16) (by rfl) (by rfl)
    component77Node8_sound component77Node11_sound

private noncomputable def component77Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node13_sound : Sound component77Node13Box :=
  sound_of_literal_split component77Node13Box component77Node6Box component77Node12Box
    .chi (13/32) (by rfl) (by rfl)
    component77Node6_sound component77Node12_sound

private noncomputable def component77Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node14_sound : Sound component77Node14Box :=
  sound_of_literal_split component77Node14Box leaf3748Box leaf3749Box
    .k (69/32) (by rfl) (by rfl)
    leaf3748FlatSound leaf3749FlatSound

private noncomputable def component77Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node15_sound : Sound component77Node15Box :=
  sound_of_literal_split component77Node15Box leaf3750Box leaf3751Box
    .k (69/32) (by rfl) (by rfl)
    leaf3750FlatSound leaf3751FlatSound

private noncomputable def component77Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node16_sound : Sound component77Node16Box :=
  sound_of_literal_split component77Node16Box component77Node14Box component77Node15Box
    .chi (25/64) (by rfl) (by rfl)
    component77Node14_sound component77Node15_sound

private noncomputable def component77Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (3/8), chiHi := (25/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node17_sound : Sound component77Node17Box :=
  sound_of_literal_split component77Node17Box leaf3752Box leaf3753Box
    .k (71/32) (by rfl) (by rfl)
    leaf3752FlatSound leaf3753FlatSound

private noncomputable def component77Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (25/64), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node18_sound : Sound component77Node18Box :=
  sound_of_literal_split component77Node18Box leaf3754Box leaf3755Box
    .k (71/32) (by rfl) (by rfl)
    leaf3754FlatSound leaf3755FlatSound

private noncomputable def component77Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node19_sound : Sound component77Node19Box :=
  sound_of_literal_split component77Node19Box component77Node17Box component77Node18Box
    .chi (25/64) (by rfl) (by rfl)
    component77Node17_sound component77Node18_sound

private noncomputable def component77Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/8), chiHi := (13/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node20_sound : Sound component77Node20Box :=
  sound_of_literal_split component77Node20Box component77Node16Box component77Node19Box
    .k (35/16) (by rfl) (by rfl)
    component77Node16_sound component77Node19_sound

private noncomputable def component77Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node21_sound : Sound component77Node21Box :=
  sound_of_literal_split component77Node21Box leaf3756Box leaf3757Box
    .k (69/32) (by rfl) (by rfl)
    leaf3756FlatSound leaf3757FlatSound

private noncomputable def component77Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node22_sound : Sound component77Node22Box :=
  sound_of_literal_split component77Node22Box leaf3758Box leaf3759Box
    .k (69/32) (by rfl) (by rfl)
    leaf3758FlatSound leaf3759FlatSound

private noncomputable def component77Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node23_sound : Sound component77Node23Box :=
  sound_of_literal_split component77Node23Box component77Node21Box component77Node22Box
    .chi (27/64) (by rfl) (by rfl)
    component77Node21_sound component77Node22_sound

private noncomputable def component77Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (13/32), chiHi := (27/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node24_sound : Sound component77Node24Box :=
  sound_of_literal_split component77Node24Box leaf3760Box leaf3761Box
    .k (71/32) (by rfl) (by rfl)
    leaf3760FlatSound leaf3761FlatSound

private noncomputable def component77Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (27/64), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node25_sound : Sound component77Node25Box :=
  sound_of_literal_split component77Node25Box leaf3762Box leaf3763Box
    .k (71/32) (by rfl) (by rfl)
    leaf3762FlatSound leaf3763FlatSound

private noncomputable def component77Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node26_sound : Sound component77Node26Box :=
  sound_of_literal_split component77Node26Box component77Node24Box component77Node25Box
    .chi (27/64) (by rfl) (by rfl)
    component77Node24_sound component77Node25_sound

private noncomputable def component77Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (13/32), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node27_sound : Sound component77Node27Box :=
  sound_of_literal_split component77Node27Box component77Node23Box component77Node26Box
    .k (35/16) (by rfl) (by rfl)
    component77Node23_sound component77Node26_sound

private noncomputable def component77Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node28_sound : Sound component77Node28Box :=
  sound_of_literal_split component77Node28Box component77Node20Box component77Node27Box
    .chi (13/32) (by rfl) (by rfl)
    component77Node20_sound component77Node27_sound

private noncomputable def component77Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component77Node29_sound : Sound component77Node29Box :=
  sound_of_literal_split component77Node29Box component77Node13Box component77Node28Box
    .k (17/8) (by rfl) (by rfl)
    component77Node13_sound component77Node28_sound

private noncomputable def component77Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node30_sound : Sound component77Node30Box :=
  sound_of_literal_split component77Node30Box leaf3764Box leaf3765Box
    .chi (29/64) (by rfl) (by rfl)
    leaf3764FlatSound leaf3765FlatSound

private noncomputable def component77Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node31_sound : Sound component77Node31Box :=
  sound_of_literal_split component77Node31Box leaf3766Box leaf3767Box
    .chi (29/64) (by rfl) (by rfl)
    leaf3766FlatSound leaf3767FlatSound

private noncomputable def component77Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node32_sound : Sound component77Node32Box :=
  sound_of_literal_split component77Node32Box component77Node30Box component77Node31Box
    .k (33/16) (by rfl) (by rfl)
    component77Node30_sound component77Node31_sound

private noncomputable def component77Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node33_sound : Sound component77Node33Box :=
  sound_of_literal_split component77Node33Box leaf3768Box leaf3769Box
    .chi (31/64) (by rfl) (by rfl)
    leaf3768FlatSound leaf3769FlatSound

private noncomputable def component77Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node34_sound : Sound component77Node34Box :=
  sound_of_literal_split component77Node34Box leaf3770Box leaf3771Box
    .chi (31/64) (by rfl) (by rfl)
    leaf3770FlatSound leaf3771FlatSound

private noncomputable def component77Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node35_sound : Sound component77Node35Box :=
  sound_of_literal_split component77Node35Box component77Node33Box component77Node34Box
    .k (33/16) (by rfl) (by rfl)
    component77Node33_sound component77Node34_sound

private noncomputable def component77Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node36_sound : Sound component77Node36Box :=
  sound_of_literal_split component77Node36Box component77Node32Box component77Node35Box
    .chi (15/32) (by rfl) (by rfl)
    component77Node32_sound component77Node35_sound

private noncomputable def component77Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node37_sound : Sound component77Node37Box :=
  sound_of_literal_split component77Node37Box leaf3772Box leaf3773Box
    .k (69/32) (by rfl) (by rfl)
    leaf3772FlatSound leaf3773FlatSound

private noncomputable def component77Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node38_sound : Sound component77Node38Box :=
  sound_of_literal_split component77Node38Box component77Node37Box leaf3774Box
    .chi (29/64) (by rfl) (by rfl)
    component77Node37_sound leaf3774FlatSound

private noncomputable def component77Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component77Node39_sound : Sound component77Node39Box :=
  sound_of_literal_split component77Node39Box leaf3775Box leaf3776Box
    .k (71/32) (by rfl) (by rfl)
    leaf3775FlatSound leaf3776FlatSound

private noncomputable def component77Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node40_sound : Sound component77Node40Box :=
  sound_of_literal_split component77Node40Box leaf3777Box leaf3778Box
    .k (71/32) (by rfl) (by rfl)
    leaf3777FlatSound leaf3778FlatSound

private noncomputable def component77Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node41_sound : Sound component77Node41Box :=
  sound_of_literal_split component77Node41Box component77Node39Box component77Node40Box
    .chi (29/64) (by rfl) (by rfl)
    component77Node39_sound component77Node40_sound

private noncomputable def component77Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component77Node42_sound : Sound component77Node42Box :=
  sound_of_literal_split component77Node42Box component77Node38Box component77Node41Box
    .k (35/16) (by rfl) (by rfl)
    component77Node38_sound component77Node41_sound

private noncomputable def component77Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node43_sound : Sound component77Node43Box :=
  sound_of_literal_split component77Node43Box leaf3779Box leaf3780Box
    .chi (31/64) (by rfl) (by rfl)
    leaf3779FlatSound leaf3780FlatSound

private noncomputable def component77Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node44_sound : Sound component77Node44Box :=
  sound_of_literal_split component77Node44Box leaf3781Box leaf3782Box
    .chi (31/64) (by rfl) (by rfl)
    leaf3781FlatSound leaf3782FlatSound

private noncomputable def component77Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node45_sound : Sound component77Node45Box :=
  sound_of_literal_split component77Node45Box component77Node43Box component77Node44Box
    .k (35/16) (by rfl) (by rfl)
    component77Node43_sound component77Node44_sound

private noncomputable def component77Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node46_sound : Sound component77Node46Box :=
  sound_of_literal_split component77Node46Box component77Node42Box component77Node45Box
    .chi (15/32) (by rfl) (by rfl)
    component77Node42_sound component77Node45_sound

private noncomputable def component77Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component77Node47_sound : Sound component77Node47Box :=
  sound_of_literal_split component77Node47Box component77Node36Box component77Node46Box
    .k (17/8) (by rfl) (by rfl)
    component77Node36_sound component77Node46_sound

noncomputable def component77Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component77_sound : Sound component77Box :=
  sound_of_literal_split component77Box component77Node29Box component77Node47Box
    .chi (7/16) (by rfl) (by rfl)
    component77Node29_sound component77Node47_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
