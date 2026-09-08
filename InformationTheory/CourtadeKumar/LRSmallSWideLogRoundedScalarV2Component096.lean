import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
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

private noncomputable def leaf4635Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4635Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871283/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357561088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1082064015/1073741824) }, upper := { exponent := 1, mantissa := (16697/16384) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716283647/68715122176) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4635InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4635LocalValidity :
    LeafFacts leaf4635Box leaf4635Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4635Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357561088) }) = true
      norm_num [leaf4635Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4635CertificateValid :
    WideCertificateValid leaf4635Box leaf4635Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi289ValidityFacts
    leaf4635LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4635CoverageChecked :
    coverageCheck (innerAD leaf4635Box) leaf4635InnerLog = true := by
  rfl'

private theorem leaf4635InnerLogValid :
    leaf4635InnerLog.Valid 8 (innerAD leaf4635Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4635CoverageChecked

private noncomputable def leaf4635InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4635InputLogOnePlusV_eq :
    leaf4635InputLogOnePlusV = outerEnclosure 24
      (leaf4635Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4635RoundedFacts : LeafRoundedFacts 8
    leaf4635Certificate.logOnePlusV leaf4635InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4635InputLogOnePlusV_eq }

private noncomputable def leaf4635Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi289InputQChi innerPair116Input
    leaf4635InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4635LowerChecked :
    lowerCheck 24 leaf4635Box leaf4635Inputs = true := by
  rfl'

private theorem leaf4635CoversExact : CoversExact 8
    leaf4635Box leaf4635Certificate leaf4635InnerLog leaf4635Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi289RoundedFacts
    innerPair116RoundedFacts leaf4635RoundedFacts (by rfl)

private theorem leaf4635FlatSound : Sound leaf4635Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4635CertificateValid
    leaf4635InnerLogValid leaf4635CoversExact leaf4635LowerChecked

private noncomputable def leaf4636Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4636Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021031424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1088879341/1073741824) }, upper := { exponent := 1, mantissa := (8401/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042132751/4042062848) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4636InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4636LocalValidity :
    LeafFacts leaf4636Box leaf4636Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4636Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021031424) }) = true
      norm_num [leaf4636Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4636CertificateValid :
    WideCertificateValid leaf4636Box leaf4636Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi290ValidityFacts
    leaf4636LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4636CoverageChecked :
    coverageCheck (innerAD leaf4636Box) leaf4636InnerLog = true := by
  rfl'

private theorem leaf4636InnerLogValid :
    leaf4636InnerLog.Valid 8 (innerAD leaf4636Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4636CoverageChecked

private noncomputable def leaf4636InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4636InputLogOnePlusV_eq :
    leaf4636InputLogOnePlusV = outerEnclosure 24
      (leaf4636Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4636RoundedFacts : LeafRoundedFacts 8
    leaf4636Certificate.logOnePlusV leaf4636InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4636InputLogOnePlusV_eq }

private noncomputable def leaf4636Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi290InputQChi innerPair116Input
    leaf4636InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4636LowerChecked :
    lowerCheck 24 leaf4636Box leaf4636Inputs = true := by
  rfl'

private theorem leaf4636CoversExact : CoversExact 8
    leaf4636Box leaf4636Certificate leaf4636InnerLog leaf4636Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi290RoundedFacts
    innerPair116RoundedFacts leaf4636RoundedFacts (by rfl)

private theorem leaf4636FlatSound : Sound leaf4636Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4636CertificateValid
    leaf4636InnerLogValid leaf4636CoversExact leaf4636LowerChecked

private noncomputable def leaf4637Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4637Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871285/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357540352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1087306573/1073741824) }, upper := { exponent := 1, mantissa := (8389/8192) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716262911/68715080704) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4637InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4637LocalValidity :
    LeafFacts leaf4637Box leaf4637Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4637Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357540352) }) = true
      norm_num [leaf4637Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4637CertificateValid :
    WideCertificateValid leaf4637Box leaf4637Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi289ValidityFacts
    leaf4637LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4637CoverageChecked :
    coverageCheck (innerAD leaf4637Box) leaf4637InnerLog = true := by
  rfl'

private theorem leaf4637InnerLogValid :
    leaf4637InnerLog.Valid 8 (innerAD leaf4637Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4637CoverageChecked

private noncomputable def leaf4637InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4637InputLogOnePlusV_eq :
    leaf4637InputLogOnePlusV = outerEnclosure 24
      (leaf4637Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4637RoundedFacts : LeafRoundedFacts 8
    leaf4637Certificate.logOnePlusV leaf4637InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4637InputLogOnePlusV_eq }

private noncomputable def leaf4637Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi289InputQChi innerPair116Input
    leaf4637InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4637LowerChecked :
    lowerCheck 24 leaf4637Box leaf4637Inputs = true := by
  rfl'

private theorem leaf4637CoversExact : CoversExact 8
    leaf4637Box leaf4637Certificate leaf4637InnerLog leaf4637Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi289RoundedFacts
    innerPair116RoundedFacts leaf4637RoundedFacts (by rfl)

private theorem leaf4637FlatSound : Sound leaf4637Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4637CertificateValid
    leaf4637InnerLogValid leaf4637CoversExact leaf4637LowerChecked

private noncomputable def leaf4638Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4638Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357513216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1094187431/1073741824) }, upper := { exponent := 1, mantissa := (4221/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716235775/68715026432) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4638InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4638LocalValidity :
    LeafFacts leaf4638Box leaf4638Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4638Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357513216) }) = true
      norm_num [leaf4638Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4638CertificateValid :
    WideCertificateValid leaf4638Box leaf4638Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi290ValidityFacts
    leaf4638LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4638CoverageChecked :
    coverageCheck (innerAD leaf4638Box) leaf4638InnerLog = true := by
  rfl'

private theorem leaf4638InnerLogValid :
    leaf4638InnerLog.Valid 8 (innerAD leaf4638Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4638CoverageChecked

private noncomputable def leaf4638InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf4638InputLogOnePlusV_eq :
    leaf4638InputLogOnePlusV = outerEnclosure 24
      (leaf4638Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4638RoundedFacts : LeafRoundedFacts 8
    leaf4638Certificate.logOnePlusV leaf4638InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4638InputLogOnePlusV_eq }

private noncomputable def leaf4638Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi290InputQChi innerPair116Input
    leaf4638InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4638LowerChecked :
    lowerCheck 24 leaf4638Box leaf4638Inputs = true := by
  rfl'

private theorem leaf4638CoversExact : CoversExact 8
    leaf4638Box leaf4638Certificate leaf4638InnerLog leaf4638Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi290RoundedFacts
    innerPair116RoundedFacts leaf4638RoundedFacts (by rfl)

private theorem leaf4638FlatSound : Sound leaf4638Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4638CertificateValid
    leaf4638InnerLogValid leaf4638CoversExact leaf4638LowerChecked

private noncomputable def leaf4639Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4639Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108306688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1095694667/1073741824) }, upper := { exponent := 1, mantissa := (16907/16384) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216652577/2216613376) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4639InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4639LocalValidity :
    LeafFacts leaf4639Box leaf4639Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4639Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108306688) }) = true
      norm_num [leaf4639Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4639CertificateValid :
    WideCertificateValid leaf4639Box leaf4639Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi291ValidityFacts
    leaf4639LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4639CoverageChecked :
    coverageCheck (innerAD leaf4639Box) leaf4639InnerLog = true := by
  rfl'

private theorem leaf4639InnerLogValid :
    leaf4639InnerLog.Valid 8 (innerAD leaf4639Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4639CoverageChecked

private noncomputable def leaf4639InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4639InputLogOnePlusV_eq :
    leaf4639InputLogOnePlusV = outerEnclosure 24
      (leaf4639Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4639RoundedFacts : LeafRoundedFacts 8
    leaf4639Certificate.logOnePlusV leaf4639InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4639InputLogOnePlusV_eq }

private noncomputable def leaf4639Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi291InputQChi innerPair311Input
    leaf4639InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4639LowerChecked :
    lowerCheck 24 leaf4639Box leaf4639Inputs = true := by
  rfl'

private theorem leaf4639CoversExact : CoversExact 8
    leaf4639Box leaf4639Certificate leaf4639InnerLog leaf4639Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi291RoundedFacts
    innerPair311RoundedFacts leaf4639RoundedFacts (by rfl)

private theorem leaf4639FlatSound : Sound leaf4639Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4639CertificateValid
    leaf4639InnerLogValid leaf4639CoversExact leaf4639LowerChecked

private noncomputable def leaf4640Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4640Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357480448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1102509993/1073741824) }, upper := { exponent := 1, mantissa := (4253/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716203007/68714960896) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4640InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf4640LocalValidity :
    LeafFacts leaf4640Box leaf4640Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4640Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357480448) }) = true
      norm_num [leaf4640Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4640CertificateValid :
    WideCertificateValid leaf4640Box leaf4640Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi292ValidityFacts
    leaf4640LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4640CoverageChecked :
    coverageCheck (innerAD leaf4640Box) leaf4640InnerLog = true := by
  rfl'

private theorem leaf4640InnerLogValid :
    leaf4640InnerLog.Valid 8 (innerAD leaf4640Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf4640CoverageChecked

private noncomputable def leaf4640InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4640InputLogOnePlusV_eq :
    leaf4640InputLogOnePlusV = outerEnclosure 24
      (leaf4640Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4640RoundedFacts : LeafRoundedFacts 8
    leaf4640Certificate.logOnePlusV leaf4640InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4640InputLogOnePlusV_eq }

private noncomputable def leaf4640Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi292InputQChi innerPair117Input
    leaf4640InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4640LowerChecked :
    lowerCheck 24 leaf4640Box leaf4640Inputs = true := by
  rfl'

private theorem leaf4640CoversExact : CoversExact 8
    leaf4640Box leaf4640Certificate leaf4640InnerLog leaf4640Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi292RoundedFacts
    innerPair117RoundedFacts leaf4640RoundedFacts (by rfl)

private theorem leaf4640FlatSound : Sound leaf4640Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4640CertificateValid
    leaf4640InnerLogValid leaf4640CoversExact leaf4640LowerChecked

private noncomputable def leaf4641Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4641Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357486080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1101068289/1073741824) }, upper := { exponent := 1, mantissa := (8495/8192) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716208639/68714972160) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4641InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4641LocalValidity :
    LeafFacts leaf4641Box leaf4641Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4641Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357486080) }) = true
      norm_num [leaf4641Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4641CertificateValid :
    WideCertificateValid leaf4641Box leaf4641Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi291ValidityFacts
    leaf4641LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4641CoverageChecked :
    coverageCheck (innerAD leaf4641Box) leaf4641InnerLog = true := by
  rfl'

private theorem leaf4641InnerLogValid :
    leaf4641InnerLog.Valid 8 (innerAD leaf4641Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4641CoverageChecked

private noncomputable def leaf4641InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4641InputLogOnePlusV_eq :
    leaf4641InputLogOnePlusV = outerEnclosure 24
      (leaf4641Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4641RoundedFacts : LeafRoundedFacts 8
    leaf4641Certificate.logOnePlusV leaf4641InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4641InputLogOnePlusV_eq }

private noncomputable def leaf4641Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi291InputQChi innerPair327Input
    leaf4641InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4641LowerChecked :
    lowerCheck 24 leaf4641Box leaf4641Inputs = true := by
  rfl'

private theorem leaf4641CoversExact : CoversExact 8
    leaf4641Box leaf4641Certificate leaf4641InnerLog leaf4641Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi291RoundedFacts
    innerPair327RoundedFacts leaf4641RoundedFacts (by rfl)

private theorem leaf4641FlatSound : Sound leaf4641Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4641CertificateValid
    leaf4641InnerLogValid leaf4641CoversExact leaf4641LowerChecked

private noncomputable def leaf4642Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4642Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357458944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1107949147/1073741824) }, upper := { exponent := 1, mantissa := (2137/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716181503/68714917888) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4642InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4642LocalValidity :
    LeafFacts leaf4642Box leaf4642Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4642Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357458944) }) = true
      norm_num [leaf4642Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4642CertificateValid :
    WideCertificateValid leaf4642Box leaf4642Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi292ValidityFacts
    leaf4642LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4642CoverageChecked :
    coverageCheck (innerAD leaf4642Box) leaf4642InnerLog = true := by
  rfl'

private theorem leaf4642InnerLogValid :
    leaf4642InnerLog.Valid 8 (innerAD leaf4642Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4642CoverageChecked

private noncomputable def leaf4642InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4642InputLogOnePlusV_eq :
    leaf4642InputLogOnePlusV = outerEnclosure 24
      (leaf4642Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4642RoundedFacts : LeafRoundedFacts 8
    leaf4642Certificate.logOnePlusV leaf4642InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4642InputLogOnePlusV_eq }

private noncomputable def leaf4642Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi292InputQChi innerPair242Input
    leaf4642InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4642LowerChecked :
    lowerCheck 24 leaf4642Box leaf4642Inputs = true := by
  rfl'

private theorem leaf4642CoversExact : CoversExact 8
    leaf4642Box leaf4642Certificate leaf4642InnerLog leaf4642Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi292RoundedFacts
    innerPair242RoundedFacts leaf4642RoundedFacts (by rfl)

private theorem leaf4642FlatSound : Sound leaf4642Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4642CertificateValid
    leaf4642InnerLogValid leaf4642CoversExact leaf4642LowerChecked

private noncomputable def leaf4643Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4643Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871287/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908217088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1092549131/1073741824) }, upper := { exponent := 1, mantissa := (16859/16384) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816606025/9816434176) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4643InnerLog : WideLogData :=
  innerPair116Data

set_option maxRecDepth 1000000 in
private theorem leaf4643LocalValidity :
    LeafFacts leaf4643Box leaf4643Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4643Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908217088) }) = true
      norm_num [leaf4643Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4643CertificateValid :
    WideCertificateValid leaf4643Box leaf4643Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi289ValidityFacts
    leaf4643LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4643CoverageChecked :
    coverageCheck (innerAD leaf4643Box) leaf4643InnerLog = true := by
  rfl'

private theorem leaf4643InnerLogValid :
    leaf4643InnerLog.Valid 8 (innerAD leaf4643Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint72PositiveFacts.valid leaf4643CoverageChecked

private noncomputable def leaf4643InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4643InputLogOnePlusV_eq :
    leaf4643InputLogOnePlusV = outerEnclosure 24
      (leaf4643Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4643RoundedFacts : LeafRoundedFacts 8
    leaf4643Certificate.logOnePlusV leaf4643InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4643InputLogOnePlusV_eq }

private noncomputable def leaf4643Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi289InputQChi innerPair116Input
    leaf4643InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4643LowerChecked :
    lowerCheck 24 leaf4643Box leaf4643Inputs = true := by
  rfl'

private theorem leaf4643CoversExact : CoversExact 8
    leaf4643Box leaf4643Certificate leaf4643InnerLog leaf4643Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi289RoundedFacts
    innerPair116RoundedFacts leaf4643RoundedFacts (by rfl)

private theorem leaf4643FlatSound : Sound leaf4643Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4643CertificateValid
    leaf4643InnerLogValid leaf4643CoversExact leaf4643LowerChecked

private noncomputable def leaf4644Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4644Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357492224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1099495521/1073741824) }, upper := { exponent := 1, mantissa := (8483/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716214783/68714984448) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4644InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4644LocalValidity :
    LeafFacts leaf4644Box leaf4644Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4644Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357492224) }) = true
      norm_num [leaf4644Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4644CertificateValid :
    WideCertificateValid leaf4644Box leaf4644Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi290ValidityFacts
    leaf4644LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4644CoverageChecked :
    coverageCheck (innerAD leaf4644Box) leaf4644InnerLog = true := by
  rfl'

private theorem leaf4644InnerLogValid :
    leaf4644InnerLog.Valid 8 (innerAD leaf4644Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4644CoverageChecked

private noncomputable def leaf4644InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4644InputLogOnePlusV_eq :
    leaf4644InputLogOnePlusV = outerEnclosure 24
      (leaf4644Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4644RoundedFacts : LeafRoundedFacts 8
    leaf4644Certificate.logOnePlusV leaf4644InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4644InputLogOnePlusV_eq }

private noncomputable def leaf4644Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi290InputQChi innerPair327Input
    leaf4644InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4644LowerChecked :
    lowerCheck 24 leaf4644Box leaf4644Inputs = true := by
  rfl'

private theorem leaf4644CoversExact : CoversExact 8
    leaf4644Box leaf4644Certificate leaf4644InnerLog leaf4644Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi290RoundedFacts
    innerPair327RoundedFacts leaf4644RoundedFacts (by rfl)

private theorem leaf4644FlatSound : Sound leaf4644Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4644CertificateValid
    leaf4644InnerLogValid leaf4644CoversExact leaf4644LowerChecked

private noncomputable def leaf4645Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4645Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871289/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357498880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1097791689/1073741824) }, upper := { exponent := 1, mantissa := (4235/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716221439/68714997760) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4645InnerLog : WideLogData :=
  innerPair311Data

set_option maxRecDepth 1000000 in
private theorem leaf4645LocalValidity :
    LeafFacts leaf4645Box leaf4645Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4645Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357498880) }) = true
      norm_num [leaf4645Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4645CertificateValid :
    WideCertificateValid leaf4645Box leaf4645Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi289ValidityFacts
    leaf4645LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4645CoverageChecked :
    coverageCheck (innerAD leaf4645Box) leaf4645InnerLog = true := by
  rfl'

private theorem leaf4645InnerLogValid :
    leaf4645InnerLog.Valid 8 (innerAD leaf4645Box) :=
  wideLogDataValid_of_cachedCheck endpoint82PositiveFacts
    endpoint86PositiveFacts.valid leaf4645CoverageChecked

private noncomputable def leaf4645InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4645InputLogOnePlusV_eq :
    leaf4645InputLogOnePlusV = outerEnclosure 24
      (leaf4645Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4645RoundedFacts : LeafRoundedFacts 8
    leaf4645Certificate.logOnePlusV leaf4645InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4645InputLogOnePlusV_eq }

private noncomputable def leaf4645Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi289InputQChi innerPair311Input
    leaf4645InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4645LowerChecked :
    lowerCheck 24 leaf4645Box leaf4645Inputs = true := by
  rfl'

private theorem leaf4645CoversExact : CoversExact 8
    leaf4645Box leaf4645Certificate leaf4645InnerLog leaf4645Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi289RoundedFacts
    innerPair311RoundedFacts leaf4645RoundedFacts (by rfl)

private theorem leaf4645FlatSound : Sound leaf4645Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4645CertificateValid
    leaf4645InnerLogValid leaf4645CoversExact leaf4645LowerChecked

private noncomputable def leaf4646Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4646Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908210176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1104803611/1073741824) }, upper := { exponent := 1, mantissa := (2131/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816599113/9816420352) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4646InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf4646LocalValidity :
    LeafFacts leaf4646Box leaf4646Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4646Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908210176) }) = true
      norm_num [leaf4646Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4646CertificateValid :
    WideCertificateValid leaf4646Box leaf4646Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi290ValidityFacts
    leaf4646LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4646CoverageChecked :
    coverageCheck (innerAD leaf4646Box) leaf4646InnerLog = true := by
  rfl'

private theorem leaf4646InnerLogValid :
    leaf4646InnerLog.Valid 8 (innerAD leaf4646Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf4646CoverageChecked

private noncomputable def leaf4646InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4646InputLogOnePlusV_eq :
    leaf4646InputLogOnePlusV = outerEnclosure 24
      (leaf4646Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4646RoundedFacts : LeafRoundedFacts 8
    leaf4646Certificate.logOnePlusV leaf4646InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4646InputLogOnePlusV_eq }

private noncomputable def leaf4646Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi290InputQChi innerPair329Input
    leaf4646InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4646LowerChecked :
    lowerCheck 24 leaf4646Box leaf4646Inputs = true := by
  rfl'

private theorem leaf4646CoversExact : CoversExact 8
    leaf4646Box leaf4646Certificate leaf4646InnerLog leaf4646Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi290RoundedFacts
    innerPair329RoundedFacts leaf4646RoundedFacts (by rfl)

private theorem leaf4646FlatSound : Sound leaf4646Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4646CertificateValid
    leaf4646InnerLogValid leaf4646CoversExact leaf4646LowerChecked

private noncomputable def leaf4647Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4647Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357464832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1106441911/1073741824) }, upper := { exponent := 1, mantissa := (17073/16384) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716187391/68714929664) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4647InnerLog : WideLogData :=
  innerPair329Data

set_option maxRecDepth 1000000 in
private theorem leaf4647LocalValidity :
    LeafFacts leaf4647Box leaf4647Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4647Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357464832) }) = true
      norm_num [leaf4647Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4647CertificateValid :
    WideCertificateValid leaf4647Box leaf4647Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi291ValidityFacts
    leaf4647LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4647CoverageChecked :
    coverageCheck (innerAD leaf4647Box) leaf4647InnerLog = true := by
  rfl'

private theorem leaf4647InnerLogValid :
    leaf4647InnerLog.Valid 8 (innerAD leaf4647Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint284PositiveFacts.valid leaf4647CoverageChecked

private noncomputable def leaf4647InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4647InputLogOnePlusV_eq :
    leaf4647InputLogOnePlusV = outerEnclosure 24
      (leaf4647Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4647RoundedFacts : LeafRoundedFacts 8
    leaf4647Certificate.logOnePlusV leaf4647InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4647InputLogOnePlusV_eq }

private noncomputable def leaf4647Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi291InputQChi innerPair329Input
    leaf4647InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4647LowerChecked :
    lowerCheck 24 leaf4647Box leaf4647Inputs = true := by
  rfl'

private theorem leaf4647CoversExact : CoversExact 8
    leaf4647Box leaf4647Certificate leaf4647InnerLog leaf4647Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi291RoundedFacts
    innerPair329RoundedFacts leaf4647RoundedFacts (by rfl)

private theorem leaf4647FlatSound : Sound leaf4647Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4647CertificateValid
    leaf4647InnerLogValid leaf4647CoversExact leaf4647LowerChecked

private noncomputable def leaf4648Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4648Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357437440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1113388301/1073741824) }, upper := { exponent := 1, mantissa := (4295/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716159999/68714874880) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4648InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4648LocalValidity :
    LeafFacts leaf4648Box leaf4648Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4648Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357437440) }) = true
      norm_num [leaf4648Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4648CertificateValid :
    WideCertificateValid leaf4648Box leaf4648Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi292ValidityFacts
    leaf4648LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4648CoverageChecked :
    coverageCheck (innerAD leaf4648Box) leaf4648InnerLog = true := by
  rfl'

private theorem leaf4648InnerLogValid :
    leaf4648InnerLog.Valid 8 (innerAD leaf4648Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4648CoverageChecked

private noncomputable def leaf4648InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4648InputLogOnePlusV_eq :
    leaf4648InputLogOnePlusV = outerEnclosure 24
      (leaf4648Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4648RoundedFacts : LeafRoundedFacts 8
    leaf4648Certificate.logOnePlusV leaf4648InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4648InputLogOnePlusV_eq }

private noncomputable def leaf4648Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi292InputQChi innerPair242Input
    leaf4648InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4648LowerChecked :
    lowerCheck 24 leaf4648Box leaf4648Inputs = true := by
  rfl'

private theorem leaf4648CoversExact : CoversExact 8
    leaf4648Box leaf4648Certificate leaf4648InnerLog leaf4648Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi292RoundedFacts
    innerPair242RoundedFacts leaf4648RoundedFacts (by rfl)

private theorem leaf4648FlatSound : Sound leaf4648Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4648CertificateValid
    leaf4648InnerLogValid leaf4648CoversExact leaf4648LowerChecked

private noncomputable def leaf4649Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4649Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357443584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1111815533/1073741824) }, upper := { exponent := 1, mantissa := (4289/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716166143/68714887168) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4649InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4649LocalValidity :
    LeafFacts leaf4649Box leaf4649Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4649Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357443584) }) = true
      norm_num [leaf4649Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4649CertificateValid :
    WideCertificateValid leaf4649Box leaf4649Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi291ValidityFacts
    leaf4649LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4649CoverageChecked :
    coverageCheck (innerAD leaf4649Box) leaf4649InnerLog = true := by
  rfl'

private theorem leaf4649InnerLogValid :
    leaf4649InnerLog.Valid 8 (innerAD leaf4649Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4649CoverageChecked

private noncomputable def leaf4649InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4649InputLogOnePlusV_eq :
    leaf4649InputLogOnePlusV = outerEnclosure 24
      (leaf4649Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4649RoundedFacts : LeafRoundedFacts 8
    leaf4649Certificate.logOnePlusV leaf4649InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4649InputLogOnePlusV_eq }

private noncomputable def leaf4649Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi291InputQChi innerPair242Input
    leaf4649InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4649LowerChecked :
    lowerCheck 24 leaf4649Box leaf4649Inputs = true := by
  rfl'

private theorem leaf4649CoversExact : CoversExact 8
    leaf4649Box leaf4649Certificate leaf4649InnerLog leaf4649Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi291RoundedFacts
    innerPair242RoundedFacts leaf4649RoundedFacts (by rfl)

private theorem leaf4649FlatSound : Sound leaf4649Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4649CertificateValid
    leaf4649InnerLogValid leaf4649CoversExact leaf4649LowerChecked

private noncomputable def leaf4650Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4650Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357415936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1118827455/1073741824) }, upper := { exponent := 1, mantissa := (1079/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716138495/68714831872) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4650InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4650LocalValidity :
    LeafFacts leaf4650Box leaf4650Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4650Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357415936) }) = true
      norm_num [leaf4650Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4650CertificateValid :
    WideCertificateValid leaf4650Box leaf4650Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi292ValidityFacts
    leaf4650LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4650CoverageChecked :
    coverageCheck (innerAD leaf4650Box) leaf4650InnerLog = true := by
  rfl'

private theorem leaf4650InnerLogValid :
    leaf4650InnerLog.Valid 8 (innerAD leaf4650Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4650CoverageChecked

private noncomputable def leaf4650InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4650InputLogOnePlusV_eq :
    leaf4650InputLogOnePlusV = outerEnclosure 24
      (leaf4650Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4650RoundedFacts : LeafRoundedFacts 8
    leaf4650Certificate.logOnePlusV leaf4650InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4650InputLogOnePlusV_eq }

private noncomputable def leaf4650Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi292InputQChi innerPair242Input
    leaf4650InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4650LowerChecked :
    lowerCheck 24 leaf4650Box leaf4650Inputs = true := by
  rfl'

private theorem leaf4650CoversExact : CoversExact 8
    leaf4650Box leaf4650Certificate leaf4650InnerLog leaf4650Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi292RoundedFacts
    innerPair242RoundedFacts leaf4650RoundedFacts (by rfl)

private theorem leaf4650FlatSound : Sound leaf4650Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4650CertificateValid
    leaf4650InnerLogValid leaf4650CoversExact leaf4650LowerChecked

private noncomputable def leaf4651Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4651Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357453568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1109325319/1073741824) }, upper := { exponent := 1, mantissa := (17117/16384) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716176127/68714907136) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4651InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4651LocalValidity :
    LeafFacts leaf4651Box leaf4651Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4651Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357453568) }) = true
      norm_num [leaf4651Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4651CertificateValid :
    WideCertificateValid leaf4651Box leaf4651Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi293ValidityFacts
    leaf4651LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4651CoverageChecked :
    coverageCheck (innerAD leaf4651Box) leaf4651InnerLog = true := by
  rfl'

private theorem leaf4651InnerLogValid :
    leaf4651InnerLog.Valid 8 (innerAD leaf4651Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4651CoverageChecked

private noncomputable def leaf4651InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4651InputLogOnePlusV_eq :
    leaf4651InputLogOnePlusV = outerEnclosure 24
      (leaf4651Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4651RoundedFacts : LeafRoundedFacts 8
    leaf4651Certificate.logOnePlusV leaf4651InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4651InputLogOnePlusV_eq }

private noncomputable def leaf4651Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi293InputQChi innerPair242Input
    leaf4651InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4651LowerChecked :
    lowerCheck 24 leaf4651Box leaf4651Inputs = true := by
  rfl'

private theorem leaf4651CoversExact : CoversExact 8
    leaf4651Box leaf4651Certificate leaf4651InnerLog leaf4651Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi293RoundedFacts
    innerPair242RoundedFacts leaf4651RoundedFacts (by rfl)

private theorem leaf4651FlatSound : Sound leaf4651Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4651CertificateValid
    leaf4651InnerLogValid leaf4651CoversExact leaf4651LowerChecked

private noncomputable def leaf4652Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4652Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357426688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1116140645/1073741824) }, upper := { exponent := 1, mantissa := (8611/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716149247/68714853376) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4652InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4652LocalValidity :
    LeafFacts leaf4652Box leaf4652Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4652Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357426688) }) = true
      norm_num [leaf4652Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4652CertificateValid :
    WideCertificateValid leaf4652Box leaf4652Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi294ValidityFacts
    leaf4652LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4652CoverageChecked :
    coverageCheck (innerAD leaf4652Box) leaf4652InnerLog = true := by
  rfl'

private theorem leaf4652InnerLogValid :
    leaf4652InnerLog.Valid 8 (innerAD leaf4652Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4652CoverageChecked

private noncomputable def leaf4652InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4652InputLogOnePlusV_eq :
    leaf4652InputLogOnePlusV = outerEnclosure 24
      (leaf4652Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4652RoundedFacts : LeafRoundedFacts 8
    leaf4652Certificate.logOnePlusV leaf4652InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4652InputLogOnePlusV_eq }

private noncomputable def leaf4652Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi294InputQChi innerPair242Input
    leaf4652InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4652LowerChecked :
    lowerCheck 24 leaf4652Box leaf4652Inputs = true := by
  rfl'

private theorem leaf4652CoversExact : CoversExact 8
    leaf4652Box leaf4652Certificate leaf4652InnerLog leaf4652Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi294RoundedFacts
    innerPair242RoundedFacts leaf4652RoundedFacts (by rfl)

private theorem leaf4652FlatSound : Sound leaf4652Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4652CertificateValid
    leaf4652InnerLogValid leaf4652CoversExact leaf4652LowerChecked

private noncomputable def leaf4653Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4653Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908204544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1114830005/1073741824) }, upper := { exponent := 1, mantissa := (8601/8192) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816593481/9816409088) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4653InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4653LocalValidity :
    LeafFacts leaf4653Box leaf4653Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4653Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908204544) }) = true
      norm_num [leaf4653Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4653CertificateValid :
    WideCertificateValid leaf4653Box leaf4653Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi293ValidityFacts
    leaf4653LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4653CoverageChecked :
    coverageCheck (innerAD leaf4653Box) leaf4653InnerLog = true := by
  rfl'

private theorem leaf4653InnerLogValid :
    leaf4653InnerLog.Valid 8 (innerAD leaf4653Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4653CoverageChecked

private noncomputable def leaf4653InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4653InputLogOnePlusV_eq :
    leaf4653InputLogOnePlusV = outerEnclosure 24
      (leaf4653Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4653RoundedFacts : LeafRoundedFacts 8
    leaf4653Certificate.logOnePlusV leaf4653InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4653InputLogOnePlusV_eq }

private noncomputable def leaf4653Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi293InputQChi innerPair242Input
    leaf4653InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4653LowerChecked :
    lowerCheck 24 leaf4653Box leaf4653Inputs = true := by
  rfl'

private theorem leaf4653CoversExact : CoversExact 8
    leaf4653Box leaf4653Certificate leaf4653InnerLog leaf4653Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi293RoundedFacts
    innerPair242RoundedFacts leaf4653RoundedFacts (by rfl)

private theorem leaf4653FlatSound : Sound leaf4653Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4653CertificateValid
    leaf4653InnerLogValid leaf4653CoversExact leaf4653LowerChecked

private noncomputable def leaf4654Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4654Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357404672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1121710863/1073741824) }, upper := { exponent := 1, mantissa := (4327/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716127231/68714809344) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4654InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4654LocalValidity :
    LeafFacts leaf4654Box leaf4654Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4654Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357404672) }) = true
      norm_num [leaf4654Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4654CertificateValid :
    WideCertificateValid leaf4654Box leaf4654Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi294ValidityFacts
    leaf4654LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4654CoverageChecked :
    coverageCheck (innerAD leaf4654Box) leaf4654InnerLog = true := by
  rfl'

private theorem leaf4654InnerLogValid :
    leaf4654InnerLog.Valid 8 (innerAD leaf4654Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4654CoverageChecked

private noncomputable def leaf4654InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4654InputLogOnePlusV_eq :
    leaf4654InputLogOnePlusV = outerEnclosure 24
      (leaf4654Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4654RoundedFacts : LeafRoundedFacts 8
    leaf4654Certificate.logOnePlusV leaf4654InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4654InputLogOnePlusV_eq }

private noncomputable def leaf4654Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi294InputQChi innerPair242Input
    leaf4654InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4654LowerChecked :
    lowerCheck 24 leaf4654Box leaf4654Inputs = true := by
  rfl'

private theorem leaf4654CoversExact : CoversExact 8
    leaf4654Box leaf4654Certificate leaf4654InnerLog leaf4654Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi294RoundedFacts
    innerPair242RoundedFacts leaf4654RoundedFacts (by rfl)

private theorem leaf4654FlatSound : Sound leaf4654Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4654CertificateValid
    leaf4654InnerLogValid leaf4654CoversExact leaf4654LowerChecked

private noncomputable def leaf4655Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4655Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357399808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1122955971/1073741824) }, upper := { exponent := 1, mantissa := (17327/16384) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716122367/68714799616) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4655InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4655LocalValidity :
    LeafFacts leaf4655Box leaf4655Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4655Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357399808) }) = true
      norm_num [leaf4655Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4655CertificateValid :
    WideCertificateValid leaf4655Box leaf4655Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi295ValidityFacts
    leaf4655LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4655CoverageChecked :
    coverageCheck (innerAD leaf4655Box) leaf4655InnerLog = true := by
  rfl'

private theorem leaf4655InnerLogValid :
    leaf4655InnerLog.Valid 8 (innerAD leaf4655Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4655CoverageChecked

private noncomputable def leaf4655InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4655InputLogOnePlusV_eq :
    leaf4655InputLogOnePlusV = outerEnclosure 24
      (leaf4655Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4655RoundedFacts : LeafRoundedFacts 8
    leaf4655Certificate.logOnePlusV leaf4655InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4655InputLogOnePlusV_eq }

private noncomputable def leaf4655Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi295InputQChi innerPair242Input
    leaf4655InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4655LowerChecked :
    lowerCheck 24 leaf4655Box leaf4655Inputs = true := by
  rfl'

private theorem leaf4655CoversExact : CoversExact 8
    leaf4655Box leaf4655Certificate leaf4655InnerLog leaf4655Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi295RoundedFacts
    innerPair242RoundedFacts leaf4655RoundedFacts (by rfl)

private theorem leaf4655FlatSound : Sound leaf4655Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4655CertificateValid
    leaf4655InnerLogValid leaf4655CoversExact leaf4655LowerChecked

private noncomputable def leaf4656Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4656Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357372928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1129771297/1073741824) }, upper := { exponent := 1, mantissa := (2179/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716095487/68714745856) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf4656InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4656LocalValidity :
    LeafFacts leaf4656Box leaf4656Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4656Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357372928) }) = true
      norm_num [leaf4656Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4656CertificateValid :
    WideCertificateValid leaf4656Box leaf4656Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi296ValidityFacts
    leaf4656LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4656CoverageChecked :
    coverageCheck (innerAD leaf4656Box) leaf4656InnerLog = true := by
  rfl'

private theorem leaf4656InnerLogValid :
    leaf4656InnerLog.Valid 8 (innerAD leaf4656Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4656CoverageChecked

private noncomputable def leaf4656InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4656InputLogOnePlusV_eq :
    leaf4656InputLogOnePlusV = outerEnclosure 24
      (leaf4656Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4656RoundedFacts : LeafRoundedFacts 8
    leaf4656Certificate.logOnePlusV leaf4656InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4656InputLogOnePlusV_eq }

private noncomputable def leaf4656Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi296InputQChi innerPair551Input
    leaf4656InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4656LowerChecked :
    lowerCheck 24 leaf4656Box leaf4656Inputs = true := by
  rfl'

private theorem leaf4656CoversExact : CoversExact 8
    leaf4656Box leaf4656Certificate leaf4656InnerLog leaf4656Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi296RoundedFacts
    innerPair551RoundedFacts leaf4656RoundedFacts (by rfl)

private theorem leaf4656FlatSound : Sound leaf4656Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4656CertificateValid
    leaf4656InnerLogValid leaf4656CoversExact leaf4656LowerChecked

private noncomputable def leaf4657Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4657Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021022208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1128591721/1073741824) }, upper := { exponent := 1, mantissa := (8707/8192) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042123535/4042044416) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4657InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4657LocalValidity :
    LeafFacts leaf4657Box leaf4657Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4657Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021022208) }) = true
      norm_num [leaf4657Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4657CertificateValid :
    WideCertificateValid leaf4657Box leaf4657Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi295ValidityFacts
    leaf4657LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4657CoverageChecked :
    coverageCheck (innerAD leaf4657Box) leaf4657InnerLog = true := by
  rfl'

private theorem leaf4657InnerLogValid :
    leaf4657InnerLog.Valid 8 (innerAD leaf4657Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4657CoverageChecked

private noncomputable def leaf4657InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4657InputLogOnePlusV_eq :
    leaf4657InputLogOnePlusV = outerEnclosure 24
      (leaf4657Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4657RoundedFacts : LeafRoundedFacts 8
    leaf4657Certificate.logOnePlusV leaf4657InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4657InputLogOnePlusV_eq }

private noncomputable def leaf4657Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi295InputQChi innerPair551Input
    leaf4657InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4657LowerChecked :
    lowerCheck 24 leaf4657Box leaf4657Inputs = true := by
  rfl'

private theorem leaf4657CoversExact : CoversExact 8
    leaf4657Box leaf4657Certificate leaf4657InnerLog leaf4657Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi295RoundedFacts
    innerPair551RoundedFacts leaf4657RoundedFacts (by rfl)

private theorem leaf4657FlatSound : Sound leaf4657Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4657CertificateValid
    leaf4657InnerLogValid leaf4657CoversExact leaf4657LowerChecked

private noncomputable def leaf4658Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4658Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357350400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1135472579/1073741824) }, upper := { exponent := 1, mantissa := (1095/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716072959/68714700800) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf4658InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4658LocalValidity :
    LeafFacts leaf4658Box leaf4658Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4658Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357350400) }) = true
      norm_num [leaf4658Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4658CertificateValid :
    WideCertificateValid leaf4658Box leaf4658Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi296ValidityFacts
    leaf4658LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4658CoverageChecked :
    coverageCheck (innerAD leaf4658Box) leaf4658InnerLog = true := by
  rfl'

private theorem leaf4658InnerLogValid :
    leaf4658InnerLog.Valid 8 (innerAD leaf4658Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4658CoverageChecked

private noncomputable def leaf4658InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4658InputLogOnePlusV_eq :
    leaf4658InputLogOnePlusV = outerEnclosure 24
      (leaf4658Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4658RoundedFacts : LeafRoundedFacts 8
    leaf4658Certificate.logOnePlusV leaf4658InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4658InputLogOnePlusV_eq }

private noncomputable def leaf4658Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi296InputQChi innerPair243Input
    leaf4658InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4658LowerChecked :
    lowerCheck 24 leaf4658Box leaf4658Inputs = true := by
  rfl'

private theorem leaf4658CoversExact : CoversExact 8
    leaf4658Box leaf4658Certificate leaf4658InnerLog leaf4658Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi296RoundedFacts
    innerPair243RoundedFacts leaf4658RoundedFacts (by rfl)

private theorem leaf4658FlatSound : Sound leaf4658Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4658CertificateValid
    leaf4658InnerLogValid leaf4658CoversExact leaf4658LowerChecked

private noncomputable def leaf4659Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4659Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357410048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1120334691/1073741824) }, upper := { exponent := 1, mantissa := (17287/16384) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716132607/68714820096) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4659InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4659LocalValidity :
    LeafFacts leaf4659Box leaf4659Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4659Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357410048) }) = true
      norm_num [leaf4659Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4659CertificateValid :
    WideCertificateValid leaf4659Box leaf4659Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi293ValidityFacts
    leaf4659LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4659CoverageChecked :
    coverageCheck (innerAD leaf4659Box) leaf4659InnerLog = true := by
  rfl'

private theorem leaf4659InnerLogValid :
    leaf4659InnerLog.Valid 8 (innerAD leaf4659Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4659CoverageChecked

private noncomputable def leaf4659InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4659InputLogOnePlusV_eq :
    leaf4659InputLogOnePlusV = outerEnclosure 24
      (leaf4659Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4659RoundedFacts : LeafRoundedFacts 8
    leaf4659Certificate.logOnePlusV leaf4659InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4659InputLogOnePlusV_eq }

private noncomputable def leaf4659Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi293InputQChi innerPair242Input
    leaf4659InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4659LowerChecked :
    lowerCheck 24 leaf4659Box leaf4659Inputs = true := by
  rfl'

private theorem leaf4659CoversExact : CoversExact 8
    leaf4659Box leaf4659Certificate leaf4659InnerLog leaf4659Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi293RoundedFacts
    innerPair242RoundedFacts leaf4659RoundedFacts (by rfl)

private theorem leaf4659FlatSound : Sound leaf4659Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4659CertificateValid
    leaf4659InnerLogValid leaf4659CoversExact leaf4659LowerChecked

private noncomputable def leaf4660Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4660Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357382656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1127281081/1073741824) }, upper := { exponent := 1, mantissa := (8697/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716105215/68714765312) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4660InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4660LocalValidity :
    LeafFacts leaf4660Box leaf4660Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4660Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357382656) }) = true
      norm_num [leaf4660Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4660CertificateValid :
    WideCertificateValid leaf4660Box leaf4660Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi294ValidityFacts
    leaf4660LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4660CoverageChecked :
    coverageCheck (innerAD leaf4660Box) leaf4660InnerLog = true := by
  rfl'

private theorem leaf4660InnerLogValid :
    leaf4660InnerLog.Valid 8 (innerAD leaf4660Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4660CoverageChecked

private noncomputable def leaf4660InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4660InputLogOnePlusV_eq :
    leaf4660InputLogOnePlusV = outerEnclosure 24
      (leaf4660Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4660RoundedFacts : LeafRoundedFacts 8
    leaf4660Certificate.logOnePlusV leaf4660InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4660InputLogOnePlusV_eq }

private noncomputable def leaf4660Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi294InputQChi innerPair242Input
    leaf4660InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4660LowerChecked :
    lowerCheck 24 leaf4660Box leaf4660Inputs = true := by
  rfl'

private theorem leaf4660CoversExact : CoversExact 8
    leaf4660Box leaf4660Certificate leaf4660InnerLog leaf4660Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi294RoundedFacts
    innerPair242RoundedFacts leaf4660RoundedFacts (by rfl)

private theorem leaf4660FlatSound : Sound leaf4660Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4660CertificateValid
    leaf4660InnerLogValid leaf4660CoversExact leaf4660LowerChecked

private noncomputable def leaf4661Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4661Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (65529/65536), upper := (1108345889/1108302848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1125839377/1073741824) }, upper := { exponent := 1, mantissa := (4343/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2216648737/2216605696) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4661InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4661LocalValidity :
    LeafFacts leaf4661Box leaf4661Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4661Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1108345889/1108302848) }) = true
      norm_num [leaf4661Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4661CertificateValid :
    WideCertificateValid leaf4661Box leaf4661Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi293ValidityFacts
    leaf4661LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4661CoverageChecked :
    coverageCheck (innerAD leaf4661Box) leaf4661InnerLog = true := by
  rfl'

private theorem leaf4661InnerLogValid :
    leaf4661InnerLog.Valid 8 (innerAD leaf4661Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4661CoverageChecked

private noncomputable def leaf4661InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4661InputLogOnePlusV_eq :
    leaf4661InputLogOnePlusV = outerEnclosure 24
      (leaf4661Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4661RoundedFacts : LeafRoundedFacts 8
    leaf4661Certificate.logOnePlusV leaf4661InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4661InputLogOnePlusV_eq }

private noncomputable def leaf4661Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi293InputQChi innerPair242Input
    leaf4661InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4661LowerChecked :
    lowerCheck 24 leaf4661Box leaf4661Inputs = true := by
  rfl'

private theorem leaf4661CoversExact : CoversExact 8
    leaf4661Box leaf4661Certificate leaf4661InnerLog leaf4661Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi293RoundedFacts
    innerPair242RoundedFacts leaf4661RoundedFacts (by rfl)

private theorem leaf4661FlatSound : Sound leaf4661Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4661CertificateValid
    leaf4661InnerLogValid leaf4661CoversExact leaf4661LowerChecked

private noncomputable def leaf4662Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4662Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357360640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1132851299/1073741824) }, upper := { exponent := 1, mantissa := (2185/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716083199/68714721280) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4662InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf4662LocalValidity :
    LeafFacts leaf4662Box leaf4662Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4662Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357360640) }) = true
      norm_num [leaf4662Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4662CertificateValid :
    WideCertificateValid leaf4662Box leaf4662Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi294ValidityFacts
    leaf4662LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4662CoverageChecked :
    coverageCheck (innerAD leaf4662Box) leaf4662InnerLog = true := by
  rfl'

private theorem leaf4662InnerLogValid :
    leaf4662InnerLog.Valid 8 (innerAD leaf4662Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf4662CoverageChecked

private noncomputable def leaf4662InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4662InputLogOnePlusV_eq :
    leaf4662InputLogOnePlusV = outerEnclosure 24
      (leaf4662Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4662RoundedFacts : LeafRoundedFacts 8
    leaf4662Certificate.logOnePlusV leaf4662InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4662InputLogOnePlusV_eq }

private noncomputable def leaf4662Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi294InputQChi innerPair336Input
    leaf4662InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4662LowerChecked :
    lowerCheck 24 leaf4662Box leaf4662Inputs = true := by
  rfl'

private theorem leaf4662CoversExact : CoversExact 8
    leaf4662Box leaf4662Certificate leaf4662InnerLog leaf4662Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi294RoundedFacts
    innerPair336RoundedFacts leaf4662RoundedFacts (by rfl)

private theorem leaf4662FlatSound : Sound leaf4662Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4662CertificateValid
    leaf4662InnerLogValid leaf4662CoversExact leaf4662LowerChecked

private noncomputable def leaf4663Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4663Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357355264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1134227471/1073741824) }, upper := { exponent := 1, mantissa := (17501/16384) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716077823/68714710528) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4663InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf4663LocalValidity :
    LeafFacts leaf4663Box leaf4663Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4663Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357355264) }) = true
      norm_num [leaf4663Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4663CertificateValid :
    WideCertificateValid leaf4663Box leaf4663Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi295ValidityFacts
    leaf4663LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4663CoverageChecked :
    coverageCheck (innerAD leaf4663Box) leaf4663InnerLog = true := by
  rfl'

private theorem leaf4663InnerLogValid :
    leaf4663InnerLog.Valid 8 (innerAD leaf4663Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf4663CoverageChecked

private noncomputable def leaf4663InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4663InputLogOnePlusV_eq :
    leaf4663InputLogOnePlusV = outerEnclosure 24
      (leaf4663Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4663RoundedFacts : LeafRoundedFacts 8
    leaf4663Certificate.logOnePlusV leaf4663InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4663InputLogOnePlusV_eq }

private noncomputable def leaf4663Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi295InputQChi innerPair336Input
    leaf4663InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4663LowerChecked :
    lowerCheck 24 leaf4663Box leaf4663Inputs = true := by
  rfl'

private theorem leaf4663CoversExact : CoversExact 8
    leaf4663Box leaf4663Certificate leaf4663InnerLog leaf4663Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi295RoundedFacts
    innerPair336RoundedFacts leaf4663RoundedFacts (by rfl)

private theorem leaf4663FlatSound : Sound leaf4663Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4663CertificateValid
    leaf4663InnerLogValid leaf4663CoversExact leaf4663LowerChecked

private noncomputable def leaf4664Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4664Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908189696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1141173861/1073741824) }, upper := { exponent := 1, mantissa := (2201/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816578633/9816379392) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf4664InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4664LocalValidity :
    LeafFacts leaf4664Box leaf4664Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4664Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908189696) }) = true
      norm_num [leaf4664Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4664CertificateValid :
    WideCertificateValid leaf4664Box leaf4664Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi296ValidityFacts
    leaf4664LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4664CoverageChecked :
    coverageCheck (innerAD leaf4664Box) leaf4664InnerLog = true := by
  rfl'

private theorem leaf4664InnerLogValid :
    leaf4664InnerLog.Valid 8 (innerAD leaf4664Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4664CoverageChecked

private noncomputable def leaf4664InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4664InputLogOnePlusV_eq :
    leaf4664InputLogOnePlusV = outerEnclosure 24
      (leaf4664Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4664RoundedFacts : LeafRoundedFacts 8
    leaf4664Certificate.logOnePlusV leaf4664InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4664InputLogOnePlusV_eq }

private noncomputable def leaf4664Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi296InputQChi innerPair249Input
    leaf4664InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4664LowerChecked :
    lowerCheck 24 leaf4664Box leaf4664Inputs = true := by
  rfl'

private theorem leaf4664CoversExact : CoversExact 8
    leaf4664Box leaf4664Certificate leaf4664InnerLog leaf4664Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi296RoundedFacts
    innerPair249RoundedFacts leaf4664RoundedFacts (by rfl)

private theorem leaf4664FlatSound : Sound leaf4664Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4664CertificateValid
    leaf4664InnerLogValid leaf4664CoversExact leaf4664LowerChecked

private noncomputable def leaf4665Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4665Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357332992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1139863221/1073741824) }, upper := { exponent := 1, mantissa := (4397/4096) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716055551/68714665984) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4665InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4665LocalValidity :
    LeafFacts leaf4665Box leaf4665Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4665Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357332992) }) = true
      norm_num [leaf4665Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4665CertificateValid :
    WideCertificateValid leaf4665Box leaf4665Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi295ValidityFacts
    leaf4665LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4665CoverageChecked :
    coverageCheck (innerAD leaf4665Box) leaf4665InnerLog = true := by
  rfl'

private theorem leaf4665InnerLogValid :
    leaf4665InnerLog.Valid 8 (innerAD leaf4665Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4665CoverageChecked

private noncomputable def leaf4665InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4665InputLogOnePlusV_eq :
    leaf4665InputLogOnePlusV = outerEnclosure 24
      (leaf4665Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4665RoundedFacts : LeafRoundedFacts 8
    leaf4665Certificate.logOnePlusV leaf4665InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4665InputLogOnePlusV_eq }

private noncomputable def leaf4665Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi295InputQChi innerPair243Input
    leaf4665InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4665LowerChecked :
    lowerCheck 24 leaf4665Box leaf4665Inputs = true := by
  rfl'

private theorem leaf4665CoversExact : CoversExact 8
    leaf4665Box leaf4665Certificate leaf4665InnerLog leaf4665Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi295RoundedFacts
    innerPair243RoundedFacts leaf4665RoundedFacts (by rfl)

private theorem leaf4665FlatSound : Sound leaf4665Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4665CertificateValid
    leaf4665InnerLogValid leaf4665CoversExact leaf4665LowerChecked

private noncomputable def leaf4666Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4666Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357305344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1146875143/1073741824) }, upper := { exponent := 1, mantissa := (553/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716027903/68714610688) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf4666InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4666LocalValidity :
    LeafFacts leaf4666Box leaf4666Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4666Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357305344) }) = true
      norm_num [leaf4666Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4666CertificateValid :
    WideCertificateValid leaf4666Box leaf4666Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi296ValidityFacts
    leaf4666LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4666CoverageChecked :
    coverageCheck (innerAD leaf4666Box) leaf4666InnerLog = true := by
  rfl'

private theorem leaf4666InnerLogValid :
    leaf4666InnerLog.Valid 8 (innerAD leaf4666Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4666CoverageChecked

private noncomputable def leaf4666InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4666InputLogOnePlusV_eq :
    leaf4666InputLogOnePlusV = outerEnclosure 24
      (leaf4666Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4666RoundedFacts : LeafRoundedFacts 8
    leaf4666Certificate.logOnePlusV leaf4666InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4666InputLogOnePlusV_eq }

private noncomputable def leaf4666Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi296InputQChi innerPair249Input
    leaf4666InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4666LowerChecked :
    lowerCheck 24 leaf4666Box leaf4666Inputs = true := by
  rfl'

private theorem leaf4666CoversExact : CoversExact 8
    leaf4666Box leaf4666Certificate leaf4666InnerLog leaf4666Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi296RoundedFacts
    innerPair249RoundedFacts leaf4666RoundedFacts (by rfl)

private theorem leaf4666FlatSound : Sound leaf4666Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4666CertificateValid
    leaf4666InnerLogValid leaf4666CoversExact leaf4666LowerChecked

private noncomputable def leaf4667Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4667Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871291/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357478144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1103034247/1073741824) }, upper := { exponent := 1, mantissa := (17021/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716200703/68714956288) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4667InnerLog : WideLogData :=
  innerPair327Data

set_option maxRecDepth 1000000 in
private theorem leaf4667LocalValidity :
    LeafFacts leaf4667Box leaf4667Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4667Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357478144) }) = true
      norm_num [leaf4667Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4667CertificateValid :
    WideCertificateValid leaf4667Box leaf4667Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi289ValidityFacts
    leaf4667LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4667CoverageChecked :
    coverageCheck (innerAD leaf4667Box) leaf4667InnerLog = true := by
  rfl'

private theorem leaf4667InnerLogValid :
    leaf4667InnerLog.Valid 8 (innerAD leaf4667Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint86PositiveFacts.valid leaf4667CoverageChecked

private noncomputable def leaf4667InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4667InputLogOnePlusV_eq :
    leaf4667InputLogOnePlusV = outerEnclosure 24
      (leaf4667Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4667RoundedFacts : LeafRoundedFacts 8
    leaf4667Certificate.logOnePlusV leaf4667InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4667InputLogOnePlusV_eq }

private noncomputable def leaf4667Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi289InputQChi innerPair327Input
    leaf4667InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4667LowerChecked :
    lowerCheck 24 leaf4667Box leaf4667Inputs = true := by
  rfl'

private theorem leaf4667CoversExact : CoversExact 8
    leaf4667Box leaf4667Certificate leaf4667InnerLog leaf4667Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi289RoundedFacts
    innerPair327RoundedFacts leaf4667RoundedFacts (by rfl)

private theorem leaf4667FlatSound : Sound leaf4667Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4667CertificateValid
    leaf4667InnerLogValid leaf4667CoversExact leaf4667LowerChecked

private noncomputable def leaf4668Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4668Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357450240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1110111701/1073741824) }, upper := { exponent := 1, mantissa := (8565/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716172799/68714900480) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4668InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf4668LocalValidity :
    LeafFacts leaf4668Box leaf4668Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4668Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357450240) }) = true
      norm_num [leaf4668Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4668CertificateValid :
    WideCertificateValid leaf4668Box leaf4668Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi290ValidityFacts
    leaf4668LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4668CoverageChecked :
    coverageCheck (innerAD leaf4668Box) leaf4668InnerLog = true := by
  rfl'

private theorem leaf4668InnerLogValid :
    leaf4668InnerLog.Valid 8 (innerAD leaf4668Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf4668CoverageChecked

private noncomputable def leaf4668InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4668InputLogOnePlusV_eq :
    leaf4668InputLogOnePlusV = outerEnclosure 24
      (leaf4668Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4668RoundedFacts : LeafRoundedFacts 8
    leaf4668Certificate.logOnePlusV leaf4668InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4668InputLogOnePlusV_eq }

private noncomputable def leaf4668Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi290InputQChi innerPair248Input
    leaf4668InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4668LowerChecked :
    lowerCheck 24 leaf4668Box leaf4668Inputs = true := by
  rfl'

private theorem leaf4668CoversExact : CoversExact 8
    leaf4668Box leaf4668Certificate leaf4668InnerLog leaf4668Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi290RoundedFacts
    innerPair248RoundedFacts leaf4668RoundedFacts (by rfl)

private theorem leaf4668FlatSound : Sound leaf4668Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4668CertificateValid
    leaf4668InnerLogValid leaf4668CoversExact leaf4668LowerChecked

private noncomputable def leaf4669Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4669Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871293/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357457408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1108276805/1073741824) }, upper := { exponent := 1, mantissa := (8551/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716179967/68714914816) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4669InnerLog : WideLogData :=
  innerPair248Data

set_option maxRecDepth 1000000 in
private theorem leaf4669LocalValidity :
    LeafFacts leaf4669Box leaf4669Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4669Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357457408) }) = true
      norm_num [leaf4669Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4669CertificateValid :
    WideCertificateValid leaf4669Box leaf4669Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi289ValidityFacts
    leaf4669LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4669CoverageChecked :
    coverageCheck (innerAD leaf4669Box) leaf4669InnerLog = true := by
  rfl'

private theorem leaf4669InnerLogValid :
    leaf4669InnerLog.Valid 8 (innerAD leaf4669Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint284PositiveFacts.valid leaf4669CoverageChecked

private noncomputable def leaf4669InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4669InputLogOnePlusV_eq :
    leaf4669InputLogOnePlusV = outerEnclosure 24
      (leaf4669Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4669RoundedFacts : LeafRoundedFacts 8
    leaf4669Certificate.logOnePlusV leaf4669InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4669InputLogOnePlusV_eq }

private noncomputable def leaf4669Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi289InputQChi innerPair248Input
    leaf4669InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4669LowerChecked :
    lowerCheck 24 leaf4669Box leaf4669Inputs = true := by
  rfl'

private theorem leaf4669CoversExact : CoversExact 8
    leaf4669Box leaf4669Certificate leaf4669InnerLog leaf4669Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi289RoundedFacts
    innerPair248RoundedFacts leaf4669RoundedFacts (by rfl)

private theorem leaf4669FlatSound : Sound leaf4669Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4669CertificateValid
    leaf4669InnerLogValid leaf4669CoversExact leaf4669LowerChecked

private noncomputable def leaf4670Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4670Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357429248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1115419791/1073741824) }, upper := { exponent := 1, mantissa := (4303/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716151807/68714858496) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4670InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4670LocalValidity :
    LeafFacts leaf4670Box leaf4670Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4670Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357429248) }) = true
      norm_num [leaf4670Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4670CertificateValid :
    WideCertificateValid leaf4670Box leaf4670Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi290ValidityFacts
    leaf4670LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4670CoverageChecked :
    coverageCheck (innerAD leaf4670Box) leaf4670InnerLog = true := by
  rfl'

private theorem leaf4670InnerLogValid :
    leaf4670InnerLog.Valid 8 (innerAD leaf4670Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4670CoverageChecked

private noncomputable def leaf4670InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4670InputLogOnePlusV_eq :
    leaf4670InputLogOnePlusV = outerEnclosure 24
      (leaf4670Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4670RoundedFacts : LeafRoundedFacts 8
    leaf4670Certificate.logOnePlusV leaf4670InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4670InputLogOnePlusV_eq }

private noncomputable def leaf4670Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi290InputQChi innerPair242Input
    leaf4670InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4670LowerChecked :
    lowerCheck 24 leaf4670Box leaf4670Inputs = true := by
  rfl'

private theorem leaf4670CoversExact : CoversExact 8
    leaf4670Box leaf4670Certificate leaf4670InnerLog leaf4670Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi290RoundedFacts
    innerPair242RoundedFacts leaf4670RoundedFacts (by rfl)

private theorem leaf4670FlatSound : Sound leaf4670Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4670CertificateValid
    leaf4670InnerLogValid leaf4670CoversExact leaf4670LowerChecked

private noncomputable def leaf4671Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4671Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357422336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1117189155/1073741824) }, upper := { exponent := 1, mantissa := (17239/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716144895/68714844672) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4671InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4671LocalValidity :
    LeafFacts leaf4671Box leaf4671Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4671Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357422336) }) = true
      norm_num [leaf4671Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4671CertificateValid :
    WideCertificateValid leaf4671Box leaf4671Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi291ValidityFacts
    leaf4671LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4671CoverageChecked :
    coverageCheck (innerAD leaf4671Box) leaf4671InnerLog = true := by
  rfl'

private theorem leaf4671InnerLogValid :
    leaf4671InnerLog.Valid 8 (innerAD leaf4671Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4671CoverageChecked

private noncomputable def leaf4671InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4671InputLogOnePlusV_eq :
    leaf4671InputLogOnePlusV = outerEnclosure 24
      (leaf4671Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4671RoundedFacts : LeafRoundedFacts 8
    leaf4671Certificate.logOnePlusV leaf4671InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4671InputLogOnePlusV_eq }

private noncomputable def leaf4671Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi291InputQChi innerPair242Input
    leaf4671InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4671LowerChecked :
    lowerCheck 24 leaf4671Box leaf4671Inputs = true := by
  rfl'

private theorem leaf4671CoversExact : CoversExact 8
    leaf4671Box leaf4671Certificate leaf4671InnerLog leaf4671Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi291RoundedFacts
    innerPair242RoundedFacts leaf4671RoundedFacts (by rfl)

private theorem leaf4671FlatSound : Sound leaf4671Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4671CertificateValid
    leaf4671InnerLogValid leaf4671CoversExact leaf4671LowerChecked

private noncomputable def leaf4672Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4672Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357394432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1124266609/1073741824) }, upper := { exponent := 1, mantissa := (4337/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716116991/68714788864) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4672InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4672LocalValidity :
    LeafFacts leaf4672Box leaf4672Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4672Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357394432) }) = true
      norm_num [leaf4672Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4672CertificateValid :
    WideCertificateValid leaf4672Box leaf4672Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi292ValidityFacts
    leaf4672LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4672CoverageChecked :
    coverageCheck (innerAD leaf4672Box) leaf4672InnerLog = true := by
  rfl'

private theorem leaf4672InnerLogValid :
    leaf4672InnerLog.Valid 8 (innerAD leaf4672Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4672CoverageChecked

private noncomputable def leaf4672InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4672InputLogOnePlusV_eq :
    leaf4672InputLogOnePlusV = outerEnclosure 24
      (leaf4672Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4672RoundedFacts : LeafRoundedFacts 8
    leaf4672Certificate.logOnePlusV leaf4672InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4672InputLogOnePlusV_eq }

private noncomputable def leaf4672Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi292InputQChi innerPair242Input
    leaf4672InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4672LowerChecked :
    lowerCheck 24 leaf4672Box leaf4672Inputs = true := by
  rfl'

private theorem leaf4672CoversExact : CoversExact 8
    leaf4672Box leaf4672Certificate leaf4672InnerLog leaf4672Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi292RoundedFacts
    innerPair242RoundedFacts leaf4672RoundedFacts (by rfl)

private theorem leaf4672FlatSound : Sound leaf4672Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4672CertificateValid
    leaf4672InnerLogValid leaf4672CoversExact leaf4672LowerChecked

private noncomputable def leaf4673Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4673Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357401088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1122562777/1073741824) }, upper := { exponent := 1, mantissa := (8661/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716123647/68714802176) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4673InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4673LocalValidity :
    LeafFacts leaf4673Box leaf4673Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4673Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357401088) }) = true
      norm_num [leaf4673Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4673CertificateValid :
    WideCertificateValid leaf4673Box leaf4673Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi291ValidityFacts
    leaf4673LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4673CoverageChecked :
    coverageCheck (innerAD leaf4673Box) leaf4673InnerLog = true := by
  rfl'

private theorem leaf4673InnerLogValid :
    leaf4673InnerLog.Valid 8 (innerAD leaf4673Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4673CoverageChecked

private noncomputable def leaf4673InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4673InputLogOnePlusV_eq :
    leaf4673InputLogOnePlusV = outerEnclosure 24
      (leaf4673Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4673RoundedFacts : LeafRoundedFacts 8
    leaf4673Certificate.logOnePlusV leaf4673InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4673InputLogOnePlusV_eq }

private noncomputable def leaf4673Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi291InputQChi innerPair242Input
    leaf4673InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4673LowerChecked :
    lowerCheck 24 leaf4673Box leaf4673Inputs = true := by
  rfl'

private theorem leaf4673CoversExact : CoversExact 8
    leaf4673Box leaf4673Certificate leaf4673InnerLog leaf4673Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi291RoundedFacts
    innerPair242RoundedFacts leaf4673RoundedFacts (by rfl)

private theorem leaf4673FlatSound : Sound leaf4673Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4673CertificateValid
    leaf4673InnerLogValid leaf4673CoversExact leaf4673LowerChecked

private noncomputable def leaf4674Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4674Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357372928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1129705763/1073741824) }, upper := { exponent := 1, mantissa := (2179/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716095487/68714745856) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4674InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4674LocalValidity :
    LeafFacts leaf4674Box leaf4674Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4674Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357372928) }) = true
      norm_num [leaf4674Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4674CertificateValid :
    WideCertificateValid leaf4674Box leaf4674Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi292ValidityFacts
    leaf4674LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4674CoverageChecked :
    coverageCheck (innerAD leaf4674Box) leaf4674InnerLog = true := by
  rfl'

private theorem leaf4674InnerLogValid :
    leaf4674InnerLog.Valid 8 (innerAD leaf4674Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4674CoverageChecked

private noncomputable def leaf4674InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4674InputLogOnePlusV_eq :
    leaf4674InputLogOnePlusV = outerEnclosure 24
      (leaf4674Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4674RoundedFacts : LeafRoundedFacts 8
    leaf4674Certificate.logOnePlusV leaf4674InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4674InputLogOnePlusV_eq }

private noncomputable def leaf4674Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi292InputQChi innerPair551Input
    leaf4674InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4674LowerChecked :
    lowerCheck 24 leaf4674Box leaf4674Inputs = true := by
  rfl'

private theorem leaf4674CoversExact : CoversExact 8
    leaf4674Box leaf4674Certificate leaf4674InnerLog leaf4674Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi292RoundedFacts
    innerPair551RoundedFacts leaf4674RoundedFacts (by rfl)

private theorem leaf4674FlatSound : Sound leaf4674Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4674CertificateValid
    leaf4674InnerLogValid leaf4674CoversExact leaf4674LowerChecked

private noncomputable def leaf4675Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4675Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871295/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357436672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1113519363/1073741824) }, upper := { exponent := 1, mantissa := (17183/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716159231/68714873344) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4675InnerLog : WideLogData :=
  innerPair247Data

set_option maxRecDepth 1000000 in
private theorem leaf4675LocalValidity :
    LeafFacts leaf4675Box leaf4675Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4675Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357436672) }) = true
      norm_num [leaf4675Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4675CertificateValid :
    WideCertificateValid leaf4675Box leaf4675Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi289ValidityFacts
    leaf4675LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4675CoverageChecked :
    coverageCheck (innerAD leaf4675Box) leaf4675InnerLog = true := by
  rfl'

private theorem leaf4675InnerLogValid :
    leaf4675InnerLog.Valid 8 (innerAD leaf4675Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint89PositiveFacts.valid leaf4675CoverageChecked

private noncomputable def leaf4675InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4675InputLogOnePlusV_eq :
    leaf4675InputLogOnePlusV = outerEnclosure 24
      (leaf4675Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4675RoundedFacts : LeafRoundedFacts 8
    leaf4675Certificate.logOnePlusV leaf4675InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4675InputLogOnePlusV_eq }

private noncomputable def leaf4675Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi289InputQChi innerPair247Input
    leaf4675InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4675LowerChecked :
    lowerCheck 24 leaf4675Box leaf4675Inputs = true := by
  rfl'

private theorem leaf4675CoversExact : CoversExact 8
    leaf4675Box leaf4675Certificate leaf4675InnerLog leaf4675Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi289RoundedFacts
    innerPair247RoundedFacts leaf4675RoundedFacts (by rfl)

private theorem leaf4675FlatSound : Sound leaf4675Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4675CertificateValid
    leaf4675InnerLogValid leaf4675CoversExact leaf4675LowerChecked

private noncomputable def leaf4676Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4676Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357408256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1120727881/1073741824) }, upper := { exponent := 1, mantissa := (8647/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716130815/68714816512) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4676InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4676LocalValidity :
    LeafFacts leaf4676Box leaf4676Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4676Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357408256) }) = true
      norm_num [leaf4676Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4676CertificateValid :
    WideCertificateValid leaf4676Box leaf4676Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi290ValidityFacts
    leaf4676LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4676CoverageChecked :
    coverageCheck (innerAD leaf4676Box) leaf4676InnerLog = true := by
  rfl'

private theorem leaf4676InnerLogValid :
    leaf4676InnerLog.Valid 8 (innerAD leaf4676Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4676CoverageChecked

private noncomputable def leaf4676InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4676InputLogOnePlusV_eq :
    leaf4676InputLogOnePlusV = outerEnclosure 24
      (leaf4676Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4676RoundedFacts : LeafRoundedFacts 8
    leaf4676Certificate.logOnePlusV leaf4676InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4676InputLogOnePlusV_eq }

private noncomputable def leaf4676Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi290InputQChi innerPair242Input
    leaf4676InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4676LowerChecked :
    lowerCheck 24 leaf4676Box leaf4676Inputs = true := by
  rfl'

private theorem leaf4676CoversExact : CoversExact 8
    leaf4676Box leaf4676Certificate leaf4676InnerLog leaf4676Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi290RoundedFacts
    innerPair242RoundedFacts leaf4676RoundedFacts (by rfl)

private theorem leaf4676FlatSound : Sound leaf4676Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4676CertificateValid
    leaf4676InnerLogValid leaf4676CoversExact leaf4676LowerChecked

private noncomputable def leaf4677Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf4677Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871297/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357415936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1118761921/1073741824) }, upper := { exponent := 1, mantissa := (1079/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716138495/68714831872) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4677InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4677LocalValidity :
    LeafFacts leaf4677Box leaf4677Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4677Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357415936) }) = true
      norm_num [leaf4677Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4677CertificateValid :
    WideCertificateValid leaf4677Box leaf4677Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi289ValidityFacts
    leaf4677LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4677CoverageChecked :
    coverageCheck (innerAD leaf4677Box) leaf4677InnerLog = true := by
  rfl'

private theorem leaf4677InnerLogValid :
    leaf4677InnerLog.Valid 8 (innerAD leaf4677Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4677CoverageChecked

private noncomputable def leaf4677InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4677InputLogOnePlusV_eq :
    leaf4677InputLogOnePlusV = outerEnclosure 24
      (leaf4677Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4677RoundedFacts : LeafRoundedFacts 8
    leaf4677Certificate.logOnePlusV leaf4677InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4677InputLogOnePlusV_eq }

private noncomputable def leaf4677Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi289InputQChi innerPair242Input
    leaf4677InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4677LowerChecked :
    lowerCheck 24 leaf4677Box leaf4677Inputs = true := by
  rfl'

private theorem leaf4677CoversExact : CoversExact 8
    leaf4677Box leaf4677Certificate leaf4677InnerLog leaf4677Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi289RoundedFacts
    innerPair242RoundedFacts leaf4677RoundedFacts (by rfl)

private theorem leaf4677FlatSound : Sound leaf4677Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4677CertificateValid
    leaf4677InnerLogValid leaf4677CoversExact leaf4677LowerChecked

private noncomputable def leaf4678Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf4678Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357387264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1126035971/1073741824) }, upper := { exponent := 1, mantissa := (543/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716109823/68714774528) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4678InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4678LocalValidity :
    LeafFacts leaf4678Box leaf4678Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4678Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357387264) }) = true
      norm_num [leaf4678Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4678CertificateValid :
    WideCertificateValid leaf4678Box leaf4678Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi290ValidityFacts
    leaf4678LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4678CoverageChecked :
    coverageCheck (innerAD leaf4678Box) leaf4678InnerLog = true := by
  rfl'

private theorem leaf4678InnerLogValid :
    leaf4678InnerLog.Valid 8 (innerAD leaf4678Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4678CoverageChecked

private noncomputable def leaf4678InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4678InputLogOnePlusV_eq :
    leaf4678InputLogOnePlusV = outerEnclosure 24
      (leaf4678Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4678RoundedFacts : LeafRoundedFacts 8
    leaf4678Certificate.logOnePlusV leaf4678InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4678InputLogOnePlusV_eq }

private noncomputable def leaf4678Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi290InputQChi innerPair242Input
    leaf4678InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4678LowerChecked :
    lowerCheck 24 leaf4678Box leaf4678Inputs = true := by
  rfl'

private theorem leaf4678CoversExact : CoversExact 8
    leaf4678Box leaf4678Certificate leaf4678InnerLog leaf4678Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi290RoundedFacts
    innerPair242RoundedFacts leaf4678RoundedFacts (by rfl)

private theorem leaf4678FlatSound : Sound leaf4678Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4678CertificateValid
    leaf4678InnerLogValid leaf4678CoversExact leaf4678LowerChecked

private noncomputable def leaf4679Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4679Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908197120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1127936399/1073741824) }, upper := { exponent := 1, mantissa := (17405/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816586057/9816394240) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4679InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf4679LocalValidity :
    LeafFacts leaf4679Box leaf4679Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4679Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908197120) }) = true
      norm_num [leaf4679Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4679CertificateValid :
    WideCertificateValid leaf4679Box leaf4679Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi291ValidityFacts
    leaf4679LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4679CoverageChecked :
    coverageCheck (innerAD leaf4679Box) leaf4679InnerLog = true := by
  rfl'

private theorem leaf4679InnerLogValid :
    leaf4679InnerLog.Valid 8 (innerAD leaf4679Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf4679CoverageChecked

private noncomputable def leaf4679InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4679InputLogOnePlusV_eq :
    leaf4679InputLogOnePlusV = outerEnclosure 24
      (leaf4679Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4679RoundedFacts : LeafRoundedFacts 8
    leaf4679Certificate.logOnePlusV leaf4679InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4679InputLogOnePlusV_eq }

private noncomputable def leaf4679Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi291InputQChi innerPair242Input
    leaf4679InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4679LowerChecked :
    lowerCheck 24 leaf4679Box leaf4679Inputs = true := by
  rfl'

private theorem leaf4679CoversExact : CoversExact 8
    leaf4679Box leaf4679Certificate leaf4679InnerLog leaf4679Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi291RoundedFacts
    innerPair242RoundedFacts leaf4679RoundedFacts (by rfl)

private theorem leaf4679FlatSound : Sound leaf4679Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4679CertificateValid
    leaf4679InnerLogValid leaf4679CoversExact leaf4679LowerChecked

private noncomputable def leaf4680Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4680Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021020672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1135144917/1073741824) }, upper := { exponent := 1, mantissa := (4379/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042121999/4042041344) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4680InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf4680LocalValidity :
    LeafFacts leaf4680Box leaf4680Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4680Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021020672) }) = true
      norm_num [leaf4680Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4680CertificateValid :
    WideCertificateValid leaf4680Box leaf4680Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi292ValidityFacts
    leaf4680LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4680CoverageChecked :
    coverageCheck (innerAD leaf4680Box) leaf4680InnerLog = true := by
  rfl'

private theorem leaf4680InnerLogValid :
    leaf4680InnerLog.Valid 8 (innerAD leaf4680Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf4680CoverageChecked

private noncomputable def leaf4680InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4680InputLogOnePlusV_eq :
    leaf4680InputLogOnePlusV = outerEnclosure 24
      (leaf4680Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4680RoundedFacts : LeafRoundedFacts 8
    leaf4680Certificate.logOnePlusV leaf4680InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4680InputLogOnePlusV_eq }

private noncomputable def leaf4680Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi292InputQChi innerPair336Input
    leaf4680InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4680LowerChecked :
    lowerCheck 24 leaf4680Box leaf4680Inputs = true := by
  rfl'

private theorem leaf4680CoversExact : CoversExact 8
    leaf4680Box leaf4680Certificate leaf4680InnerLog leaf4680Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi292RoundedFacts
    innerPair336RoundedFacts leaf4680RoundedFacts (by rfl)

private theorem leaf4680FlatSound : Sound leaf4680Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4680CertificateValid
    leaf4680InnerLogValid leaf4680CoversExact leaf4680LowerChecked

private noncomputable def leaf4681Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf4681Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357358592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1133310021/1073741824) }, upper := { exponent := 1, mantissa := (1093/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716081151/68714717184) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4681InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf4681LocalValidity :
    LeafFacts leaf4681Box leaf4681Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4681Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357358592) }) = true
      norm_num [leaf4681Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4681CertificateValid :
    WideCertificateValid leaf4681Box leaf4681Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi291ValidityFacts
    leaf4681LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4681CoverageChecked :
    coverageCheck (innerAD leaf4681Box) leaf4681InnerLog = true := by
  rfl'

private theorem leaf4681InnerLogValid :
    leaf4681InnerLog.Valid 8 (innerAD leaf4681Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf4681CoverageChecked

private noncomputable def leaf4681InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4681InputLogOnePlusV_eq :
    leaf4681InputLogOnePlusV = outerEnclosure 24
      (leaf4681Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4681RoundedFacts : LeafRoundedFacts 8
    leaf4681Certificate.logOnePlusV leaf4681InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4681InputLogOnePlusV_eq }

private noncomputable def leaf4681Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi291InputQChi innerPair336Input
    leaf4681InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4681LowerChecked :
    lowerCheck 24 leaf4681Box leaf4681Inputs = true := by
  rfl'

private theorem leaf4681CoversExact : CoversExact 8
    leaf4681Box leaf4681Certificate leaf4681InnerLog leaf4681Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi291RoundedFacts
    innerPair336RoundedFacts leaf4681RoundedFacts (by rfl)

private theorem leaf4681FlatSound : Sound leaf4681Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4681CertificateValid
    leaf4681InnerLogValid leaf4681CoversExact leaf4681LowerChecked

private noncomputable def leaf4682Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf4682Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357329920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1140584071/1073741824) }, upper := { exponent := 1, mantissa := (275/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716052479/68714659840) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4682InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf4682LocalValidity :
    LeafFacts leaf4682Box leaf4682Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4682Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357329920) }) = true
      norm_num [leaf4682Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4682CertificateValid :
    WideCertificateValid leaf4682Box leaf4682Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi292ValidityFacts
    leaf4682LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4682CoverageChecked :
    coverageCheck (innerAD leaf4682Box) leaf4682InnerLog = true := by
  rfl'

private theorem leaf4682InnerLogValid :
    leaf4682InnerLog.Valid 8 (innerAD leaf4682Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf4682CoverageChecked

private noncomputable def leaf4682InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4682InputLogOnePlusV_eq :
    leaf4682InputLogOnePlusV = outerEnclosure 24
      (leaf4682Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4682RoundedFacts : LeafRoundedFacts 8
    leaf4682Certificate.logOnePlusV leaf4682InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4682InputLogOnePlusV_eq }

private noncomputable def leaf4682Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi292InputQChi innerPair335Input
    leaf4682InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4682LowerChecked :
    lowerCheck 24 leaf4682Box leaf4682Inputs = true := by
  rfl'

private theorem leaf4682CoversExact : CoversExact 8
    leaf4682Box leaf4682Certificate leaf4682InnerLog leaf4682Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi292RoundedFacts
    innerPair335RoundedFacts leaf4682RoundedFacts (by rfl)

private theorem leaf4682FlatSound : Sound leaf4682Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4682CertificateValid
    leaf4682InnerLogValid leaf4682CoversExact leaf4682LowerChecked

private noncomputable def leaf4683Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4683Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357366528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1131344063/1073741824) }, upper := { exponent := 1, mantissa := (17457/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716089087/68714733056) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4683InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf4683LocalValidity :
    LeafFacts leaf4683Box leaf4683Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4683Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357366528) }) = true
      norm_num [leaf4683Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4683CertificateValid :
    WideCertificateValid leaf4683Box leaf4683Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi293ValidityFacts
    leaf4683LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4683CoverageChecked :
    coverageCheck (innerAD leaf4683Box) leaf4683InnerLog = true := by
  rfl'

private theorem leaf4683InnerLogValid :
    leaf4683InnerLog.Valid 8 (innerAD leaf4683Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf4683CoverageChecked

private noncomputable def leaf4683InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4683InputLogOnePlusV_eq :
    leaf4683InputLogOnePlusV = outerEnclosure 24
      (leaf4683Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4683RoundedFacts : LeafRoundedFacts 8
    leaf4683Certificate.logOnePlusV leaf4683InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4683InputLogOnePlusV_eq }

private noncomputable def leaf4683Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi293InputQChi innerPair551Input
    leaf4683InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4683LowerChecked :
    lowerCheck 24 leaf4683Box leaf4683Inputs = true := by
  rfl'

private theorem leaf4683CoversExact : CoversExact 8
    leaf4683Box leaf4683Certificate leaf4683InnerLog leaf4683Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi293RoundedFacts
    innerPair551RoundedFacts leaf4683RoundedFacts (by rfl)

private theorem leaf4683FlatSound : Sound leaf4683Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4683CertificateValid
    leaf4683InnerLogValid leaf4683CoversExact leaf4683LowerChecked

private noncomputable def leaf4684Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4684Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908191232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1138421517/1073741824) }, upper := { exponent := 1, mantissa := (8783/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816580169/9816382464) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4684InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf4684LocalValidity :
    LeafFacts leaf4684Box leaf4684Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4684Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908191232) }) = true
      norm_num [leaf4684Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4684CertificateValid :
    WideCertificateValid leaf4684Box leaf4684Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi294ValidityFacts
    leaf4684LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4684CoverageChecked :
    coverageCheck (innerAD leaf4684Box) leaf4684InnerLog = true := by
  rfl'

private theorem leaf4684InnerLogValid :
    leaf4684InnerLog.Valid 8 (innerAD leaf4684Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf4684CoverageChecked

private noncomputable def leaf4684InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4684InputLogOnePlusV_eq :
    leaf4684InputLogOnePlusV = outerEnclosure 24
      (leaf4684Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4684RoundedFacts : LeafRoundedFacts 8
    leaf4684Certificate.logOnePlusV leaf4684InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4684InputLogOnePlusV_eq }

private noncomputable def leaf4684Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi294InputQChi innerPair335Input
    leaf4684InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4684LowerChecked :
    lowerCheck 24 leaf4684Box leaf4684Inputs = true := by
  rfl'

private theorem leaf4684CoversExact : CoversExact 8
    leaf4684Box leaf4684Certificate leaf4684InnerLog leaf4684Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi294RoundedFacts
    innerPair335RoundedFacts leaf4684RoundedFacts (by rfl)

private theorem leaf4684FlatSound : Sound leaf4684Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4684CertificateValid
    leaf4684InnerLogValid leaf4684CoversExact leaf4684LowerChecked

private noncomputable def leaf4685Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4685Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357344768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1136848749/1073741824) }, upper := { exponent := 1, mantissa := (8771/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716067327/68714689536) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4685InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf4685LocalValidity :
    LeafFacts leaf4685Box leaf4685Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4685Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357344768) }) = true
      norm_num [leaf4685Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4685CertificateValid :
    WideCertificateValid leaf4685Box leaf4685Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi293ValidityFacts
    leaf4685LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4685CoverageChecked :
    coverageCheck (innerAD leaf4685Box) leaf4685InnerLog = true := by
  rfl'

private theorem leaf4685InnerLogValid :
    leaf4685InnerLog.Valid 8 (innerAD leaf4685Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf4685CoverageChecked

private noncomputable def leaf4685InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4685InputLogOnePlusV_eq :
    leaf4685InputLogOnePlusV = outerEnclosure 24
      (leaf4685Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4685RoundedFacts : LeafRoundedFacts 8
    leaf4685Certificate.logOnePlusV leaf4685InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4685InputLogOnePlusV_eq }

private noncomputable def leaf4685Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi293InputQChi innerPair335Input
    leaf4685InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4685LowerChecked :
    lowerCheck 24 leaf4685Box leaf4685Inputs = true := by
  rfl'

private theorem leaf4685CoversExact : CoversExact 8
    leaf4685Box leaf4685Certificate leaf4685InnerLog leaf4685Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi293RoundedFacts
    innerPair335RoundedFacts leaf4685RoundedFacts (by rfl)

private theorem leaf4685FlatSound : Sound leaf4685Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4685CertificateValid
    leaf4685InnerLogValid leaf4685CoversExact leaf4685LowerChecked

private noncomputable def leaf4686Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4686Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (65529/65536), upper := (2021101327/2021018624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1143991735/1073741824) }, upper := { exponent := 1, mantissa := (4413/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4042119951/4042037248) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4686InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4686LocalValidity :
    LeafFacts leaf4686Box leaf4686Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4686Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2021101327/2021018624) }) = true
      norm_num [leaf4686Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4686CertificateValid :
    WideCertificateValid leaf4686Box leaf4686Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi294ValidityFacts
    leaf4686LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4686CoverageChecked :
    coverageCheck (innerAD leaf4686Box) leaf4686InnerLog = true := by
  rfl'

private theorem leaf4686InnerLogValid :
    leaf4686InnerLog.Valid 8 (innerAD leaf4686Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4686CoverageChecked

private noncomputable def leaf4686InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4686InputLogOnePlusV_eq :
    leaf4686InputLogOnePlusV = outerEnclosure 24
      (leaf4686Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4686RoundedFacts : LeafRoundedFacts 8
    leaf4686Certificate.logOnePlusV leaf4686InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4686InputLogOnePlusV_eq }

private noncomputable def leaf4686Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi294InputQChi innerPair249Input
    leaf4686InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4686LowerChecked :
    lowerCheck 24 leaf4686Box leaf4686Inputs = true := by
  rfl'

private theorem leaf4686CoversExact : CoversExact 8
    leaf4686Box leaf4686Certificate leaf4686InnerLog leaf4686Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi294RoundedFacts
    innerPair249RoundedFacts leaf4686RoundedFacts (by rfl)

private theorem leaf4686FlatSound : Sound leaf4686Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4686CertificateValid
    leaf4686InnerLogValid leaf4686CoversExact leaf4686LowerChecked

private noncomputable def leaf4687Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4687Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357310720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1145498971/1073741824) }, upper := { exponent := 1, mantissa := (17675/16384) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716033279/68714621440) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4687InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4687LocalValidity :
    LeafFacts leaf4687Box leaf4687Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4687Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357310720) }) = true
      norm_num [leaf4687Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4687CertificateValid :
    WideCertificateValid leaf4687Box leaf4687Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi295ValidityFacts
    leaf4687LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4687CoverageChecked :
    coverageCheck (innerAD leaf4687Box) leaf4687InnerLog = true := by
  rfl'

private theorem leaf4687InnerLogValid :
    leaf4687InnerLog.Valid 8 (innerAD leaf4687Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4687CoverageChecked

private noncomputable def leaf4687InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4687InputLogOnePlusV_eq :
    leaf4687InputLogOnePlusV = outerEnclosure 24
      (leaf4687Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4687RoundedFacts : LeafRoundedFacts 8
    leaf4687Certificate.logOnePlusV leaf4687InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4687InputLogOnePlusV_eq }

private noncomputable def leaf4687Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi295InputQChi innerPair249Input
    leaf4687InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4687LowerChecked :
    lowerCheck 24 leaf4687Box leaf4687Inputs = true := by
  rfl'

private theorem leaf4687CoversExact : CoversExact 8
    leaf4687Box leaf4687Certificate leaf4687InnerLog leaf4687Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi295RoundedFacts
    innerPair249RoundedFacts leaf4687RoundedFacts (by rfl)

private theorem leaf4687FlatSound : Sound leaf4687Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4687CertificateValid
    leaf4687InnerLogValid leaf4687CoversExact leaf4687LowerChecked

private noncomputable def leaf4688Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4688Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357282816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1152576425/1073741824) }, upper := { exponent := 1, mantissa := (2223/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716005375/68714565632) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4688InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4688LocalValidity :
    LeafFacts leaf4688Box leaf4688Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4688Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357282816) }) = true
      norm_num [leaf4688Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4688CertificateValid :
    WideCertificateValid leaf4688Box leaf4688Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi296ValidityFacts
    leaf4688LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4688CoverageChecked :
    coverageCheck (innerAD leaf4688Box) leaf4688InnerLog = true := by
  rfl'

private theorem leaf4688InnerLogValid :
    leaf4688InnerLog.Valid 8 (innerAD leaf4688Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4688CoverageChecked

private noncomputable def leaf4688InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4688InputLogOnePlusV_eq :
    leaf4688InputLogOnePlusV = outerEnclosure 24
      (leaf4688Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4688RoundedFacts : LeafRoundedFacts 8
    leaf4688Certificate.logOnePlusV leaf4688InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4688InputLogOnePlusV_eq }

private noncomputable def leaf4688Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi296InputQChi innerPair249Input
    leaf4688InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4688LowerChecked :
    lowerCheck 24 leaf4688Box leaf4688Inputs = true := by
  rfl'

private theorem leaf4688CoversExact : CoversExact 8
    leaf4688Box leaf4688Certificate leaf4688InnerLog leaf4688Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi296RoundedFacts
    innerPair249RoundedFacts leaf4688RoundedFacts (by rfl)

private theorem leaf4688FlatSound : Sound leaf4688Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4688CertificateValid
    leaf4688InnerLogValid leaf4688CoversExact leaf4688LowerChecked

private noncomputable def leaf4689Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4689Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (65529/65536), upper := (4908388937/4908184064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1151134721/1073741824) }, upper := { exponent := 1, mantissa := (8881/8192) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9816573001/9816368128) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4689InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4689LocalValidity :
    LeafFacts leaf4689Box leaf4689Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4689Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4908388937/4908184064) }) = true
      norm_num [leaf4689Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4689CertificateValid :
    WideCertificateValid leaf4689Box leaf4689Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi295ValidityFacts
    leaf4689LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4689CoverageChecked :
    coverageCheck (innerAD leaf4689Box) leaf4689InnerLog = true := by
  rfl'

private theorem leaf4689InnerLogValid :
    leaf4689InnerLog.Valid 8 (innerAD leaf4689Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4689CoverageChecked

private noncomputable def leaf4689InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4689InputLogOnePlusV_eq :
    leaf4689InputLogOnePlusV = outerEnclosure 24
      (leaf4689Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4689RoundedFacts : LeafRoundedFacts 8
    leaf4689Certificate.logOnePlusV leaf4689InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4689InputLogOnePlusV_eq }

private noncomputable def leaf4689Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi295InputQChi innerPair249Input
    leaf4689InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4689LowerChecked :
    lowerCheck 24 leaf4689Box leaf4689Inputs = true := by
  rfl'

private theorem leaf4689CoversExact : CoversExact 8
    leaf4689Box leaf4689Certificate leaf4689InnerLog leaf4689Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi295RoundedFacts
    innerPair249RoundedFacts leaf4689RoundedFacts (by rfl)

private theorem leaf4689FlatSound : Sound leaf4689Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4689CertificateValid
    leaf4689InnerLogValid leaf4689CoversExact leaf4689LowerChecked

private noncomputable def leaf4690Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4690Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357260288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1158277707/1073741824) }, upper := { exponent := 1, mantissa := (1117/1024) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715982847/68714520576) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4690InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4690LocalValidity :
    LeafFacts leaf4690Box leaf4690Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4690Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357260288) }) = true
      norm_num [leaf4690Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4690CertificateValid :
    WideCertificateValid leaf4690Box leaf4690Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi296ValidityFacts
    leaf4690LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4690CoverageChecked :
    coverageCheck (innerAD leaf4690Box) leaf4690InnerLog = true := by
  rfl'

private theorem leaf4690InnerLogValid :
    leaf4690InnerLog.Valid 8 (innerAD leaf4690Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4690CoverageChecked

private noncomputable def leaf4690InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4690InputLogOnePlusV_eq :
    leaf4690InputLogOnePlusV = outerEnclosure 24
      (leaf4690Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4690RoundedFacts : LeafRoundedFacts 8
    leaf4690Certificate.logOnePlusV leaf4690InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4690InputLogOnePlusV_eq }

private noncomputable def leaf4690Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi296InputQChi innerPair249Input
    leaf4690InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4690LowerChecked :
    lowerCheck 24 leaf4690Box leaf4690Inputs = true := by
  rfl'

private theorem leaf4690CoversExact : CoversExact 8
    leaf4690Box leaf4690Certificate leaf4690InnerLog leaf4690Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi296RoundedFacts
    innerPair249RoundedFacts leaf4690RoundedFacts (by rfl)

private theorem leaf4690FlatSound : Sound leaf4690Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4690CertificateValid
    leaf4690InnerLogValid leaf4690CoversExact leaf4690LowerChecked

private noncomputable def leaf4691Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4691Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357323008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1142353435/1073741824) }, upper := { exponent := 1, mantissa := (17627/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716045567/68714646016) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4691InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf4691LocalValidity :
    LeafFacts leaf4691Box leaf4691Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4691Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357323008) }) = true
      norm_num [leaf4691Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4691CertificateValid :
    WideCertificateValid leaf4691Box leaf4691Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi293ValidityFacts
    leaf4691LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4691CoverageChecked :
    coverageCheck (innerAD leaf4691Box) leaf4691InnerLog = true := by
  rfl'

private theorem leaf4691InnerLogValid :
    leaf4691InnerLog.Valid 8 (innerAD leaf4691Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf4691CoverageChecked

private noncomputable def leaf4691InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4691InputLogOnePlusV_eq :
    leaf4691InputLogOnePlusV = outerEnclosure 24
      (leaf4691Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4691RoundedFacts : LeafRoundedFacts 8
    leaf4691Certificate.logOnePlusV leaf4691InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4691InputLogOnePlusV_eq }

private noncomputable def leaf4691Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi293InputQChi innerPair253Input
    leaf4691InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4691LowerChecked :
    lowerCheck 24 leaf4691Box leaf4691Inputs = true := by
  rfl'

private theorem leaf4691CoversExact : CoversExact 8
    leaf4691Box leaf4691Certificate leaf4691InnerLog leaf4691Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi293RoundedFacts
    innerPair253RoundedFacts leaf4691RoundedFacts (by rfl)

private theorem leaf4691FlatSound : Sound leaf4691Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4691CertificateValid
    leaf4691InnerLogValid leaf4691CoversExact leaf4691LowerChecked

private noncomputable def leaf4692Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4692Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357294592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1149561953/1073741824) }, upper := { exponent := 1, mantissa := (8869/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68716017151/68714589184) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4692InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4692LocalValidity :
    LeafFacts leaf4692Box leaf4692Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4692Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357294592) }) = true
      norm_num [leaf4692Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4692CertificateValid :
    WideCertificateValid leaf4692Box leaf4692Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi294ValidityFacts
    leaf4692LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4692CoverageChecked :
    coverageCheck (innerAD leaf4692Box) leaf4692InnerLog = true := by
  rfl'

private theorem leaf4692InnerLogValid :
    leaf4692InnerLog.Valid 8 (innerAD leaf4692Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4692CoverageChecked

private noncomputable def leaf4692InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4692InputLogOnePlusV_eq :
    leaf4692InputLogOnePlusV = outerEnclosure 24
      (leaf4692Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4692RoundedFacts : LeafRoundedFacts 8
    leaf4692Certificate.logOnePlusV leaf4692InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4692InputLogOnePlusV_eq }

private noncomputable def leaf4692Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi294InputQChi innerPair249Input
    leaf4692InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4692LowerChecked :
    lowerCheck 24 leaf4692Box leaf4692Inputs = true := by
  rfl'

private theorem leaf4692CoversExact : CoversExact 8
    leaf4692Box leaf4692Certificate leaf4692InnerLog leaf4692Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi294RoundedFacts
    innerPair249RoundedFacts leaf4692RoundedFacts (by rfl)

private theorem leaf4692FlatSound : Sound leaf4692Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4692CertificateValid
    leaf4692InnerLogValid leaf4692CoversExact leaf4692LowerChecked

private noncomputable def leaf4693Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf4693Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357301248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1147858121/1073741824) }, upper := { exponent := 1, mantissa := (1107/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716023807/68714602496) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4693InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4693LocalValidity :
    LeafFacts leaf4693Box leaf4693Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4693Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357301248) }) = true
      norm_num [leaf4693Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4693CertificateValid :
    WideCertificateValid leaf4693Box leaf4693Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi293ValidityFacts
    leaf4693LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4693CoverageChecked :
    coverageCheck (innerAD leaf4693Box) leaf4693InnerLog = true := by
  rfl'

private theorem leaf4693InnerLogValid :
    leaf4693InnerLog.Valid 8 (innerAD leaf4693Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4693CoverageChecked

private noncomputable def leaf4693InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4693InputLogOnePlusV_eq :
    leaf4693InputLogOnePlusV = outerEnclosure 24
      (leaf4693Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4693RoundedFacts : LeafRoundedFacts 8
    leaf4693Certificate.logOnePlusV leaf4693InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4693InputLogOnePlusV_eq }

private noncomputable def leaf4693Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi293InputQChi innerPair249Input
    leaf4693InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4693LowerChecked :
    lowerCheck 24 leaf4693Box leaf4693Inputs = true := by
  rfl'

private theorem leaf4693CoversExact : CoversExact 8
    leaf4693Box leaf4693Certificate leaf4693InnerLog leaf4693Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi293RoundedFacts
    innerPair249RoundedFacts leaf4693RoundedFacts (by rfl)

private theorem leaf4693FlatSound : Sound leaf4693Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4693CertificateValid
    leaf4693InnerLogValid leaf4693CoversExact leaf4693LowerChecked

private noncomputable def leaf4694Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf4694Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357272576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1155132171/1073741824) }, upper := { exponent := 1, mantissa := (557/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715995135/68714545152) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4694InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4694LocalValidity :
    LeafFacts leaf4694Box leaf4694Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4694Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357272576) }) = true
      norm_num [leaf4694Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4694CertificateValid :
    WideCertificateValid leaf4694Box leaf4694Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi294ValidityFacts
    leaf4694LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4694CoverageChecked :
    coverageCheck (innerAD leaf4694Box) leaf4694InnerLog = true := by
  rfl'

private theorem leaf4694InnerLogValid :
    leaf4694InnerLog.Valid 8 (innerAD leaf4694Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4694CoverageChecked

private noncomputable def leaf4694InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4694InputLogOnePlusV_eq :
    leaf4694InputLogOnePlusV = outerEnclosure 24
      (leaf4694Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4694RoundedFacts : LeafRoundedFacts 8
    leaf4694Certificate.logOnePlusV leaf4694InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4694InputLogOnePlusV_eq }

private noncomputable def leaf4694Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi294InputQChi innerPair249Input
    leaf4694InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4694LowerChecked :
    lowerCheck 24 leaf4694Box leaf4694Inputs = true := by
  rfl'

private theorem leaf4694CoversExact : CoversExact 8
    leaf4694Box leaf4694Certificate leaf4694InnerLog leaf4694Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi294RoundedFacts
    innerPair249RoundedFacts leaf4694RoundedFacts (by rfl)

private theorem leaf4694FlatSound : Sound leaf4694Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4694CertificateValid
    leaf4694InnerLogValid leaf4694CoversExact leaf4694LowerChecked

private noncomputable def leaf4695Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4695Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357266176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1156770471/1073741824) }, upper := { exponent := 1, mantissa := (17849/16384) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715988735/68714532352) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4695InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4695LocalValidity :
    LeafFacts leaf4695Box leaf4695Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4695Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357266176) }) = true
      norm_num [leaf4695Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4695CertificateValid :
    WideCertificateValid leaf4695Box leaf4695Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi295ValidityFacts
    leaf4695LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4695CoverageChecked :
    coverageCheck (innerAD leaf4695Box) leaf4695InnerLog = true := by
  rfl'

private theorem leaf4695InnerLogValid :
    leaf4695InnerLog.Valid 8 (innerAD leaf4695Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4695CoverageChecked

private noncomputable def leaf4695InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4695InputLogOnePlusV_eq :
    leaf4695InputLogOnePlusV = outerEnclosure 24
      (leaf4695Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4695RoundedFacts : LeafRoundedFacts 8
    leaf4695Certificate.logOnePlusV leaf4695InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4695InputLogOnePlusV_eq }

private noncomputable def leaf4695Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi295InputQChi innerPair249Input
    leaf4695InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4695LowerChecked :
    lowerCheck 24 leaf4695Box leaf4695Inputs = true := by
  rfl'

private theorem leaf4695CoversExact : CoversExact 8
    leaf4695Box leaf4695Certificate leaf4695InnerLog leaf4695Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi295RoundedFacts
    innerPair249RoundedFacts leaf4695RoundedFacts (by rfl)

private theorem leaf4695FlatSound : Sound leaf4695Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4695CertificateValid
    leaf4695InnerLogValid leaf4695CoversExact leaf4695LowerChecked

private noncomputable def leaf4696Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4696Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (65529/65536), upper := (34358722559/34357237760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1163978989/1073741824) }, upper := { exponent := 1, mantissa := (2245/2048) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68715960319/68714475520) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4696InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf4696LocalValidity :
    LeafFacts leaf4696Box leaf4696Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4696Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358722559/34357237760) }) = true
      norm_num [leaf4696Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4696CertificateValid :
    WideCertificateValid leaf4696Box leaf4696Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi296ValidityFacts
    leaf4696LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4696CoverageChecked :
    coverageCheck (innerAD leaf4696Box) leaf4696InnerLog = true := by
  rfl'

private theorem leaf4696InnerLogValid :
    leaf4696InnerLog.Valid 8 (innerAD leaf4696Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf4696CoverageChecked

private noncomputable def leaf4696InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4696InputLogOnePlusV_eq :
    leaf4696InputLogOnePlusV = outerEnclosure 24
      (leaf4696Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4696RoundedFacts : LeafRoundedFacts 8
    leaf4696Certificate.logOnePlusV leaf4696InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4696InputLogOnePlusV_eq }

private noncomputable def leaf4696Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi296InputQChi innerPair332Input
    leaf4696InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4696LowerChecked :
    lowerCheck 24 leaf4696Box leaf4696Inputs = true := by
  rfl'

private theorem leaf4696CoversExact : CoversExact 8
    leaf4696Box leaf4696Certificate leaf4696InnerLog leaf4696Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi296RoundedFacts
    innerPair332RoundedFacts leaf4696RoundedFacts (by rfl)

private theorem leaf4696FlatSound : Sound leaf4696Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4696CertificateValid
    leaf4696InnerLogValid leaf4696CoversExact leaf4696LowerChecked

private noncomputable def leaf4697Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf4697Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357243904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1162406221/1073741824) }, upper := { exponent := 1, mantissa := (1121/1024) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715966463/68714487808) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4697InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf4697LocalValidity :
    LeafFacts leaf4697Box leaf4697Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4697Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357243904) }) = true
      norm_num [leaf4697Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4697CertificateValid :
    WideCertificateValid leaf4697Box leaf4697Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi295ValidityFacts
    leaf4697LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4697CoverageChecked :
    coverageCheck (innerAD leaf4697Box) leaf4697InnerLog = true := by
  rfl'

private theorem leaf4697InnerLogValid :
    leaf4697InnerLog.Valid 8 (innerAD leaf4697Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf4697CoverageChecked

private noncomputable def leaf4697InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4697InputLogOnePlusV_eq :
    leaf4697InputLogOnePlusV = outerEnclosure 24
      (leaf4697Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4697RoundedFacts : LeafRoundedFacts 8
    leaf4697Certificate.logOnePlusV leaf4697InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4697InputLogOnePlusV_eq }

private noncomputable def leaf4697Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi295InputQChi innerPair332Input
    leaf4697InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4697LowerChecked :
    lowerCheck 24 leaf4697Box leaf4697Inputs = true := by
  rfl'

private theorem leaf4697CoversExact : CoversExact 8
    leaf4697Box leaf4697Certificate leaf4697InnerLog leaf4697Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi295RoundedFacts
    innerPair332RoundedFacts leaf4697RoundedFacts (by rfl)

private theorem leaf4697FlatSound : Sound leaf4697Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4697CertificateValid
    leaf4697InnerLogValid leaf4697CoversExact leaf4697LowerChecked

private noncomputable def leaf4698Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf4698Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357215232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1169680271/1073741824) }, upper := { exponent := 1, mantissa := (141/128) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715937791/68714430464) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf4698InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf4698LocalValidity :
    LeafFacts leaf4698Box leaf4698Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4698Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357215232) }) = true
      norm_num [leaf4698Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4698CertificateValid :
    WideCertificateValid leaf4698Box leaf4698Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi296ValidityFacts
    leaf4698LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4698CoverageChecked :
    coverageCheck (innerAD leaf4698Box) leaf4698InnerLog = true := by
  rfl'

private theorem leaf4698InnerLogValid :
    leaf4698InnerLog.Valid 8 (innerAD leaf4698Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf4698CoverageChecked

private noncomputable def leaf4698InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4698InputLogOnePlusV_eq :
    leaf4698InputLogOnePlusV = outerEnclosure 24
      (leaf4698Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4698RoundedFacts : LeafRoundedFacts 8
    leaf4698Certificate.logOnePlusV leaf4698InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4698InputLogOnePlusV_eq }

private noncomputable def leaf4698Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi296InputQChi innerPair612Input
    leaf4698InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4698LowerChecked :
    lowerCheck 24 leaf4698Box leaf4698Inputs = true := by
  rfl'

private theorem leaf4698CoversExact : CoversExact 8
    leaf4698Box leaf4698Certificate leaf4698InnerLog leaf4698Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi296RoundedFacts
    innerPair612RoundedFacts leaf4698RoundedFacts (by rfl)

private theorem leaf4698FlatSound : Sound leaf4698Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4698CertificateValid
    leaf4698InnerLogValid leaf4698CoversExact leaf4698LowerChecked

private noncomputable def component96Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node0_sound : Sound component96Node0Box :=
  sound_of_literal_split component96Node0Box leaf4635Box leaf4636Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4635FlatSound leaf4636FlatSound

private noncomputable def component96Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node1_sound : Sound component96Node1Box :=
  sound_of_literal_split component96Node1Box leaf4637Box leaf4638Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4637FlatSound leaf4638FlatSound

private noncomputable def component96Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node2_sound : Sound component96Node2Box :=
  sound_of_literal_split component96Node2Box component96Node0Box component96Node1Box
    .k (105/32) (by rfl) (by rfl)
    component96Node0_sound component96Node1_sound

private noncomputable def component96Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node3_sound : Sound component96Node3Box :=
  sound_of_literal_split component96Node3Box leaf4639Box leaf4640Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4639FlatSound leaf4640FlatSound

private noncomputable def component96Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node4_sound : Sound component96Node4Box :=
  sound_of_literal_split component96Node4Box leaf4641Box leaf4642Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4641FlatSound leaf4642FlatSound

private noncomputable def component96Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node5_sound : Sound component96Node5Box :=
  sound_of_literal_split component96Node5Box component96Node3Box component96Node4Box
    .k (105/32) (by rfl) (by rfl)
    component96Node3_sound component96Node4_sound

private noncomputable def component96Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node6_sound : Sound component96Node6Box :=
  sound_of_literal_split component96Node6Box component96Node2Box component96Node5Box
    .chi (41/128) (by rfl) (by rfl)
    component96Node2_sound component96Node5_sound

private noncomputable def component96Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node7_sound : Sound component96Node7Box :=
  sound_of_literal_split component96Node7Box leaf4643Box leaf4644Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4643FlatSound leaf4644FlatSound

private noncomputable def component96Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node8_sound : Sound component96Node8Box :=
  sound_of_literal_split component96Node8Box leaf4645Box leaf4646Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4645FlatSound leaf4646FlatSound

private noncomputable def component96Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node9_sound : Sound component96Node9Box :=
  sound_of_literal_split component96Node9Box component96Node7Box component96Node8Box
    .k (107/32) (by rfl) (by rfl)
    component96Node7_sound component96Node8_sound

private noncomputable def component96Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node10_sound : Sound component96Node10Box :=
  sound_of_literal_split component96Node10Box leaf4647Box leaf4648Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4647FlatSound leaf4648FlatSound

private noncomputable def component96Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node11_sound : Sound component96Node11Box :=
  sound_of_literal_split component96Node11Box leaf4649Box leaf4650Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4649FlatSound leaf4650FlatSound

private noncomputable def component96Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node12_sound : Sound component96Node12Box :=
  sound_of_literal_split component96Node12Box component96Node10Box component96Node11Box
    .k (107/32) (by rfl) (by rfl)
    component96Node10_sound component96Node11_sound

private noncomputable def component96Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node13_sound : Sound component96Node13Box :=
  sound_of_literal_split component96Node13Box component96Node9Box component96Node12Box
    .chi (41/128) (by rfl) (by rfl)
    component96Node9_sound component96Node12_sound

private noncomputable def component96Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node14_sound : Sound component96Node14Box :=
  sound_of_literal_split component96Node14Box component96Node6Box component96Node13Box
    .k (53/16) (by rfl) (by rfl)
    component96Node6_sound component96Node13_sound

private noncomputable def component96Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node15_sound : Sound component96Node15Box :=
  sound_of_literal_split component96Node15Box leaf4651Box leaf4652Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4651FlatSound leaf4652FlatSound

private noncomputable def component96Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node16_sound : Sound component96Node16Box :=
  sound_of_literal_split component96Node16Box leaf4653Box leaf4654Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4653FlatSound leaf4654FlatSound

private noncomputable def component96Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node17_sound : Sound component96Node17Box :=
  sound_of_literal_split component96Node17Box component96Node15Box component96Node16Box
    .k (105/32) (by rfl) (by rfl)
    component96Node15_sound component96Node16_sound

private noncomputable def component96Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node18_sound : Sound component96Node18Box :=
  sound_of_literal_split component96Node18Box leaf4655Box leaf4656Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4655FlatSound leaf4656FlatSound

private noncomputable def component96Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node19_sound : Sound component96Node19Box :=
  sound_of_literal_split component96Node19Box leaf4657Box leaf4658Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4657FlatSound leaf4658FlatSound

private noncomputable def component96Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node20_sound : Sound component96Node20Box :=
  sound_of_literal_split component96Node20Box component96Node18Box component96Node19Box
    .k (105/32) (by rfl) (by rfl)
    component96Node18_sound component96Node19_sound

private noncomputable def component96Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node21_sound : Sound component96Node21Box :=
  sound_of_literal_split component96Node21Box component96Node17Box component96Node20Box
    .chi (43/128) (by rfl) (by rfl)
    component96Node17_sound component96Node20_sound

private noncomputable def component96Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node22_sound : Sound component96Node22Box :=
  sound_of_literal_split component96Node22Box leaf4659Box leaf4660Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4659FlatSound leaf4660FlatSound

private noncomputable def component96Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node23_sound : Sound component96Node23Box :=
  sound_of_literal_split component96Node23Box leaf4661Box leaf4662Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4661FlatSound leaf4662FlatSound

private noncomputable def component96Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node24_sound : Sound component96Node24Box :=
  sound_of_literal_split component96Node24Box component96Node22Box component96Node23Box
    .k (107/32) (by rfl) (by rfl)
    component96Node22_sound component96Node23_sound

private noncomputable def component96Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node25_sound : Sound component96Node25Box :=
  sound_of_literal_split component96Node25Box leaf4663Box leaf4664Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4663FlatSound leaf4664FlatSound

private noncomputable def component96Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node26_sound : Sound component96Node26Box :=
  sound_of_literal_split component96Node26Box leaf4665Box leaf4666Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4665FlatSound leaf4666FlatSound

private noncomputable def component96Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node27_sound : Sound component96Node27Box :=
  sound_of_literal_split component96Node27Box component96Node25Box component96Node26Box
    .k (107/32) (by rfl) (by rfl)
    component96Node25_sound component96Node26_sound

private noncomputable def component96Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node28_sound : Sound component96Node28Box :=
  sound_of_literal_split component96Node28Box component96Node24Box component96Node27Box
    .chi (43/128) (by rfl) (by rfl)
    component96Node24_sound component96Node27_sound

private noncomputable def component96Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node29_sound : Sound component96Node29Box :=
  sound_of_literal_split component96Node29Box component96Node21Box component96Node28Box
    .k (53/16) (by rfl) (by rfl)
    component96Node21_sound component96Node28_sound

private noncomputable def component96Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node30_sound : Sound component96Node30Box :=
  sound_of_literal_split component96Node30Box component96Node14Box component96Node29Box
    .chi (21/64) (by rfl) (by rfl)
    component96Node14_sound component96Node29_sound

private noncomputable def component96Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node31_sound : Sound component96Node31Box :=
  sound_of_literal_split component96Node31Box leaf4667Box leaf4668Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4667FlatSound leaf4668FlatSound

private noncomputable def component96Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node32_sound : Sound component96Node32Box :=
  sound_of_literal_split component96Node32Box leaf4669Box leaf4670Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4669FlatSound leaf4670FlatSound

private noncomputable def component96Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node33_sound : Sound component96Node33Box :=
  sound_of_literal_split component96Node33Box component96Node31Box component96Node32Box
    .k (109/32) (by rfl) (by rfl)
    component96Node31_sound component96Node32_sound

private noncomputable def component96Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node34_sound : Sound component96Node34Box :=
  sound_of_literal_split component96Node34Box leaf4671Box leaf4672Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4671FlatSound leaf4672FlatSound

private noncomputable def component96Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node35_sound : Sound component96Node35Box :=
  sound_of_literal_split component96Node35Box leaf4673Box leaf4674Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4673FlatSound leaf4674FlatSound

private noncomputable def component96Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node36_sound : Sound component96Node36Box :=
  sound_of_literal_split component96Node36Box component96Node34Box component96Node35Box
    .k (109/32) (by rfl) (by rfl)
    component96Node34_sound component96Node35_sound

private noncomputable def component96Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node37_sound : Sound component96Node37Box :=
  sound_of_literal_split component96Node37Box component96Node33Box component96Node36Box
    .chi (41/128) (by rfl) (by rfl)
    component96Node33_sound component96Node36_sound

private noncomputable def component96Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node38_sound : Sound component96Node38Box :=
  sound_of_literal_split component96Node38Box leaf4675Box leaf4676Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4675FlatSound leaf4676FlatSound

private noncomputable def component96Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node39_sound : Sound component96Node39Box :=
  sound_of_literal_split component96Node39Box leaf4677Box leaf4678Box
    .chi (81/256) (by rfl) (by rfl)
    leaf4677FlatSound leaf4678FlatSound

private noncomputable def component96Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node40_sound : Sound component96Node40Box :=
  sound_of_literal_split component96Node40Box component96Node38Box component96Node39Box
    .k (111/32) (by rfl) (by rfl)
    component96Node38_sound component96Node39_sound

private noncomputable def component96Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node41_sound : Sound component96Node41Box :=
  sound_of_literal_split component96Node41Box leaf4679Box leaf4680Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4679FlatSound leaf4680FlatSound

private noncomputable def component96Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node42_sound : Sound component96Node42Box :=
  sound_of_literal_split component96Node42Box leaf4681Box leaf4682Box
    .chi (83/256) (by rfl) (by rfl)
    leaf4681FlatSound leaf4682FlatSound

private noncomputable def component96Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node43_sound : Sound component96Node43Box :=
  sound_of_literal_split component96Node43Box component96Node41Box component96Node42Box
    .k (111/32) (by rfl) (by rfl)
    component96Node41_sound component96Node42_sound

private noncomputable def component96Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node44_sound : Sound component96Node44Box :=
  sound_of_literal_split component96Node44Box component96Node40Box component96Node43Box
    .chi (41/128) (by rfl) (by rfl)
    component96Node40_sound component96Node43_sound

private noncomputable def component96Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component96Node45_sound : Sound component96Node45Box :=
  sound_of_literal_split component96Node45Box component96Node37Box component96Node44Box
    .k (55/16) (by rfl) (by rfl)
    component96Node37_sound component96Node44_sound

private noncomputable def component96Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node46_sound : Sound component96Node46Box :=
  sound_of_literal_split component96Node46Box leaf4683Box leaf4684Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4683FlatSound leaf4684FlatSound

private noncomputable def component96Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node47_sound : Sound component96Node47Box :=
  sound_of_literal_split component96Node47Box leaf4685Box leaf4686Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4685FlatSound leaf4686FlatSound

private noncomputable def component96Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node48_sound : Sound component96Node48Box :=
  sound_of_literal_split component96Node48Box component96Node46Box component96Node47Box
    .k (109/32) (by rfl) (by rfl)
    component96Node46_sound component96Node47_sound

private noncomputable def component96Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node49_sound : Sound component96Node49Box :=
  sound_of_literal_split component96Node49Box leaf4687Box leaf4688Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4687FlatSound leaf4688FlatSound

private noncomputable def component96Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node50_sound : Sound component96Node50Box :=
  sound_of_literal_split component96Node50Box leaf4689Box leaf4690Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4689FlatSound leaf4690FlatSound

private noncomputable def component96Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node51_sound : Sound component96Node51Box :=
  sound_of_literal_split component96Node51Box component96Node49Box component96Node50Box
    .k (109/32) (by rfl) (by rfl)
    component96Node49_sound component96Node50_sound

private noncomputable def component96Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node52_sound : Sound component96Node52Box :=
  sound_of_literal_split component96Node52Box component96Node48Box component96Node51Box
    .chi (43/128) (by rfl) (by rfl)
    component96Node48_sound component96Node51_sound

private noncomputable def component96Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node53_sound : Sound component96Node53Box :=
  sound_of_literal_split component96Node53Box leaf4691Box leaf4692Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4691FlatSound leaf4692FlatSound

private noncomputable def component96Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node54_sound : Sound component96Node54Box :=
  sound_of_literal_split component96Node54Box leaf4693Box leaf4694Box
    .chi (85/256) (by rfl) (by rfl)
    leaf4693FlatSound leaf4694FlatSound

private noncomputable def component96Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component96Node55_sound : Sound component96Node55Box :=
  sound_of_literal_split component96Node55Box component96Node53Box component96Node54Box
    .k (111/32) (by rfl) (by rfl)
    component96Node53_sound component96Node54_sound

private noncomputable def component96Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node56_sound : Sound component96Node56Box :=
  sound_of_literal_split component96Node56Box leaf4695Box leaf4696Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4695FlatSound leaf4696FlatSound

private noncomputable def component96Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node57_sound : Sound component96Node57Box :=
  sound_of_literal_split component96Node57Box leaf4697Box leaf4698Box
    .chi (87/256) (by rfl) (by rfl)
    leaf4697FlatSound leaf4698FlatSound

private noncomputable def component96Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node58_sound : Sound component96Node58Box :=
  sound_of_literal_split component96Node58Box component96Node56Box component96Node57Box
    .k (111/32) (by rfl) (by rfl)
    component96Node56_sound component96Node57_sound

private noncomputable def component96Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node59_sound : Sound component96Node59Box :=
  sound_of_literal_split component96Node59Box component96Node55Box component96Node58Box
    .chi (43/128) (by rfl) (by rfl)
    component96Node55_sound component96Node58_sound

private noncomputable def component96Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node60_sound : Sound component96Node60Box :=
  sound_of_literal_split component96Node60Box component96Node52Box component96Node59Box
    .k (55/16) (by rfl) (by rfl)
    component96Node52_sound component96Node59_sound

private noncomputable def component96Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component96Node61_sound : Sound component96Node61Box :=
  sound_of_literal_split component96Node61Box component96Node45Box component96Node60Box
    .chi (21/64) (by rfl) (by rfl)
    component96Node45_sound component96Node60_sound

noncomputable def component96Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
theorem component96_sound : Sound component96Box :=
  sound_of_literal_split component96Box component96Node30Box component96Node61Box
    .k (27/8) (by rfl) (by rfl)
    component96Node30_sound component96Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
