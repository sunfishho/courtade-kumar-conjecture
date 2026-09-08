import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf1772Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1772Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214903) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (712987887/536870912) }, upper := { exponent := 0, mantissa := (11017/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432759/268429806) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1772InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1772LocalValidity :
    LeafFacts leaf1772Box leaf1772Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1772Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214903) }) = true
      norm_num [leaf1772Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1772CertificateValid :
    WideCertificateValid leaf1772Box leaf1772Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi131ValidityFacts
    leaf1772LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1772CoverageChecked :
    coverageCheck (innerAD leaf1772Box) leaf1772InnerLog = true := by
  rfl'

private theorem leaf1772InnerLogValid :
    leaf1772InnerLog.Valid 8 (innerAD leaf1772Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1772CoverageChecked

private noncomputable def leaf1772InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1772InputLogOnePlusV_eq :
    leaf1772InputLogOnePlusV = outerEnclosure 24
      (leaf1772Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1772RoundedFacts : LeafRoundedFacts 8
    leaf1772Certificate.logOnePlusV leaf1772InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1772InputLogOnePlusV_eq }

private noncomputable def leaf1772Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1772InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1772LowerChecked :
    lowerCheck 24 leaf1772Box leaf1772Inputs = true := by
  rfl'

private theorem leaf1772CoversExact : CoversExact 8
    leaf1772Box leaf1772Certificate leaf1772InnerLog leaf1772Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1772RoundedFacts (by rfl)

private theorem leaf1772FlatSound : Sound leaf1772Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1772CertificateValid
    leaf1772InnerLogValid leaf1772CoversExact leaf1772LowerChecked

private noncomputable def leaf1773Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1773Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107439) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (714560653/536870912) }, upper := { exponent := 0, mantissa := (5521/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216367/134214878) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1773InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1773LocalValidity :
    LeafFacts leaf1773Box leaf1773Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1773Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107439) }) = true
      norm_num [leaf1773Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1773CertificateValid :
    WideCertificateValid leaf1773Box leaf1773Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi131ValidityFacts
    leaf1773LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1773CoverageChecked :
    coverageCheck (innerAD leaf1773Box) leaf1773InnerLog = true := by
  rfl'

private theorem leaf1773InnerLogValid :
    leaf1773InnerLog.Valid 8 (innerAD leaf1773Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1773CoverageChecked

private noncomputable def leaf1773InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1773InputLogOnePlusV_eq :
    leaf1773InputLogOnePlusV = outerEnclosure 24
      (leaf1773Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1773RoundedFacts : LeafRoundedFacts 8
    leaf1773Certificate.logOnePlusV leaf1773InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1773InputLogOnePlusV_eq }

private noncomputable def leaf1773Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1773InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1773LowerChecked :
    lowerCheck 24 leaf1773Box leaf1773Inputs = true := by
  rfl'

private theorem leaf1773CoversExact : CoversExact 8
    leaf1773Box leaf1773Certificate leaf1773InnerLog leaf1773Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1773RoundedFacts (by rfl)

private theorem leaf1773FlatSound : Sound leaf1773Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1773CertificateValid
    leaf1773InnerLogValid leaf1773CoversExact leaf1773LowerChecked

private noncomputable def leaf1774Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1774Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107395) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (720327469/536870912) }, upper := { exponent := 0, mantissa := (5565/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216323/134214790) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1774InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1774LocalValidity :
    LeafFacts leaf1774Box leaf1774Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1774Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107395) }) = true
      norm_num [leaf1774Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1774CertificateValid :
    WideCertificateValid leaf1774Box leaf1774Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi132ValidityFacts
    leaf1774LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1774CoverageChecked :
    coverageCheck (innerAD leaf1774Box) leaf1774InnerLog = true := by
  rfl'

private theorem leaf1774InnerLogValid :
    leaf1774InnerLog.Valid 8 (innerAD leaf1774Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1774CoverageChecked

private noncomputable def leaf1774InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1774InputLogOnePlusV_eq :
    leaf1774InputLogOnePlusV = outerEnclosure 24
      (leaf1774Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1774RoundedFacts : LeafRoundedFacts 8
    leaf1774Certificate.logOnePlusV leaf1774InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1774InputLogOnePlusV_eq }

private noncomputable def leaf1774Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1774InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1774LowerChecked :
    lowerCheck 24 leaf1774Box leaf1774Inputs = true := by
  rfl'

private theorem leaf1774CoversExact : CoversExact 8
    leaf1774Box leaf1774Certificate leaf1774InnerLog leaf1774Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1774RoundedFacts (by rfl)

private theorem leaf1774FlatSound : Sound leaf1774Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1774CertificateValid
    leaf1774InnerLogValid leaf1774CoversExact leaf1774LowerChecked

private noncomputable def leaf1775Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1775Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553691) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (721965767/536870912) }, upper := { exponent := 0, mantissa := (2789/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108155/67107382) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1775InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1775LocalValidity :
    LeafFacts leaf1775Box leaf1775Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1775Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553691) }) = true
      norm_num [leaf1775Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1775CertificateValid :
    WideCertificateValid leaf1775Box leaf1775Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi132ValidityFacts
    leaf1775LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1775CoverageChecked :
    coverageCheck (innerAD leaf1775Box) leaf1775InnerLog = true := by
  rfl'

private theorem leaf1775InnerLogValid :
    leaf1775InnerLog.Valid 8 (innerAD leaf1775Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1775CoverageChecked

private noncomputable def leaf1775InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1775InputLogOnePlusV_eq :
    leaf1775InputLogOnePlusV = outerEnclosure 24
      (leaf1775Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1775RoundedFacts : LeafRoundedFacts 8
    leaf1775Certificate.logOnePlusV leaf1775InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1775InputLogOnePlusV_eq }

private noncomputable def leaf1775Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1775InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1775LowerChecked :
    lowerCheck 24 leaf1775Box leaf1775Inputs = true := by
  rfl'

private theorem leaf1775CoversExact : CoversExact 8
    leaf1775Box leaf1775Certificate leaf1775InnerLog leaf1775Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1775RoundedFacts (by rfl)

private theorem leaf1775FlatSound : Sound leaf1775Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1775CertificateValid
    leaf1775InnerLogValid leaf1775CoversExact leaf1775LowerChecked

private noncomputable def leaf1776Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1776Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214853) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (716133419/536870912) }, upper := { exponent := 0, mantissa := (11067/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432709/268429706) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1776InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1776LocalValidity :
    LeafFacts leaf1776Box leaf1776Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1776Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214853) }) = true
      norm_num [leaf1776Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1776CertificateValid :
    WideCertificateValid leaf1776Box leaf1776Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi131ValidityFacts
    leaf1776LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1776CoverageChecked :
    coverageCheck (innerAD leaf1776Box) leaf1776InnerLog = true := by
  rfl'

private theorem leaf1776InnerLogValid :
    leaf1776InnerLog.Valid 8 (innerAD leaf1776Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1776CoverageChecked

private noncomputable def leaf1776InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1776InputLogOnePlusV_eq :
    leaf1776InputLogOnePlusV = outerEnclosure 24
      (leaf1776Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1776RoundedFacts : LeafRoundedFacts 8
    leaf1776Certificate.logOnePlusV leaf1776InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1776InputLogOnePlusV_eq }

private noncomputable def leaf1776Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1776InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1776LowerChecked :
    lowerCheck 24 leaf1776Box leaf1776Inputs = true := by
  rfl'

private theorem leaf1776CoversExact : CoversExact 8
    leaf1776Box leaf1776Certificate leaf1776InnerLog leaf1776Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1776RoundedFacts (by rfl)

private theorem leaf1776FlatSound : Sound leaf1776Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1776CertificateValid
    leaf1776InnerLogValid leaf1776CoversExact leaf1776LowerChecked

private noncomputable def leaf1777Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1777Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553707) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (717706185/536870912) }, upper := { exponent := 0, mantissa := (2773/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108171/67107414) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1777InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1777LocalValidity :
    LeafFacts leaf1777Box leaf1777Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1777Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553707) }) = true
      norm_num [leaf1777Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1777CertificateValid :
    WideCertificateValid leaf1777Box leaf1777Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi131ValidityFacts
    leaf1777LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1777CoverageChecked :
    coverageCheck (innerAD leaf1777Box) leaf1777InnerLog = true := by
  rfl'

private theorem leaf1777InnerLogValid :
    leaf1777InnerLog.Valid 8 (innerAD leaf1777Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1777CoverageChecked

private noncomputable def leaf1777InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1777InputLogOnePlusV_eq :
    leaf1777InputLogOnePlusV = outerEnclosure 24
      (leaf1777Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1777RoundedFacts : LeafRoundedFacts 8
    leaf1777Certificate.logOnePlusV leaf1777InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1777InputLogOnePlusV_eq }

private noncomputable def leaf1777Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1777InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1777LowerChecked :
    lowerCheck 24 leaf1777Box leaf1777Inputs = true := by
  rfl'

private theorem leaf1777CoversExact : CoversExact 8
    leaf1777Box leaf1777Certificate leaf1777InnerLog leaf1777Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1777RoundedFacts (by rfl)

private theorem leaf1777FlatSound : Sound leaf1777Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1777CertificateValid
    leaf1777InnerLogValid leaf1777CoversExact leaf1777LowerChecked

private noncomputable def leaf1778Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1778Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107369) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (723604065/536870912) }, upper := { exponent := 0, mantissa := (5591/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216297/134214738) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1778InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1778LocalValidity :
    LeafFacts leaf1778Box leaf1778Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1778Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107369) }) = true
      norm_num [leaf1778Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1778CertificateValid :
    WideCertificateValid leaf1778Box leaf1778Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi132ValidityFacts
    leaf1778LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1778CoverageChecked :
    coverageCheck (innerAD leaf1778Box) leaf1778InnerLog = true := by
  rfl'

private theorem leaf1778InnerLogValid :
    leaf1778InnerLog.Valid 8 (innerAD leaf1778Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1778CoverageChecked

private noncomputable def leaf1778InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1778InputLogOnePlusV_eq :
    leaf1778InputLogOnePlusV = outerEnclosure 24
      (leaf1778Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1778RoundedFacts : LeafRoundedFacts 8
    leaf1778Certificate.logOnePlusV leaf1778InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1778InputLogOnePlusV_eq }

private noncomputable def leaf1778Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1778InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1778LowerChecked :
    lowerCheck 24 leaf1778Box leaf1778Inputs = true := by
  rfl'

private theorem leaf1778CoversExact : CoversExact 8
    leaf1778Box leaf1778Certificate leaf1778InnerLog leaf1778Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1778RoundedFacts (by rfl)

private theorem leaf1778FlatSound : Sound leaf1778Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1778CertificateValid
    leaf1778InnerLogValid leaf1778CoversExact leaf1778LowerChecked

private noncomputable def leaf1779Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1779Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776839) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (725242363/536870912) }, upper := { exponent := 0, mantissa := (1401/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554071/33553678) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1779InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1779LocalValidity :
    LeafFacts leaf1779Box leaf1779Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1779Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776839) }) = true
      norm_num [leaf1779Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1779CertificateValid :
    WideCertificateValid leaf1779Box leaf1779Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi132ValidityFacts
    leaf1779LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1779CoverageChecked :
    coverageCheck (innerAD leaf1779Box) leaf1779InnerLog = true := by
  rfl'

private theorem leaf1779InnerLogValid :
    leaf1779InnerLog.Valid 8 (innerAD leaf1779Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1779CoverageChecked

private noncomputable def leaf1779InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1779InputLogOnePlusV_eq :
    leaf1779InputLogOnePlusV = outerEnclosure 24
      (leaf1779Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1779RoundedFacts : LeafRoundedFacts 8
    leaf1779Certificate.logOnePlusV leaf1779InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1779InputLogOnePlusV_eq }

private noncomputable def leaf1779Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1779InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1779LowerChecked :
    lowerCheck 24 leaf1779Box leaf1779Inputs = true := by
  rfl'

private theorem leaf1779CoversExact : CoversExact 8
    leaf1779Box leaf1779Certificate leaf1779InnerLog leaf1779Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1779RoundedFacts (by rfl)

private theorem leaf1779FlatSound : Sound leaf1779Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1779CertificateValid
    leaf1779InnerLogValid leaf1779CoversExact leaf1779LowerChecked

private noncomputable def leaf1780Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1780Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (7895168/7894981) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (727667051/536870912) }, upper := { exponent := 0, mantissa := (11243/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15790149/15789962) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1780InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1780LocalValidity :
    LeafFacts leaf1780Box leaf1780Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1780Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7895168/7894981) }) = true
      norm_num [leaf1780Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1780CertificateValid :
    WideCertificateValid leaf1780Box leaf1780Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi149ValidityFacts
    leaf1780LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1780CoverageChecked :
    coverageCheck (innerAD leaf1780Box) leaf1780InnerLog = true := by
  rfl'

private theorem leaf1780InnerLogValid :
    leaf1780InnerLog.Valid 8 (innerAD leaf1780Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1780CoverageChecked

private noncomputable def leaf1780InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1780InputLogOnePlusV_eq :
    leaf1780InputLogOnePlusV = outerEnclosure 24
      (leaf1780Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1780RoundedFacts : LeafRoundedFacts 8
    leaf1780Certificate.logOnePlusV leaf1780InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1780InputLogOnePlusV_eq }

private noncomputable def leaf1780Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1780InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1780LowerChecked :
    lowerCheck 24 leaf1780Box leaf1780Inputs = true := by
  rfl'

private theorem leaf1780CoversExact : CoversExact 8
    leaf1780Box leaf1780Certificate leaf1780InnerLog leaf1780Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1780RoundedFacts (by rfl)

private theorem leaf1780FlatSound : Sound leaf1780Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1780CertificateValid
    leaf1780InnerLogValid leaf1780CoversExact leaf1780LowerChecked

private noncomputable def leaf1781Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1781Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107325) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (729370881/536870912) }, upper := { exponent := 0, mantissa := (5635/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216253/134214650) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1781InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1781LocalValidity :
    LeafFacts leaf1781Box leaf1781Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1781Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107325) }) = true
      norm_num [leaf1781Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1781CertificateValid :
    WideCertificateValid leaf1781Box leaf1781Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi149ValidityFacts
    leaf1781LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1781CoverageChecked :
    coverageCheck (innerAD leaf1781Box) leaf1781InnerLog = true := by
  rfl'

private theorem leaf1781InnerLogValid :
    leaf1781InnerLog.Valid 8 (innerAD leaf1781Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1781CoverageChecked

private noncomputable def leaf1781InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1781InputLogOnePlusV_eq :
    leaf1781InputLogOnePlusV = outerEnclosure 24
      (leaf1781Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1781RoundedFacts : LeafRoundedFacts 8
    leaf1781Certificate.logOnePlusV leaf1781InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1781InputLogOnePlusV_eq }

private noncomputable def leaf1781Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi149InputQChi innerPair22Input
    leaf1781InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1781LowerChecked :
    lowerCheck 24 leaf1781Box leaf1781Inputs = true := by
  rfl'

private theorem leaf1781CoversExact : CoversExact 8
    leaf1781Box leaf1781Certificate leaf1781InnerLog leaf1781Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi149RoundedFacts
    innerPair22RoundedFacts leaf1781RoundedFacts (by rfl)

private theorem leaf1781FlatSound : Sound leaf1781Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1781CertificateValid
    leaf1781InnerLogValid leaf1781CoversExact leaf1781LowerChecked

private noncomputable def leaf1782Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1782Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553641) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (735006633/536870912) }, upper := { exponent := 0, mantissa := (2839/2048) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108105/67107282) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1782InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1782LocalValidity :
    LeafFacts leaf1782Box leaf1782Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1782Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553641) }) = true
      norm_num [leaf1782Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1782CertificateValid :
    WideCertificateValid leaf1782Box leaf1782Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi150ValidityFacts
    leaf1782LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1782CoverageChecked :
    coverageCheck (innerAD leaf1782Box) leaf1782InnerLog = true := by
  rfl'

private theorem leaf1782InnerLogValid :
    leaf1782InnerLog.Valid 8 (innerAD leaf1782Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1782CoverageChecked

private noncomputable def leaf1782InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1782InputLogOnePlusV_eq :
    leaf1782InputLogOnePlusV = outerEnclosure 24
      (leaf1782Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1782RoundedFacts : LeafRoundedFacts 8
    leaf1782Certificate.logOnePlusV leaf1782InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1782InputLogOnePlusV_eq }

private noncomputable def leaf1782Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi150InputQChi innerPair22Input
    leaf1782InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1782LowerChecked :
    lowerCheck 24 leaf1782Box leaf1782Inputs = true := by
  rfl'

private theorem leaf1782CoversExact : CoversExact 8
    leaf1782Box leaf1782Certificate leaf1782InnerLog leaf1782Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi150RoundedFacts
    innerPair22RoundedFacts leaf1782RoundedFacts (by rfl)

private theorem leaf1782FlatSound : Sound leaf1782Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1782CertificateValid
    leaf1782InnerLogValid leaf1782CoversExact leaf1782LowerChecked

private noncomputable def leaf1783Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1783Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776817) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (736775995/536870912) }, upper := { exponent := 0, mantissa := (1423/1024) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554049/33553634) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1783InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1783LocalValidity :
    LeafFacts leaf1783Box leaf1783Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1783Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776817) }) = true
      norm_num [leaf1783Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1783CertificateValid :
    WideCertificateValid leaf1783Box leaf1783Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi150ValidityFacts
    leaf1783LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1783CoverageChecked :
    coverageCheck (innerAD leaf1783Box) leaf1783InnerLog = true := by
  rfl'

private theorem leaf1783InnerLogValid :
    leaf1783InnerLog.Valid 8 (innerAD leaf1783Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1783CoverageChecked

private noncomputable def leaf1783InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1783InputLogOnePlusV_eq :
    leaf1783InputLogOnePlusV = outerEnclosure 24
      (leaf1783Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1783RoundedFacts : LeafRoundedFacts 8
    leaf1783Certificate.logOnePlusV leaf1783InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1783InputLogOnePlusV_eq }

private noncomputable def leaf1783Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi150InputQChi innerPair22Input
    leaf1783InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1783LowerChecked :
    lowerCheck 24 leaf1783Box leaf1783Inputs = true := by
  rfl'

private theorem leaf1783CoversExact : CoversExact 8
    leaf1783Box leaf1783Certificate leaf1783InnerLog leaf1783Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi150RoundedFacts
    innerPair22RoundedFacts leaf1783RoundedFacts (by rfl)

private theorem leaf1783FlatSound : Sound leaf1783Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1783CertificateValid
    leaf1783InnerLogValid leaf1783CoversExact leaf1783LowerChecked

private noncomputable def leaf1784Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1784Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214623) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (731074711/536870912) }, upper := { exponent := 0, mantissa := (11297/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432479/268429246) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1784InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1784LocalValidity :
    LeafFacts leaf1784Box leaf1784Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1784Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214623) }) = true
      norm_num [leaf1784Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1784CertificateValid :
    WideCertificateValid leaf1784Box leaf1784Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi149ValidityFacts
    leaf1784LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1784CoverageChecked :
    coverageCheck (innerAD leaf1784Box) leaf1784InnerLog = true := by
  rfl'

private theorem leaf1784InnerLogValid :
    leaf1784InnerLog.Valid 8 (innerAD leaf1784Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1784CoverageChecked

private noncomputable def leaf1784InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1784InputLogOnePlusV_eq :
    leaf1784InputLogOnePlusV = outerEnclosure 24
      (leaf1784Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1784RoundedFacts : LeafRoundedFacts 8
    leaf1784Certificate.logOnePlusV leaf1784InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1784InputLogOnePlusV_eq }

private noncomputable def leaf1784Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi149InputQChi innerPair22Input
    leaf1784InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1784LowerChecked :
    lowerCheck 24 leaf1784Box leaf1784Inputs = true := by
  rfl'

private theorem leaf1784CoversExact : CoversExact 8
    leaf1784Box leaf1784Certificate leaf1784InnerLog leaf1784Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi149RoundedFacts
    innerPair22RoundedFacts leaf1784RoundedFacts (by rfl)

private theorem leaf1784FlatSound : Sound leaf1784Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1784CertificateValid
    leaf1784InnerLogValid leaf1784CoversExact leaf1784LowerChecked

private noncomputable def leaf1785Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1785Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553649) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (732778541/536870912) }, upper := { exponent := 0, mantissa := (2831/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108113/67107298) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1785InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1785LocalValidity :
    LeafFacts leaf1785Box leaf1785Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1785Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553649) }) = true
      norm_num [leaf1785Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1785CertificateValid :
    WideCertificateValid leaf1785Box leaf1785Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi149ValidityFacts
    leaf1785LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1785CoverageChecked :
    coverageCheck (innerAD leaf1785Box) leaf1785InnerLog = true := by
  rfl'

private theorem leaf1785InnerLogValid :
    leaf1785InnerLog.Valid 8 (innerAD leaf1785Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1785CoverageChecked

private noncomputable def leaf1785InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1785InputLogOnePlusV_eq :
    leaf1785InputLogOnePlusV = outerEnclosure 24
      (leaf1785Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1785RoundedFacts : LeafRoundedFacts 8
    leaf1785Certificate.logOnePlusV leaf1785InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1785InputLogOnePlusV_eq }

private noncomputable def leaf1785Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi149InputQChi innerPair22Input
    leaf1785InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1785LowerChecked :
    lowerCheck 24 leaf1785Box leaf1785Inputs = true := by
  rfl'

private theorem leaf1785CoversExact : CoversExact 8
    leaf1785Box leaf1785Certificate leaf1785InnerLog leaf1785Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi149RoundedFacts
    innerPair22RoundedFacts leaf1785RoundedFacts (by rfl)

private theorem leaf1785FlatSound : Sound leaf1785Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1785CertificateValid
    leaf1785InnerLogValid leaf1785CoversExact leaf1785LowerChecked

private noncomputable def leaf1786Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1786Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553627) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (738545357/536870912) }, upper := { exponent := 0, mantissa := (2853/2048) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108091/67107254) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1786InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1786LocalValidity :
    LeafFacts leaf1786Box leaf1786Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1786Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553627) }) = true
      norm_num [leaf1786Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1786CertificateValid :
    WideCertificateValid leaf1786Box leaf1786Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi150ValidityFacts
    leaf1786LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1786CoverageChecked :
    coverageCheck (innerAD leaf1786Box) leaf1786InnerLog = true := by
  rfl'

private theorem leaf1786InnerLogValid :
    leaf1786InnerLog.Valid 8 (innerAD leaf1786Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1786CoverageChecked

private noncomputable def leaf1786InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1786InputLogOnePlusV_eq :
    leaf1786InputLogOnePlusV = outerEnclosure 24
      (leaf1786Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1786RoundedFacts : LeafRoundedFacts 8
    leaf1786Certificate.logOnePlusV leaf1786InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1786InputLogOnePlusV_eq }

private noncomputable def leaf1786Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1786InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1786LowerChecked :
    lowerCheck 24 leaf1786Box leaf1786Inputs = true := by
  rfl'

private theorem leaf1786CoversExact : CoversExact 8
    leaf1786Box leaf1786Certificate leaf1786InnerLog leaf1786Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1786RoundedFacts (by rfl)

private theorem leaf1786FlatSound : Sound leaf1786Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1786CertificateValid
    leaf1786InnerLogValid leaf1786CoversExact leaf1786LowerChecked

private noncomputable def leaf1787Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1787Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388405) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (740314719/536870912) }, upper := { exponent := 0, mantissa := (715/512) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777021/16776810) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1787InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1787LocalValidity :
    LeafFacts leaf1787Box leaf1787Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1787Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388405) }) = true
      norm_num [leaf1787Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1787CertificateValid :
    WideCertificateValid leaf1787Box leaf1787Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi150ValidityFacts
    leaf1787LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1787CoverageChecked :
    coverageCheck (innerAD leaf1787Box) leaf1787InnerLog = true := by
  rfl'

private theorem leaf1787InnerLogValid :
    leaf1787InnerLog.Valid 8 (innerAD leaf1787Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1787CoverageChecked

private noncomputable def leaf1787InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1787InputLogOnePlusV_eq :
    leaf1787InputLogOnePlusV = outerEnclosure 24
      (leaf1787Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1787RoundedFacts : LeafRoundedFacts 8
    leaf1787Certificate.logOnePlusV leaf1787InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1787InputLogOnePlusV_eq }

private noncomputable def leaf1787Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1787InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1787LowerChecked :
    lowerCheck 24 leaf1787Box leaf1787Inputs = true := by
  rfl'

private theorem leaf1787CoversExact : CoversExact 8
    leaf1787Box leaf1787Certificate leaf1787InnerLog leaf1787Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1787RoundedFacts (by rfl)

private theorem leaf1787FlatSound : Sound leaf1787Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1787CertificateValid
    leaf1787InnerLogValid leaf1787CoversExact leaf1787LowerChecked

private noncomputable def leaf1788Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1788Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214451) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (742346215/536870912) }, upper := { exponent := 0, mantissa := (11469/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432307/268428902) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1788InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1788LocalValidity :
    LeafFacts leaf1788Box leaf1788Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1788Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214451) }) = true
      norm_num [leaf1788Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1788CertificateValid :
    WideCertificateValid leaf1788Box leaf1788Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi155ValidityFacts
    leaf1788LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1788CoverageChecked :
    coverageCheck (innerAD leaf1788Box) leaf1788InnerLog = true := by
  rfl'

private theorem leaf1788InnerLogValid :
    leaf1788InnerLog.Valid 8 (innerAD leaf1788Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1788CoverageChecked

private noncomputable def leaf1788InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1788InputLogOnePlusV_eq :
    leaf1788InputLogOnePlusV = outerEnclosure 24
      (leaf1788Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1788RoundedFacts : LeafRoundedFacts 8
    leaf1788Certificate.logOnePlusV leaf1788InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1788InputLogOnePlusV_eq }

private noncomputable def leaf1788Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1788InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1788LowerChecked :
    lowerCheck 24 leaf1788Box leaf1788Inputs = true := by
  rfl'

private theorem leaf1788CoversExact : CoversExact 8
    leaf1788Box leaf1788Certificate leaf1788InnerLog leaf1788Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1788RoundedFacts (by rfl)

private theorem leaf1788FlatSound : Sound leaf1788Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1788CertificateValid
    leaf1788InnerLogValid leaf1788CoversExact leaf1788LowerChecked

private noncomputable def leaf1789Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1789Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (3947584/3947483) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (744181109/536870912) }, upper := { exponent := 0, mantissa := (5749/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (7895067/7894966) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1789InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1789LocalValidity :
    LeafFacts leaf1789Box leaf1789Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1789Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3947584/3947483) }) = true
      norm_num [leaf1789Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1789CertificateValid :
    WideCertificateValid leaf1789Box leaf1789Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi155ValidityFacts
    leaf1789LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1789CoverageChecked :
    coverageCheck (innerAD leaf1789Box) leaf1789InnerLog = true := by
  rfl'

private theorem leaf1789InnerLogValid :
    leaf1789InnerLog.Valid 8 (innerAD leaf1789Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1789CoverageChecked

private noncomputable def leaf1789InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1789InputLogOnePlusV_eq :
    leaf1789InputLogOnePlusV = outerEnclosure 24
      (leaf1789Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1789RoundedFacts : LeafRoundedFacts 8
    leaf1789Certificate.logOnePlusV leaf1789InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1789InputLogOnePlusV_eq }

private noncomputable def leaf1789Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1789InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1789LowerChecked :
    lowerCheck 24 leaf1789Box leaf1789Inputs = true := by
  rfl'

private theorem leaf1789CoversExact : CoversExact 8
    leaf1789Box leaf1789Certificate leaf1789InnerLog leaf1789Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1789RoundedFacts (by rfl)

private theorem leaf1789FlatSound : Sound leaf1789Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1789CertificateValid
    leaf1789InnerLogValid leaf1789CoversExact leaf1789LowerChecked

private noncomputable def leaf1790Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1790Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107169) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (749685797/536870912) }, upper := { exponent := 0, mantissa := (5791/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216097/134214338) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1790InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1790LocalValidity :
    LeafFacts leaf1790Box leaf1790Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1790Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107169) }) = true
      norm_num [leaf1790Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1790CertificateValid :
    WideCertificateValid leaf1790Box leaf1790Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi156ValidityFacts
    leaf1790LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1790CoverageChecked :
    coverageCheck (innerAD leaf1790Box) leaf1790InnerLog = true := by
  rfl'

private theorem leaf1790InnerLogValid :
    leaf1790InnerLog.Valid 8 (innerAD leaf1790Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1790CoverageChecked

private noncomputable def leaf1790InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1790InputLogOnePlusV_eq :
    leaf1790InputLogOnePlusV = outerEnclosure 24
      (leaf1790Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1790RoundedFacts : LeafRoundedFacts 8
    leaf1790Certificate.logOnePlusV leaf1790InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1790InputLogOnePlusV_eq }

private noncomputable def leaf1790Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1790InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1790LowerChecked :
    lowerCheck 24 leaf1790Box leaf1790Inputs = true := by
  rfl'

private theorem leaf1790CoversExact : CoversExact 8
    leaf1790Box leaf1790Certificate leaf1790InnerLog leaf1790Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1790RoundedFacts (by rfl)

private theorem leaf1790FlatSound : Sound leaf1790Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1790CertificateValid
    leaf1790InnerLogValid leaf1790CoversExact leaf1790LowerChecked

private noncomputable def leaf1791Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1791Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553577) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (751586223/536870912) }, upper := { exponent := 0, mantissa := (2903/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108041/67107154) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1791InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1791LocalValidity :
    LeafFacts leaf1791Box leaf1791Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1791Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553577) }) = true
      norm_num [leaf1791Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1791CertificateValid :
    WideCertificateValid leaf1791Box leaf1791Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi156ValidityFacts
    leaf1791LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1791CoverageChecked :
    coverageCheck (innerAD leaf1791Box) leaf1791InnerLog = true := by
  rfl'

private theorem leaf1791InnerLogValid :
    leaf1791InnerLog.Valid 8 (innerAD leaf1791Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1791CoverageChecked

private noncomputable def leaf1791InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1791InputLogOnePlusV_eq :
    leaf1791InputLogOnePlusV = outerEnclosure 24
      (leaf1791Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1791RoundedFacts : LeafRoundedFacts 8
    leaf1791Certificate.logOnePlusV leaf1791InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1791InputLogOnePlusV_eq }

private noncomputable def leaf1791Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1791InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1791LowerChecked :
    lowerCheck 24 leaf1791Box leaf1791Inputs = true := by
  rfl'

private theorem leaf1791CoversExact : CoversExact 8
    leaf1791Box leaf1791Certificate leaf1791InnerLog leaf1791Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1791RoundedFacts (by rfl)

private theorem leaf1791FlatSound : Sound leaf1791Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1791CertificateValid
    leaf1791InnerLogValid leaf1791CoversExact leaf1791LowerChecked

private noncomputable def leaf1792Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1792Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214225) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (757025379/536870912) }, upper := { exponent := 0, mantissa := (11695/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432081/268428450) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1792InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1792LocalValidity :
    LeafFacts leaf1792Box leaf1792Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1792Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214225) }) = true
      norm_num [leaf1792Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1792CertificateValid :
    WideCertificateValid leaf1792Box leaf1792Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi153ValidityFacts
    leaf1792LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1792CoverageChecked :
    coverageCheck (innerAD leaf1792Box) leaf1792InnerLog = true := by
  rfl'

private theorem leaf1792InnerLogValid :
    leaf1792InnerLog.Valid 8 (innerAD leaf1792Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1792CoverageChecked

private noncomputable def leaf1792InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1792InputLogOnePlusV_eq :
    leaf1792InputLogOnePlusV = outerEnclosure 24
      (leaf1792Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1792RoundedFacts : LeafRoundedFacts 8
    leaf1792Certificate.logOnePlusV leaf1792InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1792InputLogOnePlusV_eq }

private noncomputable def leaf1792Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1792InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1792LowerChecked :
    lowerCheck 24 leaf1792Box leaf1792Inputs = true := by
  rfl'

private theorem leaf1792CoversExact : CoversExact 8
    leaf1792Box leaf1792Certificate leaf1792InnerLog leaf1792Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1792RoundedFacts (by rfl)

private theorem leaf1792FlatSound : Sound leaf1792Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1792CertificateValid
    leaf1792InnerLogValid leaf1792CoversExact leaf1792LowerChecked

private noncomputable def leaf1793Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1793Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194191) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (764364961/536870912) }, upper := { exponent := 0, mantissa := (369/256) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388499/8388382) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1793InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1793LocalValidity :
    LeafFacts leaf1793Box leaf1793Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1793Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194191) }) = true
      norm_num [leaf1793Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1793CertificateValid :
    WideCertificateValid leaf1793Box leaf1793Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi154ValidityFacts
    leaf1793LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1793CoverageChecked :
    coverageCheck (innerAD leaf1793Box) leaf1793InnerLog = true := by
  rfl'

private theorem leaf1793InnerLogValid :
    leaf1793InnerLog.Valid 8 (innerAD leaf1793Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1793CoverageChecked

private noncomputable def leaf1793InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1793InputLogOnePlusV_eq :
    leaf1793InputLogOnePlusV = outerEnclosure 24
      (leaf1793Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1793RoundedFacts : LeafRoundedFacts 8
    leaf1793Certificate.logOnePlusV leaf1793InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1793InputLogOnePlusV_eq }

private noncomputable def leaf1793Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi154InputQChi innerPair405Input
    leaf1793InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1793LowerChecked :
    lowerCheck 24 leaf1793Box leaf1793Inputs = true := by
  rfl'

private theorem leaf1793CoversExact : CoversExact 8
    leaf1793Box leaf1793Certificate leaf1793InnerLog leaf1793Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi154RoundedFacts
    innerPair405RoundedFacts leaf1793RoundedFacts (by rfl)

private theorem leaf1793FlatSound : Sound leaf1793Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1793CertificateValid
    leaf1793InnerLogValid leaf1793CoversExact leaf1793LowerChecked

private noncomputable def leaf1794Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1794Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (758991337/536870912) }, upper := { exponent := 0, mantissa := (5863/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216025/134214194) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1794InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1794LocalValidity :
    LeafFacts leaf1794Box leaf1794Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1794Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107097) }) = true
      norm_num [leaf1794Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1794CertificateValid :
    WideCertificateValid leaf1794Box leaf1794Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi153ValidityFacts
    leaf1794LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1794CoverageChecked :
    coverageCheck (innerAD leaf1794Box) leaf1794InnerLog = true := by
  rfl'

private theorem leaf1794InnerLogValid :
    leaf1794InnerLog.Valid 8 (innerAD leaf1794Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1794CoverageChecked

private noncomputable def leaf1794InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1794InputLogOnePlusV_eq :
    leaf1794InputLogOnePlusV = outerEnclosure 24
      (leaf1794Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1794RoundedFacts : LeafRoundedFacts 8
    leaf1794Certificate.logOnePlusV leaf1794InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1794InputLogOnePlusV_eq }

private noncomputable def leaf1794Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1794InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1794LowerChecked :
    lowerCheck 24 leaf1794Box leaf1794Inputs = true := by
  rfl'

private theorem leaf1794CoversExact : CoversExact 8
    leaf1794Box leaf1794Certificate leaf1794InnerLog leaf1794Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1794RoundedFacts (by rfl)

private theorem leaf1794FlatSound : Sound leaf1794Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1794CertificateValid
    leaf1794InnerLogValid leaf1794CoversExact leaf1794LowerChecked

private noncomputable def leaf1795Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1795Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (2097154/2097095) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (766396451/536870912) }, upper := { exponent := 0, mantissa := (185/128) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4194249/4194190) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1795InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1795LocalValidity :
    LeafFacts leaf1795Box leaf1795Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1795Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2097154/2097095) }) = true
      norm_num [leaf1795Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1795CertificateValid :
    WideCertificateValid leaf1795Box leaf1795Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi154ValidityFacts
    leaf1795LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1795CoverageChecked :
    coverageCheck (innerAD leaf1795Box) leaf1795InnerLog = true := by
  rfl'

private theorem leaf1795InnerLogValid :
    leaf1795InnerLog.Valid 8 (innerAD leaf1795Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1795CoverageChecked

private noncomputable def leaf1795InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1795InputLogOnePlusV_eq :
    leaf1795InputLogOnePlusV = outerEnclosure 24
      (leaf1795Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1795RoundedFacts : LeafRoundedFacts 8
    leaf1795Certificate.logOnePlusV leaf1795InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1795InputLogOnePlusV_eq }

private noncomputable def leaf1795Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi154InputQChi innerPair405Input
    leaf1795InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1795LowerChecked :
    lowerCheck 24 leaf1795Box leaf1795Inputs = true := by
  rfl'

private theorem leaf1795CoversExact : CoversExact 8
    leaf1795Box leaf1795Certificate leaf1795InnerLog leaf1795Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi154RoundedFacts
    innerPair405RoundedFacts leaf1795RoundedFacts (by rfl)

private theorem leaf1795FlatSound : Sound leaf1795Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1795CertificateValid
    leaf1795InnerLogValid leaf1795CoversExact leaf1795LowerChecked

private noncomputable def leaf1796Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1796Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214393) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (746016003/536870912) }, upper := { exponent := 0, mantissa := (11527/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432249/268428786) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1796InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1796LocalValidity :
    LeafFacts leaf1796Box leaf1796Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1796Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214393) }) = true
      norm_num [leaf1796Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1796CertificateValid :
    WideCertificateValid leaf1796Box leaf1796Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi155ValidityFacts
    leaf1796LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1796CoverageChecked :
    coverageCheck (innerAD leaf1796Box) leaf1796InnerLog = true := by
  rfl'

private theorem leaf1796InnerLogValid :
    leaf1796InnerLog.Valid 8 (innerAD leaf1796Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1796CoverageChecked

private noncomputable def leaf1796InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1796InputLogOnePlusV_eq :
    leaf1796InputLogOnePlusV = outerEnclosure 24
      (leaf1796Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1796RoundedFacts : LeafRoundedFacts 8
    leaf1796Certificate.logOnePlusV leaf1796InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1796InputLogOnePlusV_eq }

private noncomputable def leaf1796Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1796InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1796LowerChecked :
    lowerCheck 24 leaf1796Box leaf1796Inputs = true := by
  rfl'

private theorem leaf1796CoversExact : CoversExact 8
    leaf1796Box leaf1796Certificate leaf1796InnerLog leaf1796Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1796RoundedFacts (by rfl)

private theorem leaf1796FlatSound : Sound leaf1796Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1796CertificateValid
    leaf1796InnerLogValid leaf1796CoversExact leaf1796LowerChecked

private noncomputable def leaf1797Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1797Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553591) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (747850897/536870912) }, upper := { exponent := 0, mantissa := (2889/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108055/67107182) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1797InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1797LocalValidity :
    LeafFacts leaf1797Box leaf1797Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1797Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553591) }) = true
      norm_num [leaf1797Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1797CertificateValid :
    WideCertificateValid leaf1797Box leaf1797Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi155ValidityFacts
    leaf1797LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1797CoverageChecked :
    coverageCheck (innerAD leaf1797Box) leaf1797InnerLog = true := by
  rfl'

private theorem leaf1797InnerLogValid :
    leaf1797InnerLog.Valid 8 (innerAD leaf1797Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1797CoverageChecked

private noncomputable def leaf1797InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1797InputLogOnePlusV_eq :
    leaf1797InputLogOnePlusV = outerEnclosure 24
      (leaf1797Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1797RoundedFacts : LeafRoundedFacts 8
    leaf1797Certificate.logOnePlusV leaf1797InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1797InputLogOnePlusV_eq }

private noncomputable def leaf1797Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1797InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1797LowerChecked :
    lowerCheck 24 leaf1797Box leaf1797Inputs = true := by
  rfl'

private theorem leaf1797CoversExact : CoversExact 8
    leaf1797Box leaf1797Certificate leaf1797InnerLog leaf1797Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1797RoundedFacts (by rfl)

private theorem leaf1797FlatSound : Sound leaf1797Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1797CertificateValid
    leaf1797InnerLogValid leaf1797CoversExact leaf1797LowerChecked

private noncomputable def leaf1798Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1798Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107139) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (753486649/536870912) }, upper := { exponent := 0, mantissa := (5821/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216067/134214278) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1798InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1798LocalValidity :
    LeafFacts leaf1798Box leaf1798Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1798Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107139) }) = true
      norm_num [leaf1798Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1798CertificateValid :
    WideCertificateValid leaf1798Box leaf1798Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi156ValidityFacts
    leaf1798LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1798CoverageChecked :
    coverageCheck (innerAD leaf1798Box) leaf1798InnerLog = true := by
  rfl'

private theorem leaf1798InnerLogValid :
    leaf1798InnerLog.Valid 8 (innerAD leaf1798Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1798CoverageChecked

private noncomputable def leaf1798InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1798InputLogOnePlusV_eq :
    leaf1798InputLogOnePlusV = outerEnclosure 24
      (leaf1798Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1798RoundedFacts : LeafRoundedFacts 8
    leaf1798Certificate.logOnePlusV leaf1798InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1798InputLogOnePlusV_eq }

private noncomputable def leaf1798Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1798InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1798LowerChecked :
    lowerCheck 24 leaf1798Box leaf1798Inputs = true := by
  rfl'

private theorem leaf1798CoversExact : CoversExact 8
    leaf1798Box leaf1798Certificate leaf1798InnerLog leaf1798Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1798RoundedFacts (by rfl)

private theorem leaf1798FlatSound : Sound leaf1798Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1798CertificateValid
    leaf1798InnerLogValid leaf1798CoversExact leaf1798LowerChecked

private noncomputable def leaf1799Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1799Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776781) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (755387075/536870912) }, upper := { exponent := 0, mantissa := (1459/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554013/33553562) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1799InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1799LocalValidity :
    LeafFacts leaf1799Box leaf1799Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1799Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776781) }) = true
      norm_num [leaf1799Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1799CertificateValid :
    WideCertificateValid leaf1799Box leaf1799Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi156ValidityFacts
    leaf1799LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1799CoverageChecked :
    coverageCheck (innerAD leaf1799Box) leaf1799InnerLog = true := by
  rfl'

private theorem leaf1799InnerLogValid :
    leaf1799InnerLog.Valid 8 (innerAD leaf1799Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1799CoverageChecked

private noncomputable def leaf1799InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1799InputLogOnePlusV_eq :
    leaf1799InputLogOnePlusV = outerEnclosure 24
      (leaf1799Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1799RoundedFacts : LeafRoundedFacts 8
    leaf1799Certificate.logOnePlusV leaf1799InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1799InputLogOnePlusV_eq }

private noncomputable def leaf1799Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1799InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1799LowerChecked :
    lowerCheck 24 leaf1799Box leaf1799Inputs = true := by
  rfl'

private theorem leaf1799CoversExact : CoversExact 8
    leaf1799Box leaf1799Certificate leaf1799InnerLog leaf1799Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1799RoundedFacts (by rfl)

private theorem leaf1799FlatSound : Sound leaf1799Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1799CertificateValid
    leaf1799InnerLogValid leaf1799CoversExact leaf1799LowerChecked

private noncomputable def leaf1800Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1800Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214163) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (760957295/536870912) }, upper := { exponent := 0, mantissa := (11757/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432019/268428326) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1800InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1800LocalValidity :
    LeafFacts leaf1800Box leaf1800Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1800Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214163) }) = true
      norm_num [leaf1800Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1800CertificateValid :
    WideCertificateValid leaf1800Box leaf1800Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi153ValidityFacts
    leaf1800LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1800CoverageChecked :
    coverageCheck (innerAD leaf1800Box) leaf1800InnerLog = true := by
  rfl'

private theorem leaf1800InnerLogValid :
    leaf1800InnerLog.Valid 8 (innerAD leaf1800Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1800CoverageChecked

private noncomputable def leaf1800InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf1800InputLogOnePlusV_eq :
    leaf1800InputLogOnePlusV = outerEnclosure 24
      (leaf1800Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1800RoundedFacts : LeafRoundedFacts 8
    leaf1800Certificate.logOnePlusV leaf1800InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1800InputLogOnePlusV_eq }

private noncomputable def leaf1800Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1800InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1800LowerChecked :
    lowerCheck 24 leaf1800Box leaf1800Inputs = true := by
  rfl'

private theorem leaf1800CoversExact : CoversExact 8
    leaf1800Box leaf1800Certificate leaf1800InnerLog leaf1800Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1800RoundedFacts (by rfl)

private theorem leaf1800FlatSound : Sound leaf1800Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1800CertificateValid
    leaf1800InnerLogValid leaf1800CoversExact leaf1800LowerChecked

private noncomputable def leaf1801Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1801Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553533) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (762923253/536870912) }, upper := { exponent := 0, mantissa := (2947/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107997/67107066) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1801InnerLog : WideLogData :=
  innerPair144Data

set_option maxRecDepth 1000000 in
private theorem leaf1801LocalValidity :
    LeafFacts leaf1801Box leaf1801Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1801Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553533) }) = true
      norm_num [leaf1801Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1801CertificateValid :
    WideCertificateValid leaf1801Box leaf1801Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi153ValidityFacts
    leaf1801LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1801CoverageChecked :
    coverageCheck (innerAD leaf1801Box) leaf1801InnerLog = true := by
  rfl'

private theorem leaf1801InnerLogValid :
    leaf1801InnerLog.Valid 8 (innerAD leaf1801Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint41PositiveFacts.valid leaf1801CoverageChecked

private noncomputable def leaf1801InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1801InputLogOnePlusV_eq :
    leaf1801InputLogOnePlusV = outerEnclosure 24
      (leaf1801Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1801RoundedFacts : LeafRoundedFacts 8
    leaf1801Certificate.logOnePlusV leaf1801InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1801InputLogOnePlusV_eq }

private noncomputable def leaf1801Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi153InputQChi innerPair144Input
    leaf1801InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1801LowerChecked :
    lowerCheck 24 leaf1801Box leaf1801Inputs = true := by
  rfl'

private theorem leaf1801CoversExact : CoversExact 8
    leaf1801Box leaf1801Certificate leaf1801InnerLog leaf1801Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi153RoundedFacts
    innerPair144RoundedFacts leaf1801RoundedFacts (by rfl)

private theorem leaf1801FlatSound : Sound leaf1801Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1801CertificateValid
    leaf1801InnerLogValid leaf1801CoversExact leaf1801LowerChecked

private noncomputable def leaf1802Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1802Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (246724/246717) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (768427941/536870912) }, upper := { exponent := 0, mantissa := (371/256) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (493441/493434) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1802InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1802LocalValidity :
    LeafFacts leaf1802Box leaf1802Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1802Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (246724/246717) }) = true
      norm_num [leaf1802Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1802CertificateValid :
    WideCertificateValid leaf1802Box leaf1802Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi154ValidityFacts
    leaf1802LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1802CoverageChecked :
    coverageCheck (innerAD leaf1802Box) leaf1802InnerLog = true := by
  rfl'

private theorem leaf1802InnerLogValid :
    leaf1802InnerLog.Valid 8 (innerAD leaf1802Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1802CoverageChecked

private noncomputable def leaf1802InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1802InputLogOnePlusV_eq :
    leaf1802InputLogOnePlusV = outerEnclosure 24
      (leaf1802Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1802RoundedFacts : LeafRoundedFacts 8
    leaf1802Certificate.logOnePlusV leaf1802InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1802InputLogOnePlusV_eq }

private noncomputable def leaf1802Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi154InputQChi innerPair405Input
    leaf1802InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1802LowerChecked :
    lowerCheck 24 leaf1802Box leaf1802Inputs = true := by
  rfl'

private theorem leaf1802CoversExact : CoversExact 8
    leaf1802Box leaf1802Certificate leaf1802InnerLog leaf1802Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi154RoundedFacts
    innerPair405RoundedFacts leaf1802RoundedFacts (by rfl)

private theorem leaf1802FlatSound : Sound leaf1802Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1802CertificateValid
    leaf1802InnerLogValid leaf1802CoversExact leaf1802LowerChecked

private noncomputable def leaf1803Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1803Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (1048577/1048547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (770459431/536870912) }, upper := { exponent := 0, mantissa := (93/64) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1048562/1048547) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1803InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1803LocalValidity :
    LeafFacts leaf1803Box leaf1803Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1803Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1048577/1048547) }) = true
      norm_num [leaf1803Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1803CertificateValid :
    WideCertificateValid leaf1803Box leaf1803Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi154ValidityFacts
    leaf1803LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1803CoverageChecked :
    coverageCheck (innerAD leaf1803Box) leaf1803InnerLog = true := by
  rfl'

private theorem leaf1803InnerLogValid :
    leaf1803InnerLog.Valid 8 (innerAD leaf1803Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1803CoverageChecked

private noncomputable def leaf1803InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1803InputLogOnePlusV_eq :
    leaf1803InputLogOnePlusV = outerEnclosure 24
      (leaf1803Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1803RoundedFacts : LeafRoundedFacts 8
    leaf1803Certificate.logOnePlusV leaf1803InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1803InputLogOnePlusV_eq }

private noncomputable def leaf1803Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi154InputQChi innerPair405Input
    leaf1803InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1803LowerChecked :
    lowerCheck 24 leaf1803Box leaf1803Inputs = true := by
  rfl'

private theorem leaf1803CoversExact : CoversExact 8
    leaf1803Box leaf1803Certificate leaf1803InnerLog leaf1803Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi154RoundedFacts
    innerPair405RoundedFacts leaf1803RoundedFacts (by rfl)

private theorem leaf1803FlatSound : Sound leaf1803Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1803CertificateValid
    leaf1803InnerLogValid leaf1803CoversExact leaf1803LowerChecked

private noncomputable def leaf1804Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1804Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214803) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (719278951/536870912) }, upper := { exponent := 0, mantissa := (11117/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432659/268429606) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1804InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1804LocalValidity :
    LeafFacts leaf1804Box leaf1804Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1804Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214803) }) = true
      norm_num [leaf1804Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1804CertificateValid :
    WideCertificateValid leaf1804Box leaf1804Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi131ValidityFacts
    leaf1804LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1804CoverageChecked :
    coverageCheck (innerAD leaf1804Box) leaf1804InnerLog = true := by
  rfl'

private theorem leaf1804InnerLogValid :
    leaf1804InnerLog.Valid 8 (innerAD leaf1804Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1804CoverageChecked

private noncomputable def leaf1804InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1804InputLogOnePlusV_eq :
    leaf1804InputLogOnePlusV = outerEnclosure 24
      (leaf1804Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1804RoundedFacts : LeafRoundedFacts 8
    leaf1804Certificate.logOnePlusV leaf1804InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1804InputLogOnePlusV_eq }

private noncomputable def leaf1804Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1804InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1804LowerChecked :
    lowerCheck 24 leaf1804Box leaf1804Inputs = true := by
  rfl'

private theorem leaf1804CoversExact : CoversExact 8
    leaf1804Box leaf1804Certificate leaf1804InnerLog leaf1804Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1804RoundedFacts (by rfl)

private theorem leaf1804FlatSound : Sound leaf1804Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1804CertificateValid
    leaf1804InnerLogValid leaf1804CoversExact leaf1804LowerChecked

private noncomputable def leaf1805Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1805Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107389) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (720851717/536870912) }, upper := { exponent := 0, mantissa := (5571/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216317/134214778) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1805InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1805LocalValidity :
    LeafFacts leaf1805Box leaf1805Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1805Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107389) }) = true
      norm_num [leaf1805Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1805CertificateValid :
    WideCertificateValid leaf1805Box leaf1805Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi131ValidityFacts
    leaf1805LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1805CoverageChecked :
    coverageCheck (innerAD leaf1805Box) leaf1805InnerLog = true := by
  rfl'

private theorem leaf1805InnerLogValid :
    leaf1805InnerLog.Valid 8 (innerAD leaf1805Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1805CoverageChecked

private noncomputable def leaf1805InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1805InputLogOnePlusV_eq :
    leaf1805InputLogOnePlusV = outerEnclosure 24
      (leaf1805Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1805RoundedFacts : LeafRoundedFacts 8
    leaf1805Certificate.logOnePlusV leaf1805InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1805InputLogOnePlusV_eq }

private noncomputable def leaf1805Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1805InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1805LowerChecked :
    lowerCheck 24 leaf1805Box leaf1805Inputs = true := by
  rfl'

private theorem leaf1805CoversExact : CoversExact 8
    leaf1805Box leaf1805Certificate leaf1805InnerLog leaf1805Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1805RoundedFacts (by rfl)

private theorem leaf1805FlatSound : Sound leaf1805Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1805CertificateValid
    leaf1805InnerLogValid leaf1805CoversExact leaf1805LowerChecked

private noncomputable def leaf1806Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1806Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107343) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (726880661/536870912) }, upper := { exponent := 0, mantissa := (5617/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216271/134214686) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1806InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1806LocalValidity :
    LeafFacts leaf1806Box leaf1806Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1806Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107343) }) = true
      norm_num [leaf1806Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1806CertificateValid :
    WideCertificateValid leaf1806Box leaf1806Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi132ValidityFacts
    leaf1806LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1806CoverageChecked :
    coverageCheck (innerAD leaf1806Box) leaf1806InnerLog = true := by
  rfl'

private theorem leaf1806InnerLogValid :
    leaf1806InnerLog.Valid 8 (innerAD leaf1806Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1806CoverageChecked

private noncomputable def leaf1806InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1806InputLogOnePlusV_eq :
    leaf1806InputLogOnePlusV = outerEnclosure 24
      (leaf1806Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1806RoundedFacts : LeafRoundedFacts 8
    leaf1806Certificate.logOnePlusV leaf1806InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1806InputLogOnePlusV_eq }

private noncomputable def leaf1806Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1806InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1806LowerChecked :
    lowerCheck 24 leaf1806Box leaf1806Inputs = true := by
  rfl'

private theorem leaf1806CoversExact : CoversExact 8
    leaf1806Box leaf1806Certificate leaf1806InnerLog leaf1806Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1806RoundedFacts (by rfl)

private theorem leaf1806FlatSound : Sound leaf1806Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1806CertificateValid
    leaf1806InnerLogValid leaf1806CoversExact leaf1806LowerChecked

private noncomputable def leaf1807Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1807Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (1973792/1973745) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (728518959/536870912) }, upper := { exponent := 0, mantissa := (2815/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3947537/3947490) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1807InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1807LocalValidity :
    LeafFacts leaf1807Box leaf1807Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1807Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1973792/1973745) }) = true
      norm_num [leaf1807Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1807CertificateValid :
    WideCertificateValid leaf1807Box leaf1807Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi132ValidityFacts
    leaf1807LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1807CoverageChecked :
    coverageCheck (innerAD leaf1807Box) leaf1807InnerLog = true := by
  rfl'

private theorem leaf1807InnerLogValid :
    leaf1807InnerLog.Valid 8 (innerAD leaf1807Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1807CoverageChecked

private noncomputable def leaf1807InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1807InputLogOnePlusV_eq :
    leaf1807InputLogOnePlusV = outerEnclosure 24
      (leaf1807Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1807RoundedFacts : LeafRoundedFacts 8
    leaf1807Certificate.logOnePlusV leaf1807InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1807InputLogOnePlusV_eq }

private noncomputable def leaf1807Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1807InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1807LowerChecked :
    lowerCheck 24 leaf1807Box leaf1807Inputs = true := by
  rfl'

private theorem leaf1807CoversExact : CoversExact 8
    leaf1807Box leaf1807Certificate leaf1807InnerLog leaf1807Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1807RoundedFacts (by rfl)

private theorem leaf1807FlatSound : Sound leaf1807Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1807CertificateValid
    leaf1807InnerLogValid leaf1807CoversExact leaf1807LowerChecked

private noncomputable def leaf1808Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1808Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214753) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (722424483/536870912) }, upper := { exponent := 0, mantissa := (11167/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432609/268429506) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1808InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1808LocalValidity :
    LeafFacts leaf1808Box leaf1808Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1808Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214753) }) = true
      norm_num [leaf1808Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1808CertificateValid :
    WideCertificateValid leaf1808Box leaf1808Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi131ValidityFacts
    leaf1808LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1808CoverageChecked :
    coverageCheck (innerAD leaf1808Box) leaf1808InnerLog = true := by
  rfl'

private theorem leaf1808InnerLogValid :
    leaf1808InnerLog.Valid 8 (innerAD leaf1808Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1808CoverageChecked

private noncomputable def leaf1808InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1808InputLogOnePlusV_eq :
    leaf1808InputLogOnePlusV = outerEnclosure 24
      (leaf1808Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1808RoundedFacts : LeafRoundedFacts 8
    leaf1808Certificate.logOnePlusV leaf1808InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1808InputLogOnePlusV_eq }

private noncomputable def leaf1808Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1808InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1808LowerChecked :
    lowerCheck 24 leaf1808Box leaf1808Inputs = true := by
  rfl'

private theorem leaf1808CoversExact : CoversExact 8
    leaf1808Box leaf1808Certificate leaf1808InnerLog leaf1808Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1808RoundedFacts (by rfl)

private theorem leaf1808FlatSound : Sound leaf1808Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1808CertificateValid
    leaf1808InnerLogValid leaf1808CoversExact leaf1808LowerChecked

private noncomputable def leaf1809Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1809Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (986896/986873) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (723997249/536870912) }, upper := { exponent := 0, mantissa := (1399/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1973769/1973746) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1809InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1809LocalValidity :
    LeafFacts leaf1809Box leaf1809Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1809Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (986896/986873) }) = true
      norm_num [leaf1809Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1809CertificateValid :
    WideCertificateValid leaf1809Box leaf1809Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi131ValidityFacts
    leaf1809LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1809CoverageChecked :
    coverageCheck (innerAD leaf1809Box) leaf1809InnerLog = true := by
  rfl'

private theorem leaf1809InnerLogValid :
    leaf1809InnerLog.Valid 8 (innerAD leaf1809Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1809CoverageChecked

private noncomputable def leaf1809InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1809InputLogOnePlusV_eq :
    leaf1809InputLogOnePlusV = outerEnclosure 24
      (leaf1809Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1809RoundedFacts : LeafRoundedFacts 8
    leaf1809Certificate.logOnePlusV leaf1809InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1809InputLogOnePlusV_eq }

private noncomputable def leaf1809Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1809InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1809LowerChecked :
    lowerCheck 24 leaf1809Box leaf1809Inputs = true := by
  rfl'

private theorem leaf1809CoversExact : CoversExact 8
    leaf1809Box leaf1809Certificate leaf1809InnerLog leaf1809Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1809RoundedFacts (by rfl)

private theorem leaf1809FlatSound : Sound leaf1809Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1809CertificateValid
    leaf1809InnerLogValid leaf1809CoversExact leaf1809LowerChecked

private noncomputable def leaf1810Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1810Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107317) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (730157257/536870912) }, upper := { exponent := 0, mantissa := (5643/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216245/134214634) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1810InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1810LocalValidity :
    LeafFacts leaf1810Box leaf1810Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1810Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107317) }) = true
      norm_num [leaf1810Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1810CertificateValid :
    WideCertificateValid leaf1810Box leaf1810Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi132ValidityFacts
    leaf1810LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1810CoverageChecked :
    coverageCheck (innerAD leaf1810Box) leaf1810InnerLog = true := by
  rfl'

private theorem leaf1810InnerLogValid :
    leaf1810InnerLog.Valid 8 (innerAD leaf1810Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1810CoverageChecked

private noncomputable def leaf1810InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1810InputLogOnePlusV_eq :
    leaf1810InputLogOnePlusV = outerEnclosure 24
      (leaf1810Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1810RoundedFacts : LeafRoundedFacts 8
    leaf1810Certificate.logOnePlusV leaf1810InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1810InputLogOnePlusV_eq }

private noncomputable def leaf1810Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi132InputQChi innerPair22Input
    leaf1810InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1810LowerChecked :
    lowerCheck 24 leaf1810Box leaf1810Inputs = true := by
  rfl'

private theorem leaf1810CoversExact : CoversExact 8
    leaf1810Box leaf1810Certificate leaf1810InnerLog leaf1810Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi132RoundedFacts
    innerPair22RoundedFacts leaf1810RoundedFacts (by rfl)

private theorem leaf1810FlatSound : Sound leaf1810Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1810CertificateValid
    leaf1810InnerLogValid leaf1810CoversExact leaf1810LowerChecked

private noncomputable def leaf1811Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1811Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388413) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (731795555/536870912) }, upper := { exponent := 0, mantissa := (707/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777029/16776826) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1811InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1811LocalValidity :
    LeafFacts leaf1811Box leaf1811Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1811Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388413) }) = true
      norm_num [leaf1811Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1811CertificateValid :
    WideCertificateValid leaf1811Box leaf1811Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi132ValidityFacts
    leaf1811LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1811CoverageChecked :
    coverageCheck (innerAD leaf1811Box) leaf1811InnerLog = true := by
  rfl'

private theorem leaf1811InnerLogValid :
    leaf1811InnerLog.Valid 8 (innerAD leaf1811Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1811CoverageChecked

private noncomputable def leaf1811InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1811InputLogOnePlusV_eq :
    leaf1811InputLogOnePlusV = outerEnclosure 24
      (leaf1811Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1811RoundedFacts : LeafRoundedFacts 8
    leaf1811Certificate.logOnePlusV leaf1811InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1811InputLogOnePlusV_eq }

private noncomputable def leaf1811Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi132InputQChi innerPair22Input
    leaf1811InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1811LowerChecked :
    lowerCheck 24 leaf1811Box leaf1811Inputs = true := by
  rfl'

private theorem leaf1811CoversExact : CoversExact 8
    leaf1811Box leaf1811Certificate leaf1811InnerLog leaf1811Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi132RoundedFacts
    innerPair22RoundedFacts leaf1811RoundedFacts (by rfl)

private theorem leaf1811FlatSound : Sound leaf1811Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1811CertificateValid
    leaf1811InnerLogValid leaf1811CoversExact leaf1811LowerChecked

private noncomputable def leaf1812Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1812Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214569) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (734482371/536870912) }, upper := { exponent := 0, mantissa := (11351/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432425/268429138) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1812InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1812LocalValidity :
    LeafFacts leaf1812Box leaf1812Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1812Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214569) }) = true
      norm_num [leaf1812Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1812CertificateValid :
    WideCertificateValid leaf1812Box leaf1812Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi149ValidityFacts
    leaf1812LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1812CoverageChecked :
    coverageCheck (innerAD leaf1812Box) leaf1812InnerLog = true := by
  rfl'

private theorem leaf1812InnerLogValid :
    leaf1812InnerLog.Valid 8 (innerAD leaf1812Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1812CoverageChecked

private noncomputable def leaf1812InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1812InputLogOnePlusV_eq :
    leaf1812InputLogOnePlusV = outerEnclosure 24
      (leaf1812Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1812RoundedFacts : LeafRoundedFacts 8
    leaf1812Certificate.logOnePlusV leaf1812InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1812InputLogOnePlusV_eq }

private noncomputable def leaf1812Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi149InputQChi innerPair22Input
    leaf1812InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1812LowerChecked :
    lowerCheck 24 leaf1812Box leaf1812Inputs = true := by
  rfl'

private theorem leaf1812CoversExact : CoversExact 8
    leaf1812Box leaf1812Certificate leaf1812InnerLog leaf1812Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi149RoundedFacts
    innerPair22RoundedFacts leaf1812RoundedFacts (by rfl)

private theorem leaf1812FlatSound : Sound leaf1812Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1812CertificateValid
    leaf1812InnerLogValid leaf1812CoversExact leaf1812LowerChecked

private noncomputable def leaf1813Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1813Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107271) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (736186201/536870912) }, upper := { exponent := 0, mantissa := (5689/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216199/134214542) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1813InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1813LocalValidity :
    LeafFacts leaf1813Box leaf1813Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1813Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107271) }) = true
      norm_num [leaf1813Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1813CertificateValid :
    WideCertificateValid leaf1813Box leaf1813Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi149ValidityFacts
    leaf1813LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1813CoverageChecked :
    coverageCheck (innerAD leaf1813Box) leaf1813InnerLog = true := by
  rfl'

private theorem leaf1813InnerLogValid :
    leaf1813InnerLog.Valid 8 (innerAD leaf1813Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1813CoverageChecked

private noncomputable def leaf1813InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1813InputLogOnePlusV_eq :
    leaf1813InputLogOnePlusV = outerEnclosure 24
      (leaf1813Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1813RoundedFacts : LeafRoundedFacts 8
    leaf1813Certificate.logOnePlusV leaf1813InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1813InputLogOnePlusV_eq }

private noncomputable def leaf1813Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi149InputQChi innerPair22Input
    leaf1813InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1813LowerChecked :
    lowerCheck 24 leaf1813Box leaf1813Inputs = true := by
  rfl'

private theorem leaf1813CoversExact : CoversExact 8
    leaf1813Box leaf1813Certificate leaf1813InnerLog leaf1813Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi149RoundedFacts
    innerPair22RoundedFacts leaf1813RoundedFacts (by rfl)

private theorem leaf1813FlatSound : Sound leaf1813Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1813CertificateValid
    leaf1813InnerLogValid leaf1813CoversExact leaf1813LowerChecked

private noncomputable def leaf1814Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1814Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553613) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (742084081/536870912) }, upper := { exponent := 0, mantissa := (2867/2048) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108077/67107226) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1814InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1814LocalValidity :
    LeafFacts leaf1814Box leaf1814Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1814Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553613) }) = true
      norm_num [leaf1814Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1814CertificateValid :
    WideCertificateValid leaf1814Box leaf1814Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi150ValidityFacts
    leaf1814LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1814CoverageChecked :
    coverageCheck (innerAD leaf1814Box) leaf1814InnerLog = true := by
  rfl'

private theorem leaf1814InnerLogValid :
    leaf1814InnerLog.Valid 8 (innerAD leaf1814Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1814CoverageChecked

private noncomputable def leaf1814InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1814InputLogOnePlusV_eq :
    leaf1814InputLogOnePlusV = outerEnclosure 24
      (leaf1814Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1814RoundedFacts : LeafRoundedFacts 8
    leaf1814Certificate.logOnePlusV leaf1814InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1814InputLogOnePlusV_eq }

private noncomputable def leaf1814Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1814InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1814LowerChecked :
    lowerCheck 24 leaf1814Box leaf1814Inputs = true := by
  rfl'

private theorem leaf1814CoversExact : CoversExact 8
    leaf1814Box leaf1814Certificate leaf1814InnerLog leaf1814Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1814RoundedFacts (by rfl)

private theorem leaf1814FlatSound : Sound leaf1814Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1814CertificateValid
    leaf1814InnerLogValid leaf1814CoversExact leaf1814LowerChecked

private noncomputable def leaf1815Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1815Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776803) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (743853443/536870912) }, upper := { exponent := 0, mantissa := (1437/1024) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554035/33553606) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1815InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1815LocalValidity :
    LeafFacts leaf1815Box leaf1815Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1815Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776803) }) = true
      norm_num [leaf1815Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1815CertificateValid :
    WideCertificateValid leaf1815Box leaf1815Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi150ValidityFacts
    leaf1815LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1815CoverageChecked :
    coverageCheck (innerAD leaf1815Box) leaf1815InnerLog = true := by
  rfl'

private theorem leaf1815InnerLogValid :
    leaf1815InnerLog.Valid 8 (innerAD leaf1815Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1815CoverageChecked

private noncomputable def leaf1815InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1815InputLogOnePlusV_eq :
    leaf1815InputLogOnePlusV = outerEnclosure 24
      (leaf1815Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1815RoundedFacts : LeafRoundedFacts 8
    leaf1815Certificate.logOnePlusV leaf1815InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1815InputLogOnePlusV_eq }

private noncomputable def leaf1815Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1815InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1815LowerChecked :
    lowerCheck 24 leaf1815Box leaf1815Inputs = true := by
  rfl'

private theorem leaf1815CoversExact : CoversExact 8
    leaf1815Box leaf1815Certificate leaf1815InnerLog leaf1815Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1815RoundedFacts (by rfl)

private theorem leaf1815FlatSound : Sound leaf1815Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1815CertificateValid
    leaf1815InnerLogValid leaf1815CoversExact leaf1815LowerChecked

private noncomputable def leaf1816Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1816Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214515) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (737890031/536870912) }, upper := { exponent := 0, mantissa := (11405/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432371/268429030) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1816InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1816LocalValidity :
    LeafFacts leaf1816Box leaf1816Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1816Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214515) }) = true
      norm_num [leaf1816Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1816CertificateValid :
    WideCertificateValid leaf1816Box leaf1816Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi149ValidityFacts
    leaf1816LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1816CoverageChecked :
    coverageCheck (innerAD leaf1816Box) leaf1816InnerLog = true := by
  rfl'

private theorem leaf1816InnerLogValid :
    leaf1816InnerLog.Valid 8 (innerAD leaf1816Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1816CoverageChecked

private noncomputable def leaf1816InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1816InputLogOnePlusV_eq :
    leaf1816InputLogOnePlusV = outerEnclosure 24
      (leaf1816Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1816RoundedFacts : LeafRoundedFacts 8
    leaf1816Certificate.logOnePlusV leaf1816InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1816InputLogOnePlusV_eq }

private noncomputable def leaf1816Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi149InputQChi innerPair22Input
    leaf1816InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1816LowerChecked :
    lowerCheck 24 leaf1816Box leaf1816Inputs = true := by
  rfl'

private theorem leaf1816CoversExact : CoversExact 8
    leaf1816Box leaf1816Certificate leaf1816InnerLog leaf1816Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi149RoundedFacts
    innerPair22RoundedFacts leaf1816RoundedFacts (by rfl)

private theorem leaf1816FlatSound : Sound leaf1816Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1816CertificateValid
    leaf1816InnerLogValid leaf1816CoversExact leaf1816LowerChecked

private noncomputable def leaf1817Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1817Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776811) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (739593861/536870912) }, upper := { exponent := 0, mantissa := (1429/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554043/33553622) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1817InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1817LocalValidity :
    LeafFacts leaf1817Box leaf1817Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1817Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776811) }) = true
      norm_num [leaf1817Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1817CertificateValid :
    WideCertificateValid leaf1817Box leaf1817Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi149ValidityFacts
    leaf1817LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1817CoverageChecked :
    coverageCheck (innerAD leaf1817Box) leaf1817InnerLog = true := by
  rfl'

private theorem leaf1817InnerLogValid :
    leaf1817InnerLog.Valid 8 (innerAD leaf1817Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1817CoverageChecked

private noncomputable def leaf1817InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1817InputLogOnePlusV_eq :
    leaf1817InputLogOnePlusV = outerEnclosure 24
      (leaf1817Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1817RoundedFacts : LeafRoundedFacts 8
    leaf1817Certificate.logOnePlusV leaf1817InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1817InputLogOnePlusV_eq }

private noncomputable def leaf1817Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi149InputQChi innerPair26Input
    leaf1817InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1817LowerChecked :
    lowerCheck 24 leaf1817Box leaf1817Inputs = true := by
  rfl'

private theorem leaf1817CoversExact : CoversExact 8
    leaf1817Box leaf1817Certificate leaf1817InnerLog leaf1817Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi149RoundedFacts
    innerPair26RoundedFacts leaf1817RoundedFacts (by rfl)

private theorem leaf1817FlatSound : Sound leaf1817Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1817CertificateValid
    leaf1817InnerLogValid leaf1817CoversExact leaf1817LowerChecked

private noncomputable def leaf1818Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1818Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553599) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (745622805/536870912) }, upper := { exponent := 0, mantissa := (2881/2048) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108063/67107198) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1818InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1818LocalValidity :
    LeafFacts leaf1818Box leaf1818Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1818Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553599) }) = true
      norm_num [leaf1818Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1818CertificateValid :
    WideCertificateValid leaf1818Box leaf1818Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi150ValidityFacts
    leaf1818LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1818CoverageChecked :
    coverageCheck (innerAD leaf1818Box) leaf1818InnerLog = true := by
  rfl'

private theorem leaf1818InnerLogValid :
    leaf1818InnerLog.Valid 8 (innerAD leaf1818Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1818CoverageChecked

private noncomputable def leaf1818InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1818InputLogOnePlusV_eq :
    leaf1818InputLogOnePlusV = outerEnclosure 24
      (leaf1818Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1818RoundedFacts : LeafRoundedFacts 8
    leaf1818Certificate.logOnePlusV leaf1818InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1818InputLogOnePlusV_eq }

private noncomputable def leaf1818Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1818InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1818LowerChecked :
    lowerCheck 24 leaf1818Box leaf1818Inputs = true := by
  rfl'

private theorem leaf1818CoversExact : CoversExact 8
    leaf1818Box leaf1818Certificate leaf1818InnerLog leaf1818Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1818RoundedFacts (by rfl)

private theorem leaf1818FlatSound : Sound leaf1818Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1818CertificateValid
    leaf1818InnerLogValid leaf1818CoversExact leaf1818LowerChecked

private noncomputable def leaf1819Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1819Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (747392167/536870912) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388507/8388398) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1819InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1819LocalValidity :
    LeafFacts leaf1819Box leaf1819Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1819Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194199) }) = true
      norm_num [leaf1819Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1819CertificateValid :
    WideCertificateValid leaf1819Box leaf1819Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi150ValidityFacts
    leaf1819LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1819CoverageChecked :
    coverageCheck (innerAD leaf1819Box) leaf1819InnerLog = true := by
  rfl'

private theorem leaf1819InnerLogValid :
    leaf1819InnerLog.Valid 8 (innerAD leaf1819Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1819CoverageChecked

private noncomputable def leaf1819InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1819InputLogOnePlusV_eq :
    leaf1819InputLogOnePlusV = outerEnclosure 24
      (leaf1819Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1819RoundedFacts : LeafRoundedFacts 8
    leaf1819Certificate.logOnePlusV leaf1819InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1819InputLogOnePlusV_eq }

private noncomputable def leaf1819Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1819InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1819LowerChecked :
    lowerCheck 24 leaf1819Box leaf1819Inputs = true := by
  rfl'

private theorem leaf1819CoversExact : CoversExact 8
    leaf1819Box leaf1819Certificate leaf1819InnerLog leaf1819Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1819RoundedFacts (by rfl)

private theorem leaf1819FlatSound : Sound leaf1819Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1819CertificateValid
    leaf1819InnerLogValid leaf1819CoversExact leaf1819LowerChecked

private noncomputable def leaf1820Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1820Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214335) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (749685791/536870912) }, upper := { exponent := 0, mantissa := (11585/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432191/268428670) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1820InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1820LocalValidity :
    LeafFacts leaf1820Box leaf1820Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1820Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214335) }) = true
      norm_num [leaf1820Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1820CertificateValid :
    WideCertificateValid leaf1820Box leaf1820Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi155ValidityFacts
    leaf1820LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1820CoverageChecked :
    coverageCheck (innerAD leaf1820Box) leaf1820InnerLog = true := by
  rfl'

private theorem leaf1820InnerLogValid :
    leaf1820InnerLog.Valid 8 (innerAD leaf1820Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1820CoverageChecked

private noncomputable def leaf1820InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1820InputLogOnePlusV_eq :
    leaf1820InputLogOnePlusV = outerEnclosure 24
      (leaf1820Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1820RoundedFacts : LeafRoundedFacts 8
    leaf1820Certificate.logOnePlusV leaf1820InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1820InputLogOnePlusV_eq }

private noncomputable def leaf1820Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1820InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1820LowerChecked :
    lowerCheck 24 leaf1820Box leaf1820Inputs = true := by
  rfl'

private theorem leaf1820CoversExact : CoversExact 8
    leaf1820Box leaf1820Certificate leaf1820InnerLog leaf1820Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1820RoundedFacts (by rfl)

private theorem leaf1820FlatSound : Sound leaf1820Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1820CertificateValid
    leaf1820InnerLogValid leaf1820CoversExact leaf1820LowerChecked

private noncomputable def leaf1821Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1821Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107153) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (751520685/536870912) }, upper := { exponent := 0, mantissa := (5807/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216081/134214306) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1821InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1821LocalValidity :
    LeafFacts leaf1821Box leaf1821Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1821Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107153) }) = true
      norm_num [leaf1821Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1821CertificateValid :
    WideCertificateValid leaf1821Box leaf1821Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi155ValidityFacts
    leaf1821LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1821CoverageChecked :
    coverageCheck (innerAD leaf1821Box) leaf1821InnerLog = true := by
  rfl'

private theorem leaf1821InnerLogValid :
    leaf1821InnerLog.Valid 8 (innerAD leaf1821Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1821CoverageChecked

private noncomputable def leaf1821InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1821InputLogOnePlusV_eq :
    leaf1821InputLogOnePlusV = outerEnclosure 24
      (leaf1821Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1821RoundedFacts : LeafRoundedFacts 8
    leaf1821Certificate.logOnePlusV leaf1821InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1821InputLogOnePlusV_eq }

private noncomputable def leaf1821Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1821InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1821LowerChecked :
    lowerCheck 24 leaf1821Box leaf1821Inputs = true := by
  rfl'

private theorem leaf1821CoversExact : CoversExact 8
    leaf1821Box leaf1821Certificate leaf1821InnerLog leaf1821Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1821RoundedFacts (by rfl)

private theorem leaf1821FlatSound : Sound leaf1821Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1821CertificateValid
    leaf1821InnerLogValid leaf1821CoversExact leaf1821LowerChecked

private noncomputable def leaf1822Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1822Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (3947584/3947477) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (757287501/536870912) }, upper := { exponent := 0, mantissa := (5851/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (7895061/7894954) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1822InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1822LocalValidity :
    LeafFacts leaf1822Box leaf1822Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1822Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3947584/3947477) }) = true
      norm_num [leaf1822Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1822CertificateValid :
    WideCertificateValid leaf1822Box leaf1822Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi156ValidityFacts
    leaf1822LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1822CoverageChecked :
    coverageCheck (innerAD leaf1822Box) leaf1822InnerLog = true := by
  rfl'

private theorem leaf1822InnerLogValid :
    leaf1822InnerLog.Valid 8 (innerAD leaf1822Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1822CoverageChecked

private noncomputable def leaf1822InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1822InputLogOnePlusV_eq :
    leaf1822InputLogOnePlusV = outerEnclosure 24
      (leaf1822Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1822RoundedFacts : LeafRoundedFacts 8
    leaf1822Certificate.logOnePlusV leaf1822InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1822InputLogOnePlusV_eq }

private noncomputable def leaf1822Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1822InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1822LowerChecked :
    lowerCheck 24 leaf1822Box leaf1822Inputs = true := by
  rfl'

private theorem leaf1822CoversExact : CoversExact 8
    leaf1822Box leaf1822Certificate leaf1822InnerLog leaf1822Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1822RoundedFacts (by rfl)

private theorem leaf1822FlatSound : Sound leaf1822Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1822CertificateValid
    leaf1822InnerLogValid leaf1822CoversExact leaf1822LowerChecked

private noncomputable def leaf1823Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1823Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (759187927/536870912) }, upper := { exponent := 0, mantissa := (2933/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108011/67107094) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1823InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1823LocalValidity :
    LeafFacts leaf1823Box leaf1823Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1823Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553547) }) = true
      norm_num [leaf1823Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1823CertificateValid :
    WideCertificateValid leaf1823Box leaf1823Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi156ValidityFacts
    leaf1823LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1823CoverageChecked :
    coverageCheck (innerAD leaf1823Box) leaf1823InnerLog = true := by
  rfl'

private theorem leaf1823InnerLogValid :
    leaf1823InnerLog.Valid 8 (innerAD leaf1823Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1823CoverageChecked

private noncomputable def leaf1823InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1823InputLogOnePlusV_eq :
    leaf1823InputLogOnePlusV = outerEnclosure 24
      (leaf1823Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1823RoundedFacts : LeafRoundedFacts 8
    leaf1823Certificate.logOnePlusV leaf1823InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1823InputLogOnePlusV_eq }

private noncomputable def leaf1823Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1823InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1823LowerChecked :
    lowerCheck 24 leaf1823Box leaf1823Inputs = true := by
  rfl'

private theorem leaf1823CoversExact : CoversExact 8
    leaf1823Box leaf1823Certificate leaf1823InnerLog leaf1823Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1823RoundedFacts (by rfl)

private theorem leaf1823FlatSound : Sound leaf1823Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1823CertificateValid
    leaf1823InnerLogValid leaf1823CoversExact leaf1823LowerChecked

private noncomputable def leaf1824Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1824Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214101) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (764889211/536870912) }, upper := { exponent := 0, mantissa := (11819/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431957/268428202) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1824InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1824LocalValidity :
    LeafFacts leaf1824Box leaf1824Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1824Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214101) }) = true
      norm_num [leaf1824Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1824CertificateValid :
    WideCertificateValid leaf1824Box leaf1824Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi153ValidityFacts
    leaf1824LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1824CoverageChecked :
    coverageCheck (innerAD leaf1824Box) leaf1824InnerLog = true := by
  rfl'

private theorem leaf1824InnerLogValid :
    leaf1824InnerLog.Valid 8 (innerAD leaf1824Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1824CoverageChecked

private noncomputable def leaf1824InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1824InputLogOnePlusV_eq :
    leaf1824InputLogOnePlusV = outerEnclosure 24
      (leaf1824Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1824RoundedFacts : LeafRoundedFacts 8
    leaf1824Certificate.logOnePlusV leaf1824InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1824InputLogOnePlusV_eq }

private noncomputable def leaf1824Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi153InputQChi innerPair405Input
    leaf1824InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1824LowerChecked :
    lowerCheck 24 leaf1824Box leaf1824Inputs = true := by
  rfl'

private theorem leaf1824CoversExact : CoversExact 8
    leaf1824Box leaf1824Certificate leaf1824InnerLog leaf1824Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi153RoundedFacts
    innerPair405RoundedFacts leaf1824RoundedFacts (by rfl)

private theorem leaf1824FlatSound : Sound leaf1824Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1824CertificateValid
    leaf1824InnerLogValid leaf1824CoversExact leaf1824LowerChecked

private noncomputable def leaf1825Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1825Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107035) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (766855169/536870912) }, upper := { exponent := 0, mantissa := (5925/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215963/134214070) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1825InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1825LocalValidity :
    LeafFacts leaf1825Box leaf1825Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1825Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107035) }) = true
      norm_num [leaf1825Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1825CertificateValid :
    WideCertificateValid leaf1825Box leaf1825Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi153ValidityFacts
    leaf1825LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1825CoverageChecked :
    coverageCheck (innerAD leaf1825Box) leaf1825InnerLog = true := by
  rfl'

private theorem leaf1825InnerLogValid :
    leaf1825InnerLog.Valid 8 (innerAD leaf1825Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1825CoverageChecked

private noncomputable def leaf1825InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1825InputLogOnePlusV_eq :
    leaf1825InputLogOnePlusV = outerEnclosure 24
      (leaf1825Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1825RoundedFacts : LeafRoundedFacts 8
    leaf1825Certificate.logOnePlusV leaf1825InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1825InputLogOnePlusV_eq }

private noncomputable def leaf1825Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi153InputQChi innerPair405Input
    leaf1825InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1825LowerChecked :
    lowerCheck 24 leaf1825Box leaf1825Inputs = true := by
  rfl'

private theorem leaf1825CoversExact : CoversExact 8
    leaf1825Box leaf1825Certificate leaf1825InnerLog leaf1825Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi153RoundedFacts
    innerPair405RoundedFacts leaf1825RoundedFacts (by rfl)

private theorem leaf1825FlatSound : Sound leaf1825Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1825CertificateValid
    leaf1825InnerLogValid leaf1825CoversExact leaf1825LowerChecked

private noncomputable def leaf1826Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1826Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194187) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (772490921/536870912) }, upper := { exponent := 0, mantissa := (373/256) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388495/8388374) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1826InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf1826LocalValidity :
    LeafFacts leaf1826Box leaf1826Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1826Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194187) }) = true
      norm_num [leaf1826Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1826CertificateValid :
    WideCertificateValid leaf1826Box leaf1826Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi154ValidityFacts
    leaf1826LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1826CoverageChecked :
    coverageCheck (innerAD leaf1826Box) leaf1826InnerLog = true := by
  rfl'

private theorem leaf1826InnerLogValid :
    leaf1826InnerLog.Valid 8 (innerAD leaf1826Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf1826CoverageChecked

private noncomputable def leaf1826InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1826InputLogOnePlusV_eq :
    leaf1826InputLogOnePlusV = outerEnclosure 24
      (leaf1826Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1826RoundedFacts : LeafRoundedFacts 8
    leaf1826Certificate.logOnePlusV leaf1826InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1826InputLogOnePlusV_eq }

private noncomputable def leaf1826Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi154InputQChi innerPair37Input
    leaf1826InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1826LowerChecked :
    lowerCheck 24 leaf1826Box leaf1826Inputs = true := by
  rfl'

private theorem leaf1826CoversExact : CoversExact 8
    leaf1826Box leaf1826Certificate leaf1826InnerLog leaf1826Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi154RoundedFacts
    innerPair37RoundedFacts leaf1826RoundedFacts (by rfl)

private theorem leaf1826FlatSound : Sound leaf1826Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1826CertificateValid
    leaf1826InnerLogValid leaf1826CoversExact leaf1826LowerChecked

private noncomputable def leaf1827Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1827Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (2097154/2097093) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (774522411/536870912) }, upper := { exponent := 0, mantissa := (187/128) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4194247/4194186) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1827InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf1827LocalValidity :
    LeafFacts leaf1827Box leaf1827Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1827Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2097154/2097093) }) = true
      norm_num [leaf1827Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1827CertificateValid :
    WideCertificateValid leaf1827Box leaf1827Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi154ValidityFacts
    leaf1827LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1827CoverageChecked :
    coverageCheck (innerAD leaf1827Box) leaf1827InnerLog = true := by
  rfl'

private theorem leaf1827InnerLogValid :
    leaf1827InnerLog.Valid 8 (innerAD leaf1827Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf1827CoverageChecked

private noncomputable def leaf1827InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1827InputLogOnePlusV_eq :
    leaf1827InputLogOnePlusV = outerEnclosure 24
      (leaf1827Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1827RoundedFacts : LeafRoundedFacts 8
    leaf1827Certificate.logOnePlusV leaf1827InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1827InputLogOnePlusV_eq }

private noncomputable def leaf1827Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi154InputQChi innerPair37Input
    leaf1827InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1827LowerChecked :
    lowerCheck 24 leaf1827Box leaf1827Inputs = true := by
  rfl'

private theorem leaf1827CoversExact : CoversExact 8
    leaf1827Box leaf1827Certificate leaf1827InnerLog leaf1827Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi154RoundedFacts
    innerPair37RoundedFacts leaf1827RoundedFacts (by rfl)

private theorem leaf1827FlatSound : Sound leaf1827Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1827CertificateValid
    leaf1827InnerLogValid leaf1827CoversExact leaf1827LowerChecked

private noncomputable def leaf1828Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1828Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214277) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (753355579/536870912) }, upper := { exponent := 0, mantissa := (11643/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432133/268428554) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1828InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1828LocalValidity :
    LeafFacts leaf1828Box leaf1828Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1828Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214277) }) = true
      norm_num [leaf1828Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1828CertificateValid :
    WideCertificateValid leaf1828Box leaf1828Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi155ValidityFacts
    leaf1828LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1828CoverageChecked :
    coverageCheck (innerAD leaf1828Box) leaf1828InnerLog = true := by
  rfl'

private theorem leaf1828InnerLogValid :
    leaf1828InnerLog.Valid 8 (innerAD leaf1828Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1828CoverageChecked

private noncomputable def leaf1828InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1828InputLogOnePlusV_eq :
    leaf1828InputLogOnePlusV = outerEnclosure 24
      (leaf1828Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1828RoundedFacts : LeafRoundedFacts 8
    leaf1828Certificate.logOnePlusV leaf1828InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1828InputLogOnePlusV_eq }

private noncomputable def leaf1828Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1828InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1828LowerChecked :
    lowerCheck 24 leaf1828Box leaf1828Inputs = true := by
  rfl'

private theorem leaf1828CoversExact : CoversExact 8
    leaf1828Box leaf1828Certificate leaf1828InnerLog leaf1828Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1828RoundedFacts (by rfl)

private theorem leaf1828FlatSound : Sound leaf1828Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1828CertificateValid
    leaf1828InnerLogValid leaf1828CoversExact leaf1828LowerChecked

private noncomputable def leaf1829Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1829Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776781) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (755190473/536870912) }, upper := { exponent := 0, mantissa := (1459/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554013/33553562) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1829InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1829LocalValidity :
    LeafFacts leaf1829Box leaf1829Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1829Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776781) }) = true
      norm_num [leaf1829Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1829CertificateValid :
    WideCertificateValid leaf1829Box leaf1829Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi155ValidityFacts
    leaf1829LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1829CoverageChecked :
    coverageCheck (innerAD leaf1829Box) leaf1829InnerLog = true := by
  rfl'

private theorem leaf1829InnerLogValid :
    leaf1829InnerLog.Valid 8 (innerAD leaf1829Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1829CoverageChecked

private noncomputable def leaf1829InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1829InputLogOnePlusV_eq :
    leaf1829InputLogOnePlusV = outerEnclosure 24
      (leaf1829Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1829RoundedFacts : LeafRoundedFacts 8
    leaf1829Certificate.logOnePlusV leaf1829InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1829InputLogOnePlusV_eq }

private noncomputable def leaf1829Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1829InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1829LowerChecked :
    lowerCheck 24 leaf1829Box leaf1829Inputs = true := by
  rfl'

private theorem leaf1829CoversExact : CoversExact 8
    leaf1829Box leaf1829Certificate leaf1829InnerLog leaf1829Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1829RoundedFacts (by rfl)

private theorem leaf1829FlatSound : Sound leaf1829Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1829CertificateValid
    leaf1829InnerLogValid leaf1829CoversExact leaf1829LowerChecked

private noncomputable def leaf1830Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1830Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107079) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (761088353/536870912) }, upper := { exponent := 0, mantissa := (5881/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216007/134214158) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1830InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1830LocalValidity :
    LeafFacts leaf1830Box leaf1830Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1830Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107079) }) = true
      norm_num [leaf1830Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1830CertificateValid :
    WideCertificateValid leaf1830Box leaf1830Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi156ValidityFacts
    leaf1830LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1830CoverageChecked :
    coverageCheck (innerAD leaf1830Box) leaf1830InnerLog = true := by
  rfl'

private theorem leaf1830InnerLogValid :
    leaf1830InnerLog.Valid 8 (innerAD leaf1830Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1830CoverageChecked

private noncomputable def leaf1830InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf1830InputLogOnePlusV_eq :
    leaf1830InputLogOnePlusV = outerEnclosure 24
      (leaf1830Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1830RoundedFacts : LeafRoundedFacts 8
    leaf1830Certificate.logOnePlusV leaf1830InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1830InputLogOnePlusV_eq }

private noncomputable def leaf1830Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1830InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1830LowerChecked :
    lowerCheck 24 leaf1830Box leaf1830Inputs = true := by
  rfl'

private theorem leaf1830CoversExact : CoversExact 8
    leaf1830Box leaf1830Certificate leaf1830InnerLog leaf1830Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1830RoundedFacts (by rfl)

private theorem leaf1830FlatSound : Sound leaf1830Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1830CertificateValid
    leaf1830InnerLogValid leaf1830CoversExact leaf1830LowerChecked

private noncomputable def leaf1831Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1831Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388383) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (762988779/536870912) }, upper := { exponent := 0, mantissa := (737/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16776999/16776766) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1831InnerLog : WideLogData :=
  innerPair144Data

set_option maxRecDepth 1000000 in
private theorem leaf1831LocalValidity :
    LeafFacts leaf1831Box leaf1831Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1831Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388383) }) = true
      norm_num [leaf1831Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1831CertificateValid :
    WideCertificateValid leaf1831Box leaf1831Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi156ValidityFacts
    leaf1831LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1831CoverageChecked :
    coverageCheck (innerAD leaf1831Box) leaf1831InnerLog = true := by
  rfl'

private theorem leaf1831InnerLogValid :
    leaf1831InnerLog.Valid 8 (innerAD leaf1831Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint41PositiveFacts.valid leaf1831CoverageChecked

private noncomputable def leaf1831InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1831InputLogOnePlusV_eq :
    leaf1831InputLogOnePlusV = outerEnclosure 24
      (leaf1831Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1831RoundedFacts : LeafRoundedFacts 8
    leaf1831Certificate.logOnePlusV leaf1831InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1831InputLogOnePlusV_eq }

private noncomputable def leaf1831Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi156InputQChi innerPair144Input
    leaf1831InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1831LowerChecked :
    lowerCheck 24 leaf1831Box leaf1831Inputs = true := by
  rfl'

private theorem leaf1831CoversExact : CoversExact 8
    leaf1831Box leaf1831Certificate leaf1831InnerLog leaf1831Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi156RoundedFacts
    innerPair144RoundedFacts leaf1831RoundedFacts (by rfl)

private theorem leaf1831FlatSound : Sound leaf1831Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1831CertificateValid
    leaf1831InnerLogValid leaf1831CoversExact leaf1831LowerChecked

private noncomputable def leaf1832Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1832Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (768821127/536870912) }, upper := { exponent := 0, mantissa := (11881/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431895/268428078) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1832InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1832LocalValidity :
    LeafFacts leaf1832Box leaf1832Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1832Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214039) }) = true
      norm_num [leaf1832Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1832CertificateValid :
    WideCertificateValid leaf1832Box leaf1832Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi153ValidityFacts
    leaf1832LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1832CoverageChecked :
    coverageCheck (innerAD leaf1832Box) leaf1832InnerLog = true := by
  rfl'

private theorem leaf1832InnerLogValid :
    leaf1832InnerLog.Valid 8 (innerAD leaf1832Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1832CoverageChecked

private noncomputable def leaf1832InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1832InputLogOnePlusV_eq :
    leaf1832InputLogOnePlusV = outerEnclosure 24
      (leaf1832Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1832RoundedFacts : LeafRoundedFacts 8
    leaf1832Certificate.logOnePlusV leaf1832InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1832InputLogOnePlusV_eq }

private noncomputable def leaf1832Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi153InputQChi innerPair405Input
    leaf1832InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1832LowerChecked :
    lowerCheck 24 leaf1832Box leaf1832Inputs = true := by
  rfl'

private theorem leaf1832CoversExact : CoversExact 8
    leaf1832Box leaf1832Certificate leaf1832InnerLog leaf1832Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi153RoundedFacts
    innerPair405RoundedFacts leaf1832RoundedFacts (by rfl)

private theorem leaf1832FlatSound : Sound leaf1832Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1832CertificateValid
    leaf1832InnerLogValid leaf1832CoversExact leaf1832LowerChecked

private noncomputable def leaf1833Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1833Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776751) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (770787085/536870912) }, upper := { exponent := 0, mantissa := (1489/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33553983/33553502) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1833InnerLog : WideLogData :=
  innerPair442Data

set_option maxRecDepth 1000000 in
private theorem leaf1833LocalValidity :
    LeafFacts leaf1833Box leaf1833Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1833Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776751) }) = true
      norm_num [leaf1833Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1833CertificateValid :
    WideCertificateValid leaf1833Box leaf1833Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi153ValidityFacts
    leaf1833LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1833CoverageChecked :
    coverageCheck (innerAD leaf1833Box) leaf1833InnerLog = true := by
  rfl'

private theorem leaf1833InnerLogValid :
    leaf1833InnerLog.Valid 8 (innerAD leaf1833Box) :=
  wideLogDataValid_of_cachedCheck endpoint155PositiveFacts
    endpoint108PositiveFacts.valid leaf1833CoverageChecked

private noncomputable def leaf1833InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1833InputLogOnePlusV_eq :
    leaf1833InputLogOnePlusV = outerEnclosure 24
      (leaf1833Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1833RoundedFacts : LeafRoundedFacts 8
    leaf1833Certificate.logOnePlusV leaf1833InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1833InputLogOnePlusV_eq }

private noncomputable def leaf1833Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi153InputQChi innerPair442Input
    leaf1833InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1833LowerChecked :
    lowerCheck 24 leaf1833Box leaf1833Inputs = true := by
  rfl'

private theorem leaf1833CoversExact : CoversExact 8
    leaf1833Box leaf1833Certificate leaf1833InnerLog leaf1833Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi153RoundedFacts
    innerPair442RoundedFacts leaf1833RoundedFacts (by rfl)

private theorem leaf1833FlatSound : Sound leaf1833Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1833CertificateValid
    leaf1833InnerLogValid leaf1833CoversExact leaf1833LowerChecked

private noncomputable def leaf1834Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1834Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194185) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (776553901/536870912) }, upper := { exponent := 0, mantissa := (375/256) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388493/8388370) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1834InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf1834LocalValidity :
    LeafFacts leaf1834Box leaf1834Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1834Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194185) }) = true
      norm_num [leaf1834Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1834CertificateValid :
    WideCertificateValid leaf1834Box leaf1834Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi154ValidityFacts
    leaf1834LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1834CoverageChecked :
    coverageCheck (innerAD leaf1834Box) leaf1834InnerLog = true := by
  rfl'

private theorem leaf1834InnerLogValid :
    leaf1834InnerLog.Valid 8 (innerAD leaf1834Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf1834CoverageChecked

private noncomputable def leaf1834InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1834InputLogOnePlusV_eq :
    leaf1834InputLogOnePlusV = outerEnclosure 24
      (leaf1834Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1834RoundedFacts : LeafRoundedFacts 8
    leaf1834Certificate.logOnePlusV leaf1834InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1834InputLogOnePlusV_eq }

private noncomputable def leaf1834Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi154InputQChi innerPair37Input
    leaf1834InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1834LowerChecked :
    lowerCheck 24 leaf1834Box leaf1834Inputs = true := by
  rfl'

private theorem leaf1834CoversExact : CoversExact 8
    leaf1834Box leaf1834Certificate leaf1834InnerLog leaf1834Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi154RoundedFacts
    innerPair37RoundedFacts leaf1834RoundedFacts (by rfl)

private theorem leaf1834FlatSound : Sound leaf1834Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1834CertificateValid
    leaf1834InnerLogValid leaf1834CoversExact leaf1834LowerChecked

private noncomputable def leaf1835Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1835Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (1048577/1048546) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (778585391/536870912) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2097123/2097092) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1835InnerLog : WideLogData :=
  innerPair37Data

set_option maxRecDepth 1000000 in
private theorem leaf1835LocalValidity :
    LeafFacts leaf1835Box leaf1835Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1835Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1048577/1048546) }) = true
      norm_num [leaf1835Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1835CertificateValid :
    WideCertificateValid leaf1835Box leaf1835Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi154ValidityFacts
    leaf1835LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1835CoverageChecked :
    coverageCheck (innerAD leaf1835Box) leaf1835InnerLog = true := by
  rfl'

private theorem leaf1835InnerLogValid :
    leaf1835InnerLog.Valid 8 (innerAD leaf1835Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint42PositiveFacts.valid leaf1835CoverageChecked

private noncomputable def leaf1835InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1835InputLogOnePlusV_eq :
    leaf1835InputLogOnePlusV = outerEnclosure 24
      (leaf1835Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1835RoundedFacts : LeafRoundedFacts 8
    leaf1835Certificate.logOnePlusV leaf1835InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1835InputLogOnePlusV_eq }

private noncomputable def leaf1835Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi154InputQChi innerPair37Input
    leaf1835InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1835LowerChecked :
    lowerCheck 24 leaf1835Box leaf1835Inputs = true := by
  rfl'

private theorem leaf1835CoversExact : CoversExact 8
    leaf1835Box leaf1835Certificate leaf1835InnerLog leaf1835Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi154RoundedFacts
    innerPair37RoundedFacts leaf1835RoundedFacts (by rfl)

private theorem leaf1835FlatSound : Sound leaf1835Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1835CertificateValid
    leaf1835InnerLogValid leaf1835CoversExact leaf1835LowerChecked

private noncomputable def component40Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node0_sound : Sound component40Node0Box :=
  sound_of_literal_split component40Node0Box leaf1772Box leaf1773Box
    .k (113/32) (by rfl) (by rfl)
    leaf1772FlatSound leaf1773FlatSound

private noncomputable def component40Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node1_sound : Sound component40Node1Box :=
  sound_of_literal_split component40Node1Box leaf1774Box leaf1775Box
    .k (113/32) (by rfl) (by rfl)
    leaf1774FlatSound leaf1775FlatSound

private noncomputable def component40Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node2_sound : Sound component40Node2Box :=
  sound_of_literal_split component40Node2Box component40Node0Box component40Node1Box
    .chi (25/256) (by rfl) (by rfl)
    component40Node0_sound component40Node1_sound

private noncomputable def component40Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node3_sound : Sound component40Node3Box :=
  sound_of_literal_split component40Node3Box leaf1776Box leaf1777Box
    .k (115/32) (by rfl) (by rfl)
    leaf1776FlatSound leaf1777FlatSound

private noncomputable def component40Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node4_sound : Sound component40Node4Box :=
  sound_of_literal_split component40Node4Box leaf1778Box leaf1779Box
    .k (115/32) (by rfl) (by rfl)
    leaf1778FlatSound leaf1779FlatSound

private noncomputable def component40Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node5_sound : Sound component40Node5Box :=
  sound_of_literal_split component40Node5Box component40Node3Box component40Node4Box
    .chi (25/256) (by rfl) (by rfl)
    component40Node3_sound component40Node4_sound

private noncomputable def component40Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node6_sound : Sound component40Node6Box :=
  sound_of_literal_split component40Node6Box component40Node2Box component40Node5Box
    .k (57/16) (by rfl) (by rfl)
    component40Node2_sound component40Node5_sound

private noncomputable def component40Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node7_sound : Sound component40Node7Box :=
  sound_of_literal_split component40Node7Box leaf1780Box leaf1781Box
    .k (113/32) (by rfl) (by rfl)
    leaf1780FlatSound leaf1781FlatSound

private noncomputable def component40Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node8_sound : Sound component40Node8Box :=
  sound_of_literal_split component40Node8Box leaf1782Box leaf1783Box
    .k (113/32) (by rfl) (by rfl)
    leaf1782FlatSound leaf1783FlatSound

private noncomputable def component40Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node9_sound : Sound component40Node9Box :=
  sound_of_literal_split component40Node9Box component40Node7Box component40Node8Box
    .chi (27/256) (by rfl) (by rfl)
    component40Node7_sound component40Node8_sound

private noncomputable def component40Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node10_sound : Sound component40Node10Box :=
  sound_of_literal_split component40Node10Box leaf1784Box leaf1785Box
    .k (115/32) (by rfl) (by rfl)
    leaf1784FlatSound leaf1785FlatSound

private noncomputable def component40Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node11_sound : Sound component40Node11Box :=
  sound_of_literal_split component40Node11Box leaf1786Box leaf1787Box
    .k (115/32) (by rfl) (by rfl)
    leaf1786FlatSound leaf1787FlatSound

private noncomputable def component40Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node12_sound : Sound component40Node12Box :=
  sound_of_literal_split component40Node12Box component40Node10Box component40Node11Box
    .chi (27/256) (by rfl) (by rfl)
    component40Node10_sound component40Node11_sound

private noncomputable def component40Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node13_sound : Sound component40Node13Box :=
  sound_of_literal_split component40Node13Box component40Node9Box component40Node12Box
    .k (57/16) (by rfl) (by rfl)
    component40Node9_sound component40Node12_sound

private noncomputable def component40Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node14_sound : Sound component40Node14Box :=
  sound_of_literal_split component40Node14Box component40Node6Box component40Node13Box
    .chi (13/128) (by rfl) (by rfl)
    component40Node6_sound component40Node13_sound

private noncomputable def component40Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node15_sound : Sound component40Node15Box :=
  sound_of_literal_split component40Node15Box leaf1788Box leaf1789Box
    .k (113/32) (by rfl) (by rfl)
    leaf1788FlatSound leaf1789FlatSound

private noncomputable def component40Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node16_sound : Sound component40Node16Box :=
  sound_of_literal_split component40Node16Box leaf1790Box leaf1791Box
    .k (113/32) (by rfl) (by rfl)
    leaf1790FlatSound leaf1791FlatSound

private noncomputable def component40Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node17_sound : Sound component40Node17Box :=
  sound_of_literal_split component40Node17Box component40Node15Box component40Node16Box
    .chi (29/256) (by rfl) (by rfl)
    component40Node15_sound component40Node16_sound

private noncomputable def component40Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node18_sound : Sound component40Node18Box :=
  sound_of_literal_split component40Node18Box leaf1792Box leaf1793Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1792FlatSound leaf1793FlatSound

private noncomputable def component40Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node19_sound : Sound component40Node19Box :=
  sound_of_literal_split component40Node19Box leaf1794Box leaf1795Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1794FlatSound leaf1795FlatSound

private noncomputable def component40Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node20_sound : Sound component40Node20Box :=
  sound_of_literal_split component40Node20Box component40Node18Box component40Node19Box
    .k (113/32) (by rfl) (by rfl)
    component40Node18_sound component40Node19_sound

private noncomputable def component40Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node21_sound : Sound component40Node21Box :=
  sound_of_literal_split component40Node21Box component40Node17Box component40Node20Box
    .chi (15/128) (by rfl) (by rfl)
    component40Node17_sound component40Node20_sound

private noncomputable def component40Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node22_sound : Sound component40Node22Box :=
  sound_of_literal_split component40Node22Box leaf1796Box leaf1797Box
    .k (115/32) (by rfl) (by rfl)
    leaf1796FlatSound leaf1797FlatSound

private noncomputable def component40Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node23_sound : Sound component40Node23Box :=
  sound_of_literal_split component40Node23Box leaf1798Box leaf1799Box
    .k (115/32) (by rfl) (by rfl)
    leaf1798FlatSound leaf1799FlatSound

private noncomputable def component40Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node24_sound : Sound component40Node24Box :=
  sound_of_literal_split component40Node24Box component40Node22Box component40Node23Box
    .chi (29/256) (by rfl) (by rfl)
    component40Node22_sound component40Node23_sound

private noncomputable def component40Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node25_sound : Sound component40Node25Box :=
  sound_of_literal_split component40Node25Box leaf1800Box leaf1801Box
    .k (115/32) (by rfl) (by rfl)
    leaf1800FlatSound leaf1801FlatSound

private noncomputable def component40Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node26_sound : Sound component40Node26Box :=
  sound_of_literal_split component40Node26Box leaf1802Box leaf1803Box
    .k (115/32) (by rfl) (by rfl)
    leaf1802FlatSound leaf1803FlatSound

private noncomputable def component40Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node27_sound : Sound component40Node27Box :=
  sound_of_literal_split component40Node27Box component40Node25Box component40Node26Box
    .chi (31/256) (by rfl) (by rfl)
    component40Node25_sound component40Node26_sound

private noncomputable def component40Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node28_sound : Sound component40Node28Box :=
  sound_of_literal_split component40Node28Box component40Node24Box component40Node27Box
    .chi (15/128) (by rfl) (by rfl)
    component40Node24_sound component40Node27_sound

private noncomputable def component40Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node29_sound : Sound component40Node29Box :=
  sound_of_literal_split component40Node29Box component40Node21Box component40Node28Box
    .k (57/16) (by rfl) (by rfl)
    component40Node21_sound component40Node28_sound

private noncomputable def component40Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node30_sound : Sound component40Node30Box :=
  sound_of_literal_split component40Node30Box component40Node14Box component40Node29Box
    .chi (7/64) (by rfl) (by rfl)
    component40Node14_sound component40Node29_sound

private noncomputable def component40Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node31_sound : Sound component40Node31Box :=
  sound_of_literal_split component40Node31Box leaf1804Box leaf1805Box
    .k (117/32) (by rfl) (by rfl)
    leaf1804FlatSound leaf1805FlatSound

private noncomputable def component40Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node32_sound : Sound component40Node32Box :=
  sound_of_literal_split component40Node32Box leaf1806Box leaf1807Box
    .k (117/32) (by rfl) (by rfl)
    leaf1806FlatSound leaf1807FlatSound

private noncomputable def component40Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node33_sound : Sound component40Node33Box :=
  sound_of_literal_split component40Node33Box component40Node31Box component40Node32Box
    .chi (25/256) (by rfl) (by rfl)
    component40Node31_sound component40Node32_sound

private noncomputable def component40Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node34_sound : Sound component40Node34Box :=
  sound_of_literal_split component40Node34Box leaf1808Box leaf1809Box
    .k (119/32) (by rfl) (by rfl)
    leaf1808FlatSound leaf1809FlatSound

private noncomputable def component40Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node35_sound : Sound component40Node35Box :=
  sound_of_literal_split component40Node35Box leaf1810Box leaf1811Box
    .k (119/32) (by rfl) (by rfl)
    leaf1810FlatSound leaf1811FlatSound

private noncomputable def component40Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node36_sound : Sound component40Node36Box :=
  sound_of_literal_split component40Node36Box component40Node34Box component40Node35Box
    .chi (25/256) (by rfl) (by rfl)
    component40Node34_sound component40Node35_sound

private noncomputable def component40Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node37_sound : Sound component40Node37Box :=
  sound_of_literal_split component40Node37Box component40Node33Box component40Node36Box
    .k (59/16) (by rfl) (by rfl)
    component40Node33_sound component40Node36_sound

private noncomputable def component40Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node38_sound : Sound component40Node38Box :=
  sound_of_literal_split component40Node38Box leaf1812Box leaf1813Box
    .k (117/32) (by rfl) (by rfl)
    leaf1812FlatSound leaf1813FlatSound

private noncomputable def component40Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node39_sound : Sound component40Node39Box :=
  sound_of_literal_split component40Node39Box leaf1814Box leaf1815Box
    .k (117/32) (by rfl) (by rfl)
    leaf1814FlatSound leaf1815FlatSound

private noncomputable def component40Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node40_sound : Sound component40Node40Box :=
  sound_of_literal_split component40Node40Box component40Node38Box component40Node39Box
    .chi (27/256) (by rfl) (by rfl)
    component40Node38_sound component40Node39_sound

private noncomputable def component40Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node41_sound : Sound component40Node41Box :=
  sound_of_literal_split component40Node41Box leaf1816Box leaf1817Box
    .k (119/32) (by rfl) (by rfl)
    leaf1816FlatSound leaf1817FlatSound

private noncomputable def component40Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node42_sound : Sound component40Node42Box :=
  sound_of_literal_split component40Node42Box leaf1818Box leaf1819Box
    .k (119/32) (by rfl) (by rfl)
    leaf1818FlatSound leaf1819FlatSound

private noncomputable def component40Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node43_sound : Sound component40Node43Box :=
  sound_of_literal_split component40Node43Box component40Node41Box component40Node42Box
    .chi (27/256) (by rfl) (by rfl)
    component40Node41_sound component40Node42_sound

private noncomputable def component40Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node44_sound : Sound component40Node44Box :=
  sound_of_literal_split component40Node44Box component40Node40Box component40Node43Box
    .k (59/16) (by rfl) (by rfl)
    component40Node40_sound component40Node43_sound

private noncomputable def component40Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component40Node45_sound : Sound component40Node45Box :=
  sound_of_literal_split component40Node45Box component40Node37Box component40Node44Box
    .chi (13/128) (by rfl) (by rfl)
    component40Node37_sound component40Node44_sound

private noncomputable def component40Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node46_sound : Sound component40Node46Box :=
  sound_of_literal_split component40Node46Box leaf1820Box leaf1821Box
    .k (117/32) (by rfl) (by rfl)
    leaf1820FlatSound leaf1821FlatSound

private noncomputable def component40Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node47_sound : Sound component40Node47Box :=
  sound_of_literal_split component40Node47Box leaf1822Box leaf1823Box
    .k (117/32) (by rfl) (by rfl)
    leaf1822FlatSound leaf1823FlatSound

private noncomputable def component40Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node48_sound : Sound component40Node48Box :=
  sound_of_literal_split component40Node48Box component40Node46Box component40Node47Box
    .chi (29/256) (by rfl) (by rfl)
    component40Node46_sound component40Node47_sound

private noncomputable def component40Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node49_sound : Sound component40Node49Box :=
  sound_of_literal_split component40Node49Box leaf1824Box leaf1825Box
    .k (117/32) (by rfl) (by rfl)
    leaf1824FlatSound leaf1825FlatSound

private noncomputable def component40Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node50_sound : Sound component40Node50Box :=
  sound_of_literal_split component40Node50Box leaf1826Box leaf1827Box
    .k (117/32) (by rfl) (by rfl)
    leaf1826FlatSound leaf1827FlatSound

private noncomputable def component40Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node51_sound : Sound component40Node51Box :=
  sound_of_literal_split component40Node51Box component40Node49Box component40Node50Box
    .chi (31/256) (by rfl) (by rfl)
    component40Node49_sound component40Node50_sound

private noncomputable def component40Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node52_sound : Sound component40Node52Box :=
  sound_of_literal_split component40Node52Box component40Node48Box component40Node51Box
    .chi (15/128) (by rfl) (by rfl)
    component40Node48_sound component40Node51_sound

private noncomputable def component40Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node53_sound : Sound component40Node53Box :=
  sound_of_literal_split component40Node53Box leaf1828Box leaf1829Box
    .k (119/32) (by rfl) (by rfl)
    leaf1828FlatSound leaf1829FlatSound

private noncomputable def component40Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node54_sound : Sound component40Node54Box :=
  sound_of_literal_split component40Node54Box leaf1830Box leaf1831Box
    .k (119/32) (by rfl) (by rfl)
    leaf1830FlatSound leaf1831FlatSound

private noncomputable def component40Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component40Node55_sound : Sound component40Node55Box :=
  sound_of_literal_split component40Node55Box component40Node53Box component40Node54Box
    .chi (29/256) (by rfl) (by rfl)
    component40Node53_sound component40Node54_sound

private noncomputable def component40Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component40Node56_sound : Sound component40Node56Box :=
  sound_of_literal_split component40Node56Box leaf1832Box leaf1833Box
    .k (119/32) (by rfl) (by rfl)
    leaf1832FlatSound leaf1833FlatSound

private noncomputable def component40Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node57_sound : Sound component40Node57Box :=
  sound_of_literal_split component40Node57Box leaf1834Box leaf1835Box
    .k (119/32) (by rfl) (by rfl)
    leaf1834FlatSound leaf1835FlatSound

private noncomputable def component40Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node58_sound : Sound component40Node58Box :=
  sound_of_literal_split component40Node58Box component40Node56Box component40Node57Box
    .chi (31/256) (by rfl) (by rfl)
    component40Node56_sound component40Node57_sound

private noncomputable def component40Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node59_sound : Sound component40Node59Box :=
  sound_of_literal_split component40Node59Box component40Node55Box component40Node58Box
    .chi (15/128) (by rfl) (by rfl)
    component40Node55_sound component40Node58_sound

private noncomputable def component40Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node60_sound : Sound component40Node60Box :=
  sound_of_literal_split component40Node60Box component40Node52Box component40Node59Box
    .k (59/16) (by rfl) (by rfl)
    component40Node52_sound component40Node59_sound

private noncomputable def component40Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component40Node61_sound : Sound component40Node61Box :=
  sound_of_literal_split component40Node61Box component40Node45Box component40Node60Box
    .chi (7/64) (by rfl) (by rfl)
    component40Node45_sound component40Node60_sound

noncomputable def component40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component40_sound : Sound component40Box :=
  sound_of_literal_split component40Box component40Node30Box component40Node61Box
    .k (29/8) (by rfl) (by rfl)
    component40Node30_sound component40Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
