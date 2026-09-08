import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
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

private noncomputable def leaf6774Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6774Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435811/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711955456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (738135711/536870912) }, upper := { exponent := 1, mantissa := (11441/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428351997/137423910912) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6774InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6774LocalValidity :
    LeafFacts leaf6774Box leaf6774Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6774Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711955456) }) = true
      norm_num [leaf6774Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6774CertificateValid :
    WideCertificateValid leaf6774Box leaf6774Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi329ValidityFacts
    leaf6774LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6774CoverageChecked :
    coverageCheck (innerAD leaf6774Box) leaf6774InnerLog = true := by
  rfl'

private theorem leaf6774InnerLogValid :
    leaf6774InnerLog.Valid 8 (innerAD leaf6774Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6774CoverageChecked

private noncomputable def leaf6774InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629623/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6774InputLogOnePlusV_eq :
    leaf6774InputLogOnePlusV = outerEnclosure 24
      (leaf6774Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6774RoundedFacts : LeafRoundedFacts 8
    leaf6774Certificate.logOnePlusV leaf6774InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6774InputLogOnePlusV_eq }

private noncomputable def leaf6774Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi329InputQChi innerPair353Input
    leaf6774InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6774LowerChecked :
    lowerCheck 24 leaf6774Box leaf6774Inputs = true := by
  rfl'

private theorem leaf6774CoversExact : CoversExact 8
    leaf6774Box leaf6774Certificate leaf6774InnerLog leaf6774Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi329RoundedFacts
    innerPair353RoundedFacts leaf6774RoundedFacts (by rfl)

private theorem leaf6774FlatSound : Sound leaf6774Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6774CertificateValid
    leaf6774InnerLogValid leaf6774CoversExact leaf6774LowerChecked

private noncomputable def leaf6775Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6775Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711888896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (742329757/536870912) }, upper := { exponent := 1, mantissa := (5753/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428285437/137423777792) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6775InnerLog : WideLogData :=
  innerPair356Data

set_option maxRecDepth 1000000 in
private theorem leaf6775LocalValidity :
    LeafFacts leaf6775Box leaf6775Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6775Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711888896) }) = true
      norm_num [leaf6775Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6775CertificateValid :
    WideCertificateValid leaf6775Box leaf6775Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi329ValidityFacts
    leaf6775LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6775CoverageChecked :
    coverageCheck (innerAD leaf6775Box) leaf6775InnerLog = true := by
  rfl'

private theorem leaf6775InnerLogValid :
    leaf6775InnerLog.Valid 8 (innerAD leaf6775Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint96PositiveFacts.valid leaf6775CoverageChecked

private noncomputable def leaf6775InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629631/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6775InputLogOnePlusV_eq :
    leaf6775InputLogOnePlusV = outerEnclosure 24
      (leaf6775Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6775RoundedFacts : LeafRoundedFacts 8
    leaf6775Certificate.logOnePlusV leaf6775InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6775InputLogOnePlusV_eq }

private noncomputable def leaf6775Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi329InputQChi innerPair356Input
    leaf6775InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6775LowerChecked :
    lowerCheck 24 leaf6775Box leaf6775Inputs = true := by
  rfl'

private theorem leaf6775CoversExact : CoversExact 8
    leaf6775Box leaf6775Certificate leaf6775InnerLog leaf6775Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi329RoundedFacts
    innerPair356RoundedFacts leaf6775RoundedFacts (by rfl)

private theorem leaf6775FlatSound : Sound leaf6775Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6775CertificateValid
    leaf6775InnerLogValid leaf6775CoversExact leaf6775LowerChecked

private noncomputable def leaf6776Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6776Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435813/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711839744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (745475293/536870912) }, upper := { exponent := 1, mantissa := (5777/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428236285/137423679488) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6776InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6776LocalValidity :
    LeafFacts leaf6776Box leaf6776Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6776Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711839744) }) = true
      norm_num [leaf6776Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6776CertificateValid :
    WideCertificateValid leaf6776Box leaf6776Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi330ValidityFacts
    leaf6776LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6776CoverageChecked :
    coverageCheck (innerAD leaf6776Box) leaf6776InnerLog = true := by
  rfl'

private theorem leaf6776InnerLogValid :
    leaf6776InnerLog.Valid 8 (innerAD leaf6776Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6776CoverageChecked

private noncomputable def leaf6776InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629637/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6776InputLogOnePlusV_eq :
    leaf6776InputLogOnePlusV = outerEnclosure 24
      (leaf6776Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6776RoundedFacts : LeafRoundedFacts 8
    leaf6776Certificate.logOnePlusV leaf6776InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6776InputLogOnePlusV_eq }

private noncomputable def leaf6776Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi330InputQChi innerPair357Input
    leaf6776InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6776LowerChecked :
    lowerCheck 24 leaf6776Box leaf6776Inputs = true := by
  rfl'

private theorem leaf6776CoversExact : CoversExact 8
    leaf6776Box leaf6776Certificate leaf6776InnerLog leaf6776Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi330RoundedFacts
    innerPair357RoundedFacts leaf6776RoundedFacts (by rfl)

private theorem leaf6776FlatSound : Sound leaf6776Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6776CertificateValid
    leaf6776InnerLogValid leaf6776CoversExact leaf6776LowerChecked

private noncomputable def leaf6777Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6777Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711772160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (749734871/536870912) }, upper := { exponent := 1, mantissa := (2905/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428168701/137423544320) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6777InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6777LocalValidity :
    LeafFacts leaf6777Box leaf6777Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6777Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711772160) }) = true
      norm_num [leaf6777Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6777CertificateValid :
    WideCertificateValid leaf6777Box leaf6777Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi330ValidityFacts
    leaf6777LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6777CoverageChecked :
    coverageCheck (innerAD leaf6777Box) leaf6777InnerLog = true := by
  rfl'

private theorem leaf6777InnerLogValid :
    leaf6777InnerLog.Valid 8 (innerAD leaf6777Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6777CoverageChecked

private noncomputable def leaf6777InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629645/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6777InputLogOnePlusV_eq :
    leaf6777InputLogOnePlusV = outerEnclosure 24
      (leaf6777Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6777RoundedFacts : LeafRoundedFacts 8
    leaf6777Certificate.logOnePlusV leaf6777InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6777InputLogOnePlusV_eq }

private noncomputable def leaf6777Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi330InputQChi innerPair357Input
    leaf6777InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6777LowerChecked :
    lowerCheck 24 leaf6777Box leaf6777Inputs = true := by
  rfl'

private theorem leaf6777CoversExact : CoversExact 8
    leaf6777Box leaf6777Certificate leaf6777InnerLog leaf6777Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi330RoundedFacts
    innerPair357RoundedFacts leaf6777RoundedFacts (by rfl)

private theorem leaf6777FlatSound : Sound leaf6777Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6777CertificateValid
    leaf6777InnerLogValid leaf6777CoversExact leaf6777LowerChecked

private noncomputable def leaf6778Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6778Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711822336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (746523803/536870912) }, upper := { exponent := 1, mantissa := (11571/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428218877/137423644672) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6778InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6778LocalValidity :
    LeafFacts leaf6778Box leaf6778Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6778Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711822336) }) = true
      norm_num [leaf6778Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6778CertificateValid :
    WideCertificateValid leaf6778Box leaf6778Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi329ValidityFacts
    leaf6778LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6778CoverageChecked :
    coverageCheck (innerAD leaf6778Box) leaf6778InnerLog = true := by
  rfl'

private theorem leaf6778InnerLogValid :
    leaf6778InnerLog.Valid 8 (innerAD leaf6778Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6778CoverageChecked

private noncomputable def leaf6778InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629639/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6778InputLogOnePlusV_eq :
    leaf6778InputLogOnePlusV = outerEnclosure 24
      (leaf6778Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6778RoundedFacts : LeafRoundedFacts 8
    leaf6778Certificate.logOnePlusV leaf6778InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6778InputLogOnePlusV_eq }

private noncomputable def leaf6778Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi329InputQChi innerPair357Input
    leaf6778InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6778LowerChecked :
    lowerCheck 24 leaf6778Box leaf6778Inputs = true := by
  rfl'

private theorem leaf6778CoversExact : CoversExact 8
    leaf6778Box leaf6778Certificate leaf6778InnerLog leaf6778Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi329RoundedFacts
    innerPair357RoundedFacts leaf6778RoundedFacts (by rfl)

private theorem leaf6778FlatSound : Sound leaf6778Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6778CertificateValid
    leaf6778InnerLogValid leaf6778CoversExact leaf6778LowerChecked

private noncomputable def leaf6779Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6779Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711755776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (750717849/536870912) }, upper := { exponent := 1, mantissa := (2909/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428152317/137423511552) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6779InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6779LocalValidity :
    LeafFacts leaf6779Box leaf6779Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6779Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711755776) }) = true
      norm_num [leaf6779Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6779CertificateValid :
    WideCertificateValid leaf6779Box leaf6779Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi329ValidityFacts
    leaf6779LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6779CoverageChecked :
    coverageCheck (innerAD leaf6779Box) leaf6779InnerLog = true := by
  rfl'

private theorem leaf6779InnerLogValid :
    leaf6779InnerLog.Valid 8 (innerAD leaf6779Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6779CoverageChecked

private noncomputable def leaf6779InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629647/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6779InputLogOnePlusV_eq :
    leaf6779InputLogOnePlusV = outerEnclosure 24
      (leaf6779Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6779RoundedFacts : LeafRoundedFacts 8
    leaf6779Certificate.logOnePlusV leaf6779InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6779InputLogOnePlusV_eq }

private noncomputable def leaf6779Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi329InputQChi innerPair357Input
    leaf6779InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6779LowerChecked :
    lowerCheck 24 leaf6779Box leaf6779Inputs = true := by
  rfl'

private theorem leaf6779CoversExact : CoversExact 8
    leaf6779Box leaf6779Certificate leaf6779InnerLog leaf6779Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi329RoundedFacts
    innerPair357RoundedFacts leaf6779RoundedFacts (by rfl)

private theorem leaf6779FlatSound : Sound leaf6779Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6779CertificateValid
    leaf6779InnerLogValid leaf6779CoversExact leaf6779LowerChecked

private noncomputable def leaf6780Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6780Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711704576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (753994449/536870912) }, upper := { exponent := 1, mantissa := (5843/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428101117/137423409152) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6780InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6780LocalValidity :
    LeafFacts leaf6780Box leaf6780Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6780Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711704576) }) = true
      norm_num [leaf6780Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6780CertificateValid :
    WideCertificateValid leaf6780Box leaf6780Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi330ValidityFacts
    leaf6780LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6780CoverageChecked :
    coverageCheck (innerAD leaf6780Box) leaf6780InnerLog = true := by
  rfl'

private theorem leaf6780InnerLogValid :
    leaf6780InnerLog.Valid 8 (innerAD leaf6780Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6780CoverageChecked

private noncomputable def leaf6780InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814827/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6780InputLogOnePlusV_eq :
    leaf6780InputLogOnePlusV = outerEnclosure 24
      (leaf6780Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6780RoundedFacts : LeafRoundedFacts 8
    leaf6780Certificate.logOnePlusV leaf6780InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6780InputLogOnePlusV_eq }

private noncomputable def leaf6780Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi330InputQChi innerPair357Input
    leaf6780InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6780LowerChecked :
    lowerCheck 24 leaf6780Box leaf6780Inputs = true := by
  rfl'

private theorem leaf6780CoversExact : CoversExact 8
    leaf6780Box leaf6780Certificate leaf6780InnerLog leaf6780Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi330RoundedFacts
    innerPair357RoundedFacts leaf6780RoundedFacts (by rfl)

private theorem leaf6780FlatSound : Sound leaf6780Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6780CertificateValid
    leaf6780InnerLogValid leaf6780CoversExact leaf6780LowerChecked

private noncomputable def leaf6781Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6781Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711636992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (758254027/536870912) }, upper := { exponent := 1, mantissa := (1469/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428033533/137423273984) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6781InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6781LocalValidity :
    LeafFacts leaf6781Box leaf6781Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6781Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711636992) }) = true
      norm_num [leaf6781Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6781CertificateValid :
    WideCertificateValid leaf6781Box leaf6781Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi330ValidityFacts
    leaf6781LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6781CoverageChecked :
    coverageCheck (innerAD leaf6781Box) leaf6781InnerLog = true := by
  rfl'

private theorem leaf6781InnerLogValid :
    leaf6781InnerLog.Valid 8 (innerAD leaf6781Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6781CoverageChecked

private noncomputable def leaf6781InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814831/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6781InputLogOnePlusV_eq :
    leaf6781InputLogOnePlusV = outerEnclosure 24
      (leaf6781Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6781RoundedFacts : LeafRoundedFacts 8
    leaf6781Certificate.logOnePlusV leaf6781InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6781InputLogOnePlusV_eq }

private noncomputable def leaf6781Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi330InputQChi innerPair367Input
    leaf6781InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6781LowerChecked :
    lowerCheck 24 leaf6781Box leaf6781Inputs = true := by
  rfl'

private theorem leaf6781CoversExact : CoversExact 8
    leaf6781Box leaf6781Certificate leaf6781InnerLog leaf6781Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi330RoundedFacts
    innerPair367RoundedFacts leaf6781RoundedFacts (by rfl)

private theorem leaf6781FlatSound : Sound leaf6781Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6781CertificateValid
    leaf6781InnerLogValid leaf6781CoversExact leaf6781LowerChecked

private noncomputable def leaf6782Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6782Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435815/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711724032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (752814875/536870912) }, upper := { exponent := 1, mantissa := (11667/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428120573/137423448064) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6782InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6782LocalValidity :
    LeafFacts leaf6782Box leaf6782Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6782Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711724032) }) = true
      norm_num [leaf6782Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6782CertificateValid :
    WideCertificateValid leaf6782Box leaf6782Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi331ValidityFacts
    leaf6782LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6782CoverageChecked :
    coverageCheck (innerAD leaf6782Box) leaf6782InnerLog = true := by
  rfl'

private theorem leaf6782InnerLogValid :
    leaf6782InnerLog.Valid 8 (innerAD leaf6782Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6782CoverageChecked

private noncomputable def leaf6782InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629651/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6782InputLogOnePlusV_eq :
    leaf6782InputLogOnePlusV = outerEnclosure 24
      (leaf6782Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6782RoundedFacts : LeafRoundedFacts 8
    leaf6782Certificate.logOnePlusV leaf6782InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6782InputLogOnePlusV_eq }

private noncomputable def leaf6782Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi331InputQChi innerPair357Input
    leaf6782InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6782LowerChecked :
    lowerCheck 24 leaf6782Box leaf6782Inputs = true := by
  rfl'

private theorem leaf6782CoversExact : CoversExact 8
    leaf6782Box leaf6782Certificate leaf6782InnerLog leaf6782Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi331RoundedFacts
    innerPair357RoundedFacts leaf6782RoundedFacts (by rfl)

private theorem leaf6782FlatSound : Sound leaf6782Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6782CertificateValid
    leaf6782InnerLogValid leaf6782CoversExact leaf6782LowerChecked

private noncomputable def leaf6783Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6783Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711655424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (757139985/536870912) }, upper := { exponent := 1, mantissa := (5867/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428051965/137423310848) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6783InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6783LocalValidity :
    LeafFacts leaf6783Box leaf6783Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6783Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711655424) }) = true
      norm_num [leaf6783Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6783CertificateValid :
    WideCertificateValid leaf6783Box leaf6783Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi331ValidityFacts
    leaf6783LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6783CoverageChecked :
    coverageCheck (innerAD leaf6783Box) leaf6783InnerLog = true := by
  rfl'

private theorem leaf6783InnerLogValid :
    leaf6783InnerLog.Valid 8 (innerAD leaf6783Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6783CoverageChecked

private noncomputable def leaf6783InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907415/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6783InputLogOnePlusV_eq :
    leaf6783InputLogOnePlusV = outerEnclosure 24
      (leaf6783Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6783RoundedFacts : LeafRoundedFacts 8
    leaf6783Certificate.logOnePlusV leaf6783InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6783InputLogOnePlusV_eq }

private noncomputable def leaf6783Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi331InputQChi innerPair367Input
    leaf6783InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6783LowerChecked :
    lowerCheck 24 leaf6783Box leaf6783Inputs = true := by
  rfl'

private theorem leaf6783CoversExact : CoversExact 8
    leaf6783Box leaf6783Certificate leaf6783InnerLog leaf6783Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi331RoundedFacts
    innerPair367RoundedFacts leaf6783RoundedFacts (by rfl)

private theorem leaf6783FlatSound : Sound leaf6783Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6783CertificateValid
    leaf6783InnerLogValid leaf6783CoversExact leaf6783LowerChecked

private noncomputable def leaf6784Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6784Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435817/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711608320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (760154457/536870912) }, upper := { exponent := 1, mantissa := (2945/2048) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428004861/137423216640) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6784InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6784LocalValidity :
    LeafFacts leaf6784Box leaf6784Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6784Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711608320) }) = true
      norm_num [leaf6784Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6784CertificateValid :
    WideCertificateValid leaf6784Box leaf6784Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi332ValidityFacts
    leaf6784LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6784CoverageChecked :
    coverageCheck (innerAD leaf6784Box) leaf6784InnerLog = true := by
  rfl'

private theorem leaf6784InnerLogValid :
    leaf6784InnerLog.Valid 8 (innerAD leaf6784Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6784CoverageChecked

private noncomputable def leaf6784InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629665/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6784InputLogOnePlusV_eq :
    leaf6784InputLogOnePlusV = outerEnclosure 24
      (leaf6784Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6784RoundedFacts : LeafRoundedFacts 8
    leaf6784Certificate.logOnePlusV leaf6784InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6784InputLogOnePlusV_eq }

private noncomputable def leaf6784Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi332InputQChi innerPair368Input
    leaf6784InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6784LowerChecked :
    lowerCheck 24 leaf6784Box leaf6784Inputs = true := by
  rfl'

private theorem leaf6784CoversExact : CoversExact 8
    leaf6784Box leaf6784Certificate leaf6784InnerLog leaf6784Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi332RoundedFacts
    innerPair368RoundedFacts leaf6784RoundedFacts (by rfl)

private theorem leaf6784FlatSound : Sound leaf6784Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6784CertificateValid
    leaf6784InnerLogValid leaf6784CoversExact leaf6784LowerChecked

private noncomputable def leaf6785Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6785Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285502976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (764545099/536870912) }, upper := { exponent := 1, mantissa := (1481/1024) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571379633/10571005952) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6785InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6785LocalValidity :
    LeafFacts leaf6785Box leaf6785Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6785Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285502976) }) = true
      norm_num [leaf6785Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6785CertificateValid :
    WideCertificateValid leaf6785Box leaf6785Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi332ValidityFacts
    leaf6785LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6785CoverageChecked :
    coverageCheck (innerAD leaf6785Box) leaf6785InnerLog = true := by
  rfl'

private theorem leaf6785InnerLogValid :
    leaf6785InnerLog.Valid 8 (innerAD leaf6785Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6785CoverageChecked

private noncomputable def leaf6785InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814837/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6785InputLogOnePlusV_eq :
    leaf6785InputLogOnePlusV = outerEnclosure 24
      (leaf6785Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6785RoundedFacts : LeafRoundedFacts 8
    leaf6785Certificate.logOnePlusV leaf6785InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6785InputLogOnePlusV_eq }

private noncomputable def leaf6785Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi332InputQChi innerPair368Input
    leaf6785InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6785LowerChecked :
    lowerCheck 24 leaf6785Box leaf6785Inputs = true := by
  rfl'

private theorem leaf6785CoversExact : CoversExact 8
    leaf6785Box leaf6785Certificate leaf6785InnerLog leaf6785Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi332RoundedFacts
    innerPair368RoundedFacts leaf6785RoundedFacts (by rfl)

private theorem leaf6785FlatSound : Sound leaf6785Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6785CertificateValid
    leaf6785InnerLogValid leaf6785CoversExact leaf6785LowerChecked

private noncomputable def leaf6786Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6786Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041858048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (761465095/536870912) }, upper := { exponent := 1, mantissa := (11801/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8083999021/8083716096) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6786InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6786LocalValidity :
    LeafFacts leaf6786Box leaf6786Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6786Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041858048) }) = true
      norm_num [leaf6786Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6786CertificateValid :
    WideCertificateValid leaf6786Box leaf6786Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi331ValidityFacts
    leaf6786LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6786CoverageChecked :
    coverageCheck (innerAD leaf6786Box) leaf6786InnerLog = true := by
  rfl'

private theorem leaf6786InnerLogValid :
    leaf6786InnerLog.Valid 8 (innerAD leaf6786Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6786CoverageChecked

private noncomputable def leaf6786InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907417/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6786InputLogOnePlusV_eq :
    leaf6786InputLogOnePlusV = outerEnclosure 24
      (leaf6786Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6786RoundedFacts : LeafRoundedFacts 8
    leaf6786Certificate.logOnePlusV leaf6786InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6786InputLogOnePlusV_eq }

private noncomputable def leaf6786Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi331InputQChi innerPair368Input
    leaf6786InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6786LowerChecked :
    lowerCheck 24 leaf6786Box leaf6786Inputs = true := by
  rfl'

private theorem leaf6786CoversExact : CoversExact 8
    leaf6786Box leaf6786Certificate leaf6786InnerLog leaf6786Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi331RoundedFacts
    innerPair368RoundedFacts leaf6786RoundedFacts (by rfl)

private theorem leaf6786FlatSound : Sound leaf6786Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6786CertificateValid
    leaf6786InnerLogValid leaf6786CoversExact leaf6786LowerChecked

private noncomputable def leaf6787Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6787Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711518208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (765790205/536870912) }, upper := { exponent := 1, mantissa := (2967/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427914749/137423036416) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6787InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6787LocalValidity :
    LeafFacts leaf6787Box leaf6787Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6787Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711518208) }) = true
      norm_num [leaf6787Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6787CertificateValid :
    WideCertificateValid leaf6787Box leaf6787Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi331ValidityFacts
    leaf6787LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6787CoverageChecked :
    coverageCheck (innerAD leaf6787Box) leaf6787InnerLog = true := by
  rfl'

private theorem leaf6787InnerLogValid :
    leaf6787InnerLog.Valid 8 (innerAD leaf6787Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6787CoverageChecked

private noncomputable def leaf6787InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907419/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6787InputLogOnePlusV_eq :
    leaf6787InputLogOnePlusV = outerEnclosure 24
      (leaf6787Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6787RoundedFacts : LeafRoundedFacts 8
    leaf6787Certificate.logOnePlusV leaf6787InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6787InputLogOnePlusV_eq }

private noncomputable def leaf6787Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi331InputQChi innerPair368Input
    leaf6787InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6787LowerChecked :
    lowerCheck 24 leaf6787Box leaf6787Inputs = true := by
  rfl'

private theorem leaf6787CoversExact : CoversExact 8
    leaf6787Box leaf6787Certificate leaf6787InnerLog leaf6787Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi331RoundedFacts
    innerPair368RoundedFacts leaf6787RoundedFacts (by rfl)

private theorem leaf6787FlatSound : Sound leaf6787Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6787CertificateValid
    leaf6787InnerLogValid leaf6787CoversExact leaf6787LowerChecked

private noncomputable def leaf6788Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6788Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711469056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (768935741/536870912) }, upper := { exponent := 1, mantissa := (2979/2048) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427865597/137422938112) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6788InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6788LocalValidity :
    LeafFacts leaf6788Box leaf6788Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6788Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711469056) }) = true
      norm_num [leaf6788Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6788CertificateValid :
    WideCertificateValid leaf6788Box leaf6788Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi332ValidityFacts
    leaf6788LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6788CoverageChecked :
    coverageCheck (innerAD leaf6788Box) leaf6788InnerLog = true := by
  rfl'

private theorem leaf6788InnerLogValid :
    leaf6788InnerLog.Valid 8 (innerAD leaf6788Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6788CoverageChecked

private noncomputable def leaf6788InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814841/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6788InputLogOnePlusV_eq :
    leaf6788InputLogOnePlusV = outerEnclosure 24
      (leaf6788Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6788RoundedFacts : LeafRoundedFacts 8
    leaf6788Certificate.logOnePlusV leaf6788InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6788InputLogOnePlusV_eq }

private noncomputable def leaf6788Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi332InputQChi innerPair368Input
    leaf6788InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6788LowerChecked :
    lowerCheck 24 leaf6788Box leaf6788Inputs = true := by
  rfl'

private theorem leaf6788CoversExact : CoversExact 8
    leaf6788Box leaf6788Certificate leaf6788InnerLog leaf6788Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi332RoundedFacts
    innerPair368RoundedFacts leaf6788RoundedFacts (by rfl)

private theorem leaf6788FlatSound : Sound leaf6788Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6788CertificateValid
    leaf6788InnerLogValid leaf6788CoversExact leaf6788LowerChecked

private noncomputable def leaf6789Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6789Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711399424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (773326383/536870912) }, upper := { exponent := 1, mantissa := (749/512) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427795965/137422798848) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6789InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6789LocalValidity :
    LeafFacts leaf6789Box leaf6789Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6789Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711399424) }) = true
      norm_num [leaf6789Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6789CertificateValid :
    WideCertificateValid leaf6789Box leaf6789Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi332ValidityFacts
    leaf6789LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6789CoverageChecked :
    coverageCheck (innerAD leaf6789Box) leaf6789InnerLog = true := by
  rfl'

private theorem leaf6789InnerLogValid :
    leaf6789InnerLog.Valid 8 (innerAD leaf6789Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6789CoverageChecked

private noncomputable def leaf6789InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629691/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6789InputLogOnePlusV_eq :
    leaf6789InputLogOnePlusV = outerEnclosure 24
      (leaf6789Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6789RoundedFacts : LeafRoundedFacts 8
    leaf6789Certificate.logOnePlusV leaf6789InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6789InputLogOnePlusV_eq }

private noncomputable def leaf6789Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi332InputQChi innerPair371Input
    leaf6789InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6789LowerChecked :
    lowerCheck 24 leaf6789Box leaf6789Inputs = true := by
  rfl'

private theorem leaf6789CoversExact : CoversExact 8
    leaf6789Box leaf6789Certificate leaf6789InnerLog leaf6789Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi332RoundedFacts
    innerPair371RoundedFacts leaf6789RoundedFacts (by rfl)

private theorem leaf6789FlatSound : Sound leaf6789Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6789CertificateValid
    leaf6789InnerLogValid leaf6789CoversExact leaf6789LowerChecked

private noncomputable def leaf6790Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6790Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711689216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (754911895/536870912) }, upper := { exponent := 1, mantissa := (11701/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428085757/137423378432) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6790InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6790LocalValidity :
    LeafFacts leaf6790Box leaf6790Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6790Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711689216) }) = true
      norm_num [leaf6790Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6790CertificateValid :
    WideCertificateValid leaf6790Box leaf6790Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi329ValidityFacts
    leaf6790LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6790CoverageChecked :
    coverageCheck (innerAD leaf6790Box) leaf6790InnerLog = true := by
  rfl'

private theorem leaf6790InnerLogValid :
    leaf6790InnerLog.Valid 8 (innerAD leaf6790Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6790CoverageChecked

private noncomputable def leaf6790InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629655/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6790InputLogOnePlusV_eq :
    leaf6790InputLogOnePlusV = outerEnclosure 24
      (leaf6790Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6790RoundedFacts : LeafRoundedFacts 8
    leaf6790Certificate.logOnePlusV leaf6790InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6790InputLogOnePlusV_eq }

private noncomputable def leaf6790Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi329InputQChi innerPair357Input
    leaf6790InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6790LowerChecked :
    lowerCheck 24 leaf6790Box leaf6790Inputs = true := by
  rfl'

private theorem leaf6790CoversExact : CoversExact 8
    leaf6790Box leaf6790Certificate leaf6790InnerLog leaf6790Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi329RoundedFacts
    innerPair357RoundedFacts leaf6790RoundedFacts (by rfl)

private theorem leaf6790FlatSound : Sound leaf6790Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6790CertificateValid
    leaf6790InnerLogValid leaf6790CoversExact leaf6790LowerChecked

private noncomputable def leaf6791Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6791Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711622656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (759105941/536870912) }, upper := { exponent := 1, mantissa := (5883/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137428019197/137423245312) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6791InnerLog : WideLogData :=
  innerPair367Data

set_option maxRecDepth 1000000 in
private theorem leaf6791LocalValidity :
    LeafFacts leaf6791Box leaf6791Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6791Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711622656) }) = true
      norm_num [leaf6791Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6791CertificateValid :
    WideCertificateValid leaf6791Box leaf6791Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi329ValidityFacts
    leaf6791LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6791CoverageChecked :
    coverageCheck (innerAD leaf6791Box) leaf6791InnerLog = true := by
  rfl'

private theorem leaf6791InnerLogValid :
    leaf6791InnerLog.Valid 8 (innerAD leaf6791Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint97PositiveFacts.valid leaf6791CoverageChecked

private noncomputable def leaf6791InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363427/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6791InputLogOnePlusV_eq :
    leaf6791InputLogOnePlusV = outerEnclosure 24
      (leaf6791Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6791RoundedFacts : LeafRoundedFacts 8
    leaf6791Certificate.logOnePlusV leaf6791InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6791InputLogOnePlusV_eq }

private noncomputable def leaf6791Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi329InputQChi innerPair367Input
    leaf6791InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6791LowerChecked :
    lowerCheck 24 leaf6791Box leaf6791Inputs = true := by
  rfl'

private theorem leaf6791CoversExact : CoversExact 8
    leaf6791Box leaf6791Certificate leaf6791InnerLog leaf6791Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi329RoundedFacts
    innerPair367RoundedFacts leaf6791RoundedFacts (by rfl)

private theorem leaf6791FlatSound : Sound leaf6791Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6791CertificateValid
    leaf6791InnerLogValid leaf6791CoversExact leaf6791LowerChecked

private noncomputable def leaf6792Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6792Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (4042140973/4041857024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (762513605/536870912) }, upper := { exponent := 1, mantissa := (5909/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8083997997/8083714048) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6792InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6792LocalValidity :
    LeafFacts leaf6792Box leaf6792Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6792Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042140973/4041857024) }) = true
      norm_num [leaf6792Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6792CertificateValid :
    WideCertificateValid leaf6792Box leaf6792Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi330ValidityFacts
    leaf6792LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6792CoverageChecked :
    coverageCheck (innerAD leaf6792Box) leaf6792InnerLog = true := by
  rfl'

private theorem leaf6792InnerLogValid :
    leaf6792InnerLog.Valid 8 (innerAD leaf6792Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6792CoverageChecked

private noncomputable def leaf6792InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814835/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6792InputLogOnePlusV_eq :
    leaf6792InputLogOnePlusV = outerEnclosure 24
      (leaf6792Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6792RoundedFacts : LeafRoundedFacts 8
    leaf6792Certificate.logOnePlusV leaf6792InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6792InputLogOnePlusV_eq }

private noncomputable def leaf6792Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi330InputQChi innerPair368Input
    leaf6792InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6792LowerChecked :
    lowerCheck 24 leaf6792Box leaf6792Inputs = true := by
  rfl'

private theorem leaf6792CoversExact : CoversExact 8
    leaf6792Box leaf6792Certificate leaf6792InnerLog leaf6792Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi330RoundedFacts
    innerPair368RoundedFacts leaf6792RoundedFacts (by rfl)

private theorem leaf6792FlatSound : Sound leaf6792Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6792CertificateValid
    leaf6792InnerLogValid leaf6792CoversExact leaf6792LowerChecked

private noncomputable def leaf6793Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6793Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711501824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (766773183/536870912) }, upper := { exponent := 1, mantissa := (2971/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427898365/137423003648) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6793InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6793LocalValidity :
    LeafFacts leaf6793Box leaf6793Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6793Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711501824) }) = true
      norm_num [leaf6793Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6793CertificateValid :
    WideCertificateValid leaf6793Box leaf6793Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi330ValidityFacts
    leaf6793LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6793CoverageChecked :
    coverageCheck (innerAD leaf6793Box) leaf6793InnerLog = true := by
  rfl'

private theorem leaf6793InnerLogValid :
    leaf6793InnerLog.Valid 8 (innerAD leaf6793Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6793CoverageChecked

private noncomputable def leaf6793InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814839/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6793InputLogOnePlusV_eq :
    leaf6793InputLogOnePlusV = outerEnclosure 24
      (leaf6793Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6793RoundedFacts : LeafRoundedFacts 8
    leaf6793Certificate.logOnePlusV leaf6793InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6793InputLogOnePlusV_eq }

private noncomputable def leaf6793Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi330InputQChi innerPair368Input
    leaf6793InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6793LowerChecked :
    lowerCheck 24 leaf6793Box leaf6793Inputs = true := by
  rfl'

private theorem leaf6793CoversExact : CoversExact 8
    leaf6793Box leaf6793Certificate leaf6793InnerLog leaf6793Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi330RoundedFacts
    innerPair368RoundedFacts leaf6793RoundedFacts (by rfl)

private theorem leaf6793FlatSound : Sound leaf6793Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6793CertificateValid
    leaf6793InnerLogValid leaf6793CoversExact leaf6793LowerChecked

private noncomputable def leaf6794Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6794Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711556096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (763299987/536870912) }, upper := { exponent := 1, mantissa := (11831/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427952637/137423112192) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6794InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6794LocalValidity :
    LeafFacts leaf6794Box leaf6794Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6794Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711556096) }) = true
      norm_num [leaf6794Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6794CertificateValid :
    WideCertificateValid leaf6794Box leaf6794Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi329ValidityFacts
    leaf6794LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6794CoverageChecked :
    coverageCheck (innerAD leaf6794Box) leaf6794InnerLog = true := by
  rfl'

private theorem leaf6794InnerLogValid :
    leaf6794InnerLog.Valid 8 (innerAD leaf6794Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6794CoverageChecked

private noncomputable def leaf6794InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453709/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6794InputLogOnePlusV_eq :
    leaf6794InputLogOnePlusV = outerEnclosure 24
      (leaf6794Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6794RoundedFacts : LeafRoundedFacts 8
    leaf6794Certificate.logOnePlusV leaf6794InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6794InputLogOnePlusV_eq }

private noncomputable def leaf6794Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi329InputQChi innerPair368Input
    leaf6794InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6794LowerChecked :
    lowerCheck 24 leaf6794Box leaf6794Inputs = true := by
  rfl'

private theorem leaf6794CoversExact : CoversExact 8
    leaf6794Box leaf6794Certificate leaf6794InnerLog leaf6794Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi329RoundedFacts
    innerPair368RoundedFacts leaf6794RoundedFacts (by rfl)

private theorem leaf6794FlatSound : Sound leaf6794Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6794CertificateValid
    leaf6794InnerLogValid leaf6794CoversExact leaf6794LowerChecked

private noncomputable def leaf6795Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6795Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711489536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (767494033/536870912) }, upper := { exponent := 1, mantissa := (1487/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427886077/137422979072) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6795InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6795LocalValidity :
    LeafFacts leaf6795Box leaf6795Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6795Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711489536) }) = true
      norm_num [leaf6795Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6795CertificateValid :
    WideCertificateValid leaf6795Box leaf6795Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi329ValidityFacts
    leaf6795LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6795CoverageChecked :
    coverageCheck (innerAD leaf6795Box) leaf6795InnerLog = true := by
  rfl'

private theorem leaf6795InnerLogValid :
    leaf6795InnerLog.Valid 8 (innerAD leaf6795Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6795CoverageChecked

private noncomputable def leaf6795InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726855/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6795InputLogOnePlusV_eq :
    leaf6795InputLogOnePlusV = outerEnclosure 24
      (leaf6795Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6795RoundedFacts : LeafRoundedFacts 8
    leaf6795Certificate.logOnePlusV leaf6795InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6795InputLogOnePlusV_eq }

private noncomputable def leaf6795Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi329InputQChi innerPair368Input
    leaf6795InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6795LowerChecked :
    lowerCheck 24 leaf6795Box leaf6795Inputs = true := by
  rfl'

private theorem leaf6795CoversExact : CoversExact 8
    leaf6795Box leaf6795Certificate leaf6795InnerLog leaf6795Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi329RoundedFacts
    innerPair368RoundedFacts leaf6795RoundedFacts (by rfl)

private theorem leaf6795FlatSound : Sound leaf6795Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6795CertificateValid
    leaf6795InnerLogValid leaf6795CoversExact leaf6795LowerChecked

private noncomputable def leaf6796Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6796Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711434240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (771032761/536870912) }, upper := { exponent := 1, mantissa := (5975/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427830781/137422868480) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6796InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6796LocalValidity :
    LeafFacts leaf6796Box leaf6796Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6796Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711434240) }) = true
      norm_num [leaf6796Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6796CertificateValid :
    WideCertificateValid leaf6796Box leaf6796Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi330ValidityFacts
    leaf6796LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6796CoverageChecked :
    coverageCheck (innerAD leaf6796Box) leaf6796InnerLog = true := by
  rfl'

private theorem leaf6796InnerLogValid :
    leaf6796InnerLog.Valid 8 (innerAD leaf6796Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6796CoverageChecked

private noncomputable def leaf6796InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629687/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6796InputLogOnePlusV_eq :
    leaf6796InputLogOnePlusV = outerEnclosure 24
      (leaf6796Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6796RoundedFacts : LeafRoundedFacts 8
    leaf6796Certificate.logOnePlusV leaf6796InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6796InputLogOnePlusV_eq }

private noncomputable def leaf6796Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi330InputQChi innerPair368Input
    leaf6796InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6796LowerChecked :
    lowerCheck 24 leaf6796Box leaf6796Inputs = true := by
  rfl'

private theorem leaf6796CoversExact : CoversExact 8
    leaf6796Box leaf6796Certificate leaf6796InnerLog leaf6796Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi330RoundedFacts
    innerPair368RoundedFacts leaf6796RoundedFacts (by rfl)

private theorem leaf6796FlatSound : Sound leaf6796Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6796CertificateValid
    leaf6796InnerLogValid leaf6796CoversExact leaf6796LowerChecked

private noncomputable def leaf6797Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6797Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711366656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (775292339/536870912) }, upper := { exponent := 1, mantissa := (751/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427763197/137422733312) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6797InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6797LocalValidity :
    LeafFacts leaf6797Box leaf6797Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6797Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711366656) }) = true
      norm_num [leaf6797Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6797CertificateValid :
    WideCertificateValid leaf6797Box leaf6797Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi330ValidityFacts
    leaf6797LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6797CoverageChecked :
    coverageCheck (innerAD leaf6797Box) leaf6797InnerLog = true := by
  rfl'

private theorem leaf6797InnerLogValid :
    leaf6797InnerLog.Valid 8 (innerAD leaf6797Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6797CoverageChecked

private noncomputable def leaf6797InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629695/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6797InputLogOnePlusV_eq :
    leaf6797InputLogOnePlusV = outerEnclosure 24
      (leaf6797Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6797RoundedFacts : LeafRoundedFacts 8
    leaf6797Certificate.logOnePlusV leaf6797InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6797InputLogOnePlusV_eq }

private noncomputable def leaf6797Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi330InputQChi innerPair371Input
    leaf6797InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6797LowerChecked :
    lowerCheck 24 leaf6797Box leaf6797Inputs = true := by
  rfl'

private theorem leaf6797CoversExact : CoversExact 8
    leaf6797Box leaf6797Certificate leaf6797InnerLog leaf6797Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi330RoundedFacts
    innerPair371RoundedFacts leaf6797RoundedFacts (by rfl)

private theorem leaf6797FlatSound : Sound leaf6797Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6797CertificateValid
    leaf6797InnerLogValid leaf6797CoversExact leaf6797LowerChecked

private noncomputable def leaf6798Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6798Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711449600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (770115315/536870912) }, upper := { exponent := 1, mantissa := (11935/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427846141/137422899200) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6798InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6798LocalValidity :
    LeafFacts leaf6798Box leaf6798Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6798Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711449600) }) = true
      norm_num [leaf6798Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6798CertificateValid :
    WideCertificateValid leaf6798Box leaf6798Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi331ValidityFacts
    leaf6798LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6798CoverageChecked :
    coverageCheck (innerAD leaf6798Box) leaf6798InnerLog = true := by
  rfl'

private theorem leaf6798InnerLogValid :
    leaf6798InnerLog.Valid 8 (innerAD leaf6798Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6798CoverageChecked

private noncomputable def leaf6798InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629685/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6798InputLogOnePlusV_eq :
    leaf6798InputLogOnePlusV = outerEnclosure 24
      (leaf6798Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6798RoundedFacts : LeafRoundedFacts 8
    leaf6798Certificate.logOnePlusV leaf6798InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6798InputLogOnePlusV_eq }

private noncomputable def leaf6798Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi331InputQChi innerPair368Input
    leaf6798InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6798LowerChecked :
    lowerCheck 24 leaf6798Box leaf6798Inputs = true := by
  rfl'

private theorem leaf6798CoversExact : CoversExact 8
    leaf6798Box leaf6798Certificate leaf6798InnerLog leaf6798Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi331RoundedFacts
    innerPair368RoundedFacts leaf6798RoundedFacts (by rfl)

private theorem leaf6798FlatSound : Sound leaf6798Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6798CertificateValid
    leaf6798InnerLogValid leaf6798CoversExact leaf6798LowerChecked

private noncomputable def leaf6799Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6799Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711380992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (774440425/536870912) }, upper := { exponent := 1, mantissa := (6001/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427777533/137422761984) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6799InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6799LocalValidity :
    LeafFacts leaf6799Box leaf6799Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6799Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711380992) }) = true
      norm_num [leaf6799Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6799CertificateValid :
    WideCertificateValid leaf6799Box leaf6799Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi331ValidityFacts
    leaf6799LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6799CoverageChecked :
    coverageCheck (innerAD leaf6799Box) leaf6799InnerLog = true := by
  rfl'

private theorem leaf6799InnerLogValid :
    leaf6799InnerLog.Valid 8 (innerAD leaf6799Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6799CoverageChecked

private noncomputable def leaf6799InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629693/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6799InputLogOnePlusV_eq :
    leaf6799InputLogOnePlusV = outerEnclosure 24
      (leaf6799Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6799RoundedFacts : LeafRoundedFacts 8
    leaf6799Certificate.logOnePlusV leaf6799InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6799InputLogOnePlusV_eq }

private noncomputable def leaf6799Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi331InputQChi innerPair371Input
    leaf6799InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6799LowerChecked :
    lowerCheck 24 leaf6799Box leaf6799Inputs = true := by
  rfl'

private theorem leaf6799CoversExact : CoversExact 8
    leaf6799Box leaf6799Certificate leaf6799InnerLog leaf6799Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi331RoundedFacts
    innerPair371RoundedFacts leaf6799RoundedFacts (by rfl)

private theorem leaf6799FlatSound : Sound leaf6799Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6799CertificateValid
    leaf6799InnerLogValid leaf6799CoversExact leaf6799LowerChecked

private noncomputable def leaf6800Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6800Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711329792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (777717025/536870912) }, upper := { exponent := 1, mantissa := (3013/2048) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427726333/137422659584) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6800InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6800LocalValidity :
    LeafFacts leaf6800Box leaf6800Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6800Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711329792) }) = true
      norm_num [leaf6800Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6800CertificateValid :
    WideCertificateValid leaf6800Box leaf6800Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi332ValidityFacts
    leaf6800LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6800CoverageChecked :
    coverageCheck (innerAD leaf6800Box) leaf6800InnerLog = true := by
  rfl'

private theorem leaf6800InnerLogValid :
    leaf6800InnerLog.Valid 8 (innerAD leaf6800Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6800CoverageChecked

private noncomputable def leaf6800InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629699/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6800InputLogOnePlusV_eq :
    leaf6800InputLogOnePlusV = outerEnclosure 24
      (leaf6800Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6800RoundedFacts : LeafRoundedFacts 8
    leaf6800Certificate.logOnePlusV leaf6800InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6800InputLogOnePlusV_eq }

private noncomputable def leaf6800Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi332InputQChi innerPair372Input
    leaf6800InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6800LowerChecked :
    lowerCheck 24 leaf6800Box leaf6800Inputs = true := by
  rfl'

private theorem leaf6800CoversExact : CoversExact 8
    leaf6800Box leaf6800Certificate leaf6800InnerLog leaf6800Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi332RoundedFacts
    innerPair372RoundedFacts leaf6800RoundedFacts (by rfl)

private theorem leaf6800FlatSound : Sound leaf6800Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6800CertificateValid
    leaf6800InnerLogValid leaf6800CoversExact leaf6800LowerChecked

private noncomputable def leaf6801Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6801Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711260160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (782107667/536870912) }, upper := { exponent := 1, mantissa := (1515/1024) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427656701/137422520320) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6801InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6801LocalValidity :
    LeafFacts leaf6801Box leaf6801Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6801Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711260160) }) = true
      norm_num [leaf6801Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6801CertificateValid :
    WideCertificateValid leaf6801Box leaf6801Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi332ValidityFacts
    leaf6801LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6801CoverageChecked :
    coverageCheck (innerAD leaf6801Box) leaf6801InnerLog = true := by
  rfl'

private theorem leaf6801InnerLogValid :
    leaf6801InnerLog.Valid 8 (innerAD leaf6801Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6801CoverageChecked

private noncomputable def leaf6801InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907427/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6801InputLogOnePlusV_eq :
    leaf6801InputLogOnePlusV = outerEnclosure 24
      (leaf6801Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6801RoundedFacts : LeafRoundedFacts 8
    leaf6801Certificate.logOnePlusV leaf6801InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6801InputLogOnePlusV_eq }

private noncomputable def leaf6801Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi332InputQChi innerPair372Input
    leaf6801InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6801LowerChecked :
    lowerCheck 24 leaf6801Box leaf6801Inputs = true := by
  rfl'

private theorem leaf6801CoversExact : CoversExact 8
    leaf6801Box leaf6801Certificate leaf6801InnerLog leaf6801Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi332RoundedFacts
    innerPair372RoundedFacts leaf6801RoundedFacts (by rfl)

private theorem leaf6801FlatSound : Sound leaf6801Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6801CertificateValid
    leaf6801InnerLogValid leaf6801CoversExact leaf6801LowerChecked

private noncomputable def leaf6802Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6802Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (5285876657/5285485568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (778765535/536870912) }, upper := { exponent := 1, mantissa := (12069/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10571362225/10570971136) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6802InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6802LocalValidity :
    LeafFacts leaf6802Box leaf6802Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6802Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5285876657/5285485568) }) = true
      norm_num [leaf6802Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6802CertificateValid :
    WideCertificateValid leaf6802Box leaf6802Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi331ValidityFacts
    leaf6802LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6802CoverageChecked :
    coverageCheck (innerAD leaf6802Box) leaf6802InnerLog = true := by
  rfl'

private theorem leaf6802InnerLogValid :
    leaf6802InnerLog.Valid 8 (innerAD leaf6802Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6802CoverageChecked

private noncomputable def leaf6802InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629701/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6802InputLogOnePlusV_eq :
    leaf6802InputLogOnePlusV = outerEnclosure 24
      (leaf6802Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6802RoundedFacts : LeafRoundedFacts 8
    leaf6802Certificate.logOnePlusV leaf6802InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6802InputLogOnePlusV_eq }

private noncomputable def leaf6802Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi331InputQChi innerPair372Input
    leaf6802InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6802LowerChecked :
    lowerCheck 24 leaf6802Box leaf6802Inputs = true := by
  rfl'

private theorem leaf6802CoversExact : CoversExact 8
    leaf6802Box leaf6802Certificate leaf6802InnerLog leaf6802Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi331RoundedFacts
    innerPair372RoundedFacts leaf6802RoundedFacts (by rfl)

private theorem leaf6802FlatSound : Sound leaf6802Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6802CertificateValid
    leaf6802InnerLogValid leaf6802CoversExact leaf6802LowerChecked

private noncomputable def leaf6803Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6803Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711243776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (783090645/536870912) }, upper := { exponent := 1, mantissa := (1517/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427640317/137422487552) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6803InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6803LocalValidity :
    LeafFacts leaf6803Box leaf6803Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6803Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711243776) }) = true
      norm_num [leaf6803Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6803CertificateValid :
    WideCertificateValid leaf6803Box leaf6803Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi331ValidityFacts
    leaf6803LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6803CoverageChecked :
    coverageCheck (innerAD leaf6803Box) leaf6803InnerLog = true := by
  rfl'

private theorem leaf6803InnerLogValid :
    leaf6803InnerLog.Valid 8 (innerAD leaf6803Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6803CoverageChecked

private noncomputable def leaf6803InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814855/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6803InputLogOnePlusV_eq :
    leaf6803InputLogOnePlusV = outerEnclosure 24
      (leaf6803Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6803RoundedFacts : LeafRoundedFacts 8
    leaf6803Certificate.logOnePlusV leaf6803InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6803InputLogOnePlusV_eq }

private noncomputable def leaf6803Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi331InputQChi innerPair372Input
    leaf6803InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6803LowerChecked :
    lowerCheck 24 leaf6803Box leaf6803Inputs = true := by
  rfl'

private theorem leaf6803CoversExact : CoversExact 8
    leaf6803Box leaf6803Certificate leaf6803InnerLog leaf6803Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi331RoundedFacts
    innerPair372RoundedFacts leaf6803RoundedFacts (by rfl)

private theorem leaf6803FlatSound : Sound leaf6803Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6803CertificateValid
    leaf6803InnerLogValid leaf6803CoversExact leaf6803LowerChecked

private noncomputable def leaf6804Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6804Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711190528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (786498309/536870912) }, upper := { exponent := 1, mantissa := (3047/2048) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427587069/137422381056) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6804InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6804LocalValidity :
    LeafFacts leaf6804Box leaf6804Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6804Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711190528) }) = true
      norm_num [leaf6804Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6804CertificateValid :
    WideCertificateValid leaf6804Box leaf6804Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi332ValidityFacts
    leaf6804LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6804CoverageChecked :
    coverageCheck (innerAD leaf6804Box) leaf6804InnerLog = true := by
  rfl'

private theorem leaf6804InnerLogValid :
    leaf6804InnerLog.Valid 8 (innerAD leaf6804Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6804CoverageChecked

private noncomputable def leaf6804InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907429/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6804InputLogOnePlusV_eq :
    leaf6804InputLogOnePlusV = outerEnclosure 24
      (leaf6804Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6804RoundedFacts : LeafRoundedFacts 8
    leaf6804Certificate.logOnePlusV leaf6804InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6804InputLogOnePlusV_eq }

private noncomputable def leaf6804Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi332InputQChi innerPair372Input
    leaf6804InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6804LowerChecked :
    lowerCheck 24 leaf6804Box leaf6804Inputs = true := by
  rfl'

private theorem leaf6804CoversExact : CoversExact 8
    leaf6804Box leaf6804Certificate leaf6804InnerLog leaf6804Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi332RoundedFacts
    innerPair372RoundedFacts leaf6804RoundedFacts (by rfl)

private theorem leaf6804FlatSound : Sound leaf6804Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6804CertificateValid
    leaf6804InnerLogValid leaf6804CoversExact leaf6804LowerChecked

private noncomputable def leaf6805Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6805Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (135266433/135258112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (790888951/536870912) }, upper := { exponent := 1, mantissa := (383/256) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (270524545/270516224) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6805InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6805LocalValidity :
    LeafFacts leaf6805Box leaf6805Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6805Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (135266433/135258112) }) = true
      norm_num [leaf6805Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6805CertificateValid :
    WideCertificateValid leaf6805Box leaf6805Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi332ValidityFacts
    leaf6805LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6805CoverageChecked :
    coverageCheck (innerAD leaf6805Box) leaf6805InnerLog = true := by
  rfl'

private theorem leaf6805InnerLogValid :
    leaf6805InnerLog.Valid 8 (innerAD leaf6805Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6805CoverageChecked

private noncomputable def leaf6805InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6805InputLogOnePlusV_eq :
    leaf6805InputLogOnePlusV = outerEnclosure 24
      (leaf6805Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6805RoundedFacts : LeafRoundedFacts 8
    leaf6805Certificate.logOnePlusV leaf6805InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6805InputLogOnePlusV_eq }

private noncomputable def leaf6805Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi332InputQChi innerPair375Input
    leaf6805InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6805LowerChecked :
    lowerCheck 24 leaf6805Box leaf6805Inputs = true := by
  rfl'

private theorem leaf6805CoversExact : CoversExact 8
    leaf6805Box leaf6805Certificate leaf6805InnerLog leaf6805Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi332RoundedFacts
    innerPair375RoundedFacts leaf6805RoundedFacts (by rfl)

private theorem leaf6805FlatSound : Sound leaf6805Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6805CertificateValid
    leaf6805InnerLogValid leaf6805CoversExact leaf6805LowerChecked

private noncomputable def leaf6806Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6806Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435819/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711492608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (767494039/536870912) }, upper := { exponent := 1, mantissa := (11893/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427889149/137422985216) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6806InnerLog : WideLogData :=
  innerPair368Data

set_option maxRecDepth 1000000 in
private theorem leaf6806LocalValidity :
    LeafFacts leaf6806Box leaf6806Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6806Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711492608) }) = true
      norm_num [leaf6806Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6806CertificateValid :
    WideCertificateValid leaf6806Box leaf6806Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi327ValidityFacts
    leaf6806LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6806CoverageChecked :
    coverageCheck (innerAD leaf6806Box) leaf6806InnerLog = true := by
  rfl'

private theorem leaf6806InnerLogValid :
    leaf6806InnerLog.Valid 8 (innerAD leaf6806Box) :=
  wideLogDataValid_of_cachedCheck endpoint96PositiveFacts
    endpoint98PositiveFacts.valid leaf6806CoverageChecked

private noncomputable def leaf6806InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629679/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6806InputLogOnePlusV_eq :
    leaf6806InputLogOnePlusV = outerEnclosure 24
      (leaf6806Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6806RoundedFacts : LeafRoundedFacts 8
    leaf6806Certificate.logOnePlusV leaf6806InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6806InputLogOnePlusV_eq }

private noncomputable def leaf6806Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi327InputQChi innerPair368Input
    leaf6806InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6806LowerChecked :
    lowerCheck 24 leaf6806Box leaf6806Inputs = true := by
  rfl'

private theorem leaf6806CoversExact : CoversExact 8
    leaf6806Box leaf6806Certificate leaf6806InnerLog leaf6806Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi327RoundedFacts
    innerPair368RoundedFacts leaf6806RoundedFacts (by rfl)

private theorem leaf6806FlatSound : Sound leaf6806Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6806CertificateValid
    leaf6806InnerLogValid leaf6806CoversExact leaf6806LowerChecked

private noncomputable def leaf6807Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6807Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711421952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (771950213/536870912) }, upper := { exponent := 1, mantissa := (5981/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427818493/137422843904) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6807InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6807LocalValidity :
    LeafFacts leaf6807Box leaf6807Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6807Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711421952) }) = true
      norm_num [leaf6807Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6807CertificateValid :
    WideCertificateValid leaf6807Box leaf6807Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi327ValidityFacts
    leaf6807LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6807CoverageChecked :
    coverageCheck (innerAD leaf6807Box) leaf6807InnerLog = true := by
  rfl'

private theorem leaf6807InnerLogValid :
    leaf6807InnerLog.Valid 8 (innerAD leaf6807Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6807CoverageChecked

private noncomputable def leaf6807InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453711/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6807InputLogOnePlusV_eq :
    leaf6807InputLogOnePlusV = outerEnclosure 24
      (leaf6807Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6807RoundedFacts : LeafRoundedFacts 8
    leaf6807Certificate.logOnePlusV leaf6807InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6807InputLogOnePlusV_eq }

private noncomputable def leaf6807Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi327InputQChi innerPair371Input
    leaf6807InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6807LowerChecked :
    lowerCheck 24 leaf6807Box leaf6807Inputs = true := by
  rfl'

private theorem leaf6807CoversExact : CoversExact 8
    leaf6807Box leaf6807Certificate leaf6807InnerLog leaf6807Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi327RoundedFacts
    innerPair371RoundedFacts leaf6807RoundedFacts (by rfl)

private theorem leaf6807FlatSound : Sound leaf6807Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6807CertificateValid
    leaf6807InnerLogValid leaf6807CoversExact leaf6807LowerChecked

private noncomputable def leaf6808Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6808Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435821/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711376896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (774833621/536870912) }, upper := { exponent := 1, mantissa := (6003/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427773437/137422753792) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6808InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6808LocalValidity :
    LeafFacts leaf6808Box leaf6808Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6808Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711376896) }) = true
      norm_num [leaf6808Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6808CertificateValid :
    WideCertificateValid leaf6808Box leaf6808Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi328ValidityFacts
    leaf6808LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6808CoverageChecked :
    coverageCheck (innerAD leaf6808Box) leaf6808InnerLog = true := by
  rfl'

private theorem leaf6808InnerLogValid :
    leaf6808InnerLog.Valid 8 (innerAD leaf6808Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6808CoverageChecked

private noncomputable def leaf6808InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814847/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6808InputLogOnePlusV_eq :
    leaf6808InputLogOnePlusV = outerEnclosure 24
      (leaf6808Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6808RoundedFacts : LeafRoundedFacts 8
    leaf6808Certificate.logOnePlusV leaf6808InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6808InputLogOnePlusV_eq }

private noncomputable def leaf6808Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi328InputQChi innerPair371Input
    leaf6808InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6808LowerChecked :
    lowerCheck 24 leaf6808Box leaf6808Inputs = true := by
  rfl'

private theorem leaf6808CoversExact : CoversExact 8
    leaf6808Box leaf6808Certificate leaf6808InnerLog leaf6808Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi328RoundedFacts
    innerPair371RoundedFacts leaf6808RoundedFacts (by rfl)

private theorem leaf6808FlatSound : Sound leaf6808Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6808CertificateValid
    leaf6808InnerLogValid leaf6808CoversExact leaf6808LowerChecked

private noncomputable def leaf6809Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6809Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711305216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (779355327/536870912) }, upper := { exponent := 1, mantissa := (3019/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427701757/137422610432) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6809InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6809LocalValidity :
    LeafFacts leaf6809Box leaf6809Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6809Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711305216) }) = true
      norm_num [leaf6809Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6809CertificateValid :
    WideCertificateValid leaf6809Box leaf6809Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi328ValidityFacts
    leaf6809LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6809CoverageChecked :
    coverageCheck (innerAD leaf6809Box) leaf6809InnerLog = true := by
  rfl'

private theorem leaf6809InnerLogValid :
    leaf6809InnerLog.Valid 8 (innerAD leaf6809Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6809CoverageChecked

private noncomputable def leaf6809InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814851/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6809InputLogOnePlusV_eq :
    leaf6809InputLogOnePlusV = outerEnclosure 24
      (leaf6809Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6809RoundedFacts : LeafRoundedFacts 8
    leaf6809Certificate.logOnePlusV leaf6809InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6809InputLogOnePlusV_eq }

private noncomputable def leaf6809Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi328InputQChi innerPair372Input
    leaf6809InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6809LowerChecked :
    lowerCheck 24 leaf6809Box leaf6809Inputs = true := by
  rfl'

private theorem leaf6809CoversExact : CoversExact 8
    leaf6809Box leaf6809Certificate leaf6809InnerLog leaf6809Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi328RoundedFacts
    innerPair372RoundedFacts leaf6809RoundedFacts (by rfl)

private theorem leaf6809FlatSound : Sound leaf6809Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6809CertificateValid
    leaf6809InnerLogValid leaf6809CoversExact leaf6809LowerChecked

private noncomputable def leaf6810Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6810Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711351296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (776406387/536870912) }, upper := { exponent := 1, mantissa := (12031/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427747837/137422702592) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6810InnerLog : WideLogData :=
  innerPair371Data

set_option maxRecDepth 1000000 in
private theorem leaf6810LocalValidity :
    LeafFacts leaf6810Box leaf6810Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6810Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711351296) }) = true
      norm_num [leaf6810Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6810CertificateValid :
    WideCertificateValid leaf6810Box leaf6810Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi327ValidityFacts
    leaf6810LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6810CoverageChecked :
    coverageCheck (innerAD leaf6810Box) leaf6810InnerLog = true := by
  rfl'

private theorem leaf6810InnerLogValid :
    leaf6810InnerLog.Valid 8 (innerAD leaf6810Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint98PositiveFacts.valid leaf6810CoverageChecked

private noncomputable def leaf6810InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629697/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6810InputLogOnePlusV_eq :
    leaf6810InputLogOnePlusV = outerEnclosure 24
      (leaf6810Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6810RoundedFacts : LeafRoundedFacts 8
    leaf6810Certificate.logOnePlusV leaf6810InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6810InputLogOnePlusV_eq }

private noncomputable def leaf6810Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi327InputQChi innerPair371Input
    leaf6810InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6810LowerChecked :
    lowerCheck 24 leaf6810Box leaf6810Inputs = true := by
  rfl'

private theorem leaf6810CoversExact : CoversExact 8
    leaf6810Box leaf6810Certificate leaf6810InnerLog leaf6810Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi327RoundedFacts
    innerPair371RoundedFacts leaf6810RoundedFacts (by rfl)

private theorem leaf6810FlatSound : Sound leaf6810Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6810CertificateValid
    leaf6810InnerLogValid leaf6810CoversExact leaf6810LowerChecked

private noncomputable def leaf6811Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6811Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711280640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (780862561/536870912) }, upper := { exponent := 1, mantissa := (3025/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427677181/137422561280) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6811InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6811LocalValidity :
    LeafFacts leaf6811Box leaf6811Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6811Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711280640) }) = true
      norm_num [leaf6811Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6811CertificateValid :
    WideCertificateValid leaf6811Box leaf6811Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi327ValidityFacts
    leaf6811LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6811CoverageChecked :
    coverageCheck (innerAD leaf6811Box) leaf6811InnerLog = true := by
  rfl'

private theorem leaf6811InnerLogValid :
    leaf6811InnerLog.Valid 8 (innerAD leaf6811Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6811CoverageChecked

private noncomputable def leaf6811InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6811InputLogOnePlusV_eq :
    leaf6811InputLogOnePlusV = outerEnclosure 24
      (leaf6811Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6811RoundedFacts : LeafRoundedFacts 8
    leaf6811Certificate.logOnePlusV leaf6811InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6811InputLogOnePlusV_eq }

private noncomputable def leaf6811Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi327InputQChi innerPair372Input
    leaf6811InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6811LowerChecked :
    lowerCheck 24 leaf6811Box leaf6811Inputs = true := by
  rfl'

private theorem leaf6811CoversExact : CoversExact 8
    leaf6811Box leaf6811Certificate leaf6811InnerLog leaf6811Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi327RoundedFacts
    innerPair372RoundedFacts leaf6811RoundedFacts (by rfl)

private theorem leaf6811FlatSound : Sound leaf6811Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6811CertificateValid
    leaf6811InnerLogValid leaf6811CoversExact leaf6811LowerChecked

private noncomputable def leaf6812Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6812Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711233536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (783877033/536870912) }, upper := { exponent := 1, mantissa := (6073/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427630077/137422467072) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6812InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6812LocalValidity :
    LeafFacts leaf6812Box leaf6812Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6812Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711233536) }) = true
      norm_num [leaf6812Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6812CertificateValid :
    WideCertificateValid leaf6812Box leaf6812Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi328ValidityFacts
    leaf6812LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6812CoverageChecked :
    coverageCheck (innerAD leaf6812Box) leaf6812InnerLog = true := by
  rfl'

private theorem leaf6812InnerLogValid :
    leaf6812InnerLog.Valid 8 (innerAD leaf6812Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6812CoverageChecked

private noncomputable def leaf6812InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629711/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6812InputLogOnePlusV_eq :
    leaf6812InputLogOnePlusV = outerEnclosure 24
      (leaf6812Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6812RoundedFacts : LeafRoundedFacts 8
    leaf6812Certificate.logOnePlusV leaf6812InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6812InputLogOnePlusV_eq }

private noncomputable def leaf6812Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi328InputQChi innerPair372Input
    leaf6812InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6812LowerChecked :
    lowerCheck 24 leaf6812Box leaf6812Inputs = true := by
  rfl'

private theorem leaf6812CoversExact : CoversExact 8
    leaf6812Box leaf6812Certificate leaf6812InnerLog leaf6812Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi328RoundedFacts
    innerPair372RoundedFacts leaf6812RoundedFacts (by rfl)

private theorem leaf6812FlatSound : Sound leaf6812Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6812CertificateValid
    leaf6812InnerLogValid leaf6812CoversExact leaf6812LowerChecked

private noncomputable def leaf6813Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6813Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711161856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (788398739/536870912) }, upper := { exponent := 1, mantissa := (1527/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427558397/137422323712) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6813InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6813LocalValidity :
    LeafFacts leaf6813Box leaf6813Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6813Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711161856) }) = true
      norm_num [leaf6813Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6813CertificateValid :
    WideCertificateValid leaf6813Box leaf6813Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi328ValidityFacts
    leaf6813LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6813CoverageChecked :
    coverageCheck (innerAD leaf6813Box) leaf6813InnerLog = true := by
  rfl'

private theorem leaf6813InnerLogValid :
    leaf6813InnerLog.Valid 8 (innerAD leaf6813Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6813CoverageChecked

private noncomputable def leaf6813InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453715/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6813InputLogOnePlusV_eq :
    leaf6813InputLogOnePlusV = outerEnclosure 24
      (leaf6813Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6813RoundedFacts : LeafRoundedFacts 8
    leaf6813Certificate.logOnePlusV leaf6813InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6813InputLogOnePlusV_eq }

private noncomputable def leaf6813Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi328InputQChi innerPair372Input
    leaf6813InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6813LowerChecked :
    lowerCheck 24 leaf6813Box leaf6813Inputs = true := by
  rfl'

private theorem leaf6813CoversExact : CoversExact 8
    leaf6813Box leaf6813Certificate leaf6813InnerLog leaf6813Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi328RoundedFacts
    innerPair372RoundedFacts leaf6813RoundedFacts (by rfl)

private theorem leaf6813FlatSound : Sound leaf6813Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6813CertificateValid
    leaf6813InnerLogValid leaf6813CoversExact leaf6813LowerChecked

private noncomputable def leaf6814Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6814Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435823/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711261184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (782173203/536870912) }, upper := { exponent := 1, mantissa := (12119/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427657725/137422522368) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf6814InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6814LocalValidity :
    LeafFacts leaf6814Box leaf6814Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6814Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711261184) }) = true
      norm_num [leaf6814Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6814CertificateValid :
    WideCertificateValid leaf6814Box leaf6814Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi333ValidityFacts
    leaf6814LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6814CoverageChecked :
    coverageCheck (innerAD leaf6814Box) leaf6814InnerLog = true := by
  rfl'

private theorem leaf6814InnerLogValid :
    leaf6814InnerLog.Valid 8 (innerAD leaf6814Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6814CoverageChecked

private noncomputable def leaf6814InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907427/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6814InputLogOnePlusV_eq :
    leaf6814InputLogOnePlusV = outerEnclosure 24
      (leaf6814Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6814RoundedFacts : LeafRoundedFacts 8
    leaf6814Certificate.logOnePlusV leaf6814InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6814InputLogOnePlusV_eq }

private noncomputable def leaf6814Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi333InputQChi innerPair372Input
    leaf6814InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6814LowerChecked :
    lowerCheck 24 leaf6814Box leaf6814Inputs = true := by
  rfl'

private theorem leaf6814CoversExact : CoversExact 8
    leaf6814Box leaf6814Certificate leaf6814InnerLog leaf6814Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi333RoundedFacts
    innerPair372RoundedFacts leaf6814RoundedFacts (by rfl)

private theorem leaf6814FlatSound : Sound leaf6814Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6814CertificateValid
    leaf6814InnerLogValid leaf6814CoversExact leaf6814LowerChecked

private noncomputable def leaf6815Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6815Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435825/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711188480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (786760441/536870912) }, upper := { exponent := 1, mantissa := (6095/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427585021/137422376960) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf6815InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6815LocalValidity :
    LeafFacts leaf6815Box leaf6815Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6815Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711188480) }) = true
      norm_num [leaf6815Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6815CertificateValid :
    WideCertificateValid leaf6815Box leaf6815Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi333ValidityFacts
    leaf6815LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6815CoverageChecked :
    coverageCheck (innerAD leaf6815Box) leaf6815InnerLog = true := by
  rfl'

private theorem leaf6815InnerLogValid :
    leaf6815InnerLog.Valid 8 (innerAD leaf6815Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6815CoverageChecked

private noncomputable def leaf6815InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629717/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6815InputLogOnePlusV_eq :
    leaf6815InputLogOnePlusV = outerEnclosure 24
      (leaf6815Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6815RoundedFacts : LeafRoundedFacts 8
    leaf6815Certificate.logOnePlusV leaf6815InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6815InputLogOnePlusV_eq }

private noncomputable def leaf6815Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi333InputQChi innerPair372Input
    leaf6815InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6815LowerChecked :
    lowerCheck 24 leaf6815Box leaf6815Inputs = true := by
  rfl'

private theorem leaf6815CoversExact : CoversExact 8
    leaf6815Box leaf6815Certificate leaf6815InnerLog leaf6815Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi333RoundedFacts
    innerPair372RoundedFacts leaf6815RoundedFacts (by rfl)

private theorem leaf6815FlatSound : Sound leaf6815Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6815CertificateValid
    leaf6815InnerLogValid leaf6815CoversExact leaf6815LowerChecked

private noncomputable def leaf6816Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6816Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217985/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588883968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (394739937/268435456) }, upper := { exponent := 1, mantissa := (769/512) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178310655/17177767936) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6816InnerLog : WideLogData :=
  innerPair380Data

set_option maxRecDepth 1000000 in
private theorem leaf6816LocalValidity :
    LeafFacts leaf6816Box leaf6816Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6816Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588883968) }) = true
      norm_num [leaf6816Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6816CertificateValid :
    WideCertificateValid leaf6816Box leaf6816Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi334ValidityFacts
    leaf6816LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6816CoverageChecked :
    coverageCheck (innerAD leaf6816Box) leaf6816InnerLog = true := by
  rfl'

private theorem leaf6816InnerLogValid :
    leaf6816InnerLog.Valid 8 (innerAD leaf6816Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint529PositiveFacts.valid leaf6816CoverageChecked

private noncomputable def leaf6816InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629611/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6816InputLogOnePlusV_eq :
    leaf6816InputLogOnePlusV = outerEnclosure 24
      (leaf6816Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6816RoundedFacts : LeafRoundedFacts 8
    leaf6816Certificate.logOnePlusV leaf6816InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6816InputLogOnePlusV_eq }

private noncomputable def leaf6816Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi334InputQChi innerPair380Input
    leaf6816InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6816LowerChecked :
    lowerCheck 24 leaf6816Box leaf6816Inputs = true := by
  rfl'

private theorem leaf6816CoversExact : CoversExact 8
    leaf6816Box leaf6816Certificate leaf6816InnerLog leaf6816Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi334RoundedFacts
    innerPair380RoundedFacts leaf6816RoundedFacts (by rfl)

private theorem leaf6816FlatSound : Sound leaf6816Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6816CertificateValid
    leaf6816InnerLogValid leaf6816CoversExact leaf6816LowerChecked

private noncomputable def leaf6817Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6817Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177778944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (791347679/536870912) }, upper := { exponent := 1, mantissa := (12261/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356615935/34355557888) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6817InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6817LocalValidity :
    LeafFacts leaf6817Box leaf6817Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6817Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177778944) }) = true
      norm_num [leaf6817Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6817CertificateValid :
    WideCertificateValid leaf6817Box leaf6817Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi333ValidityFacts
    leaf6817LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6817CoverageChecked :
    coverageCheck (innerAD leaf6817Box) leaf6817InnerLog = true := by
  rfl'

private theorem leaf6817InnerLogValid :
    leaf6817InnerLog.Valid 8 (innerAD leaf6817Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6817CoverageChecked

private noncomputable def leaf6817InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6817InputLogOnePlusV_eq :
    leaf6817InputLogOnePlusV = outerEnclosure 24
      (leaf6817Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6817RoundedFacts : LeafRoundedFacts 8
    leaf6817Certificate.logOnePlusV leaf6817InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6817InputLogOnePlusV_eq }

private noncomputable def leaf6817Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi333InputQChi innerPair375Input
    leaf6817InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6817LowerChecked :
    lowerCheck 24 leaf6817Box leaf6817Inputs = true := by
  rfl'

private theorem leaf6817CoversExact : CoversExact 8
    leaf6817Box leaf6817Certificate leaf6817InnerLog leaf6817Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi333RoundedFacts
    innerPair375RoundedFacts leaf6817RoundedFacts (by rfl)

private theorem leaf6817FlatSound : Sound leaf6817Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6817CertificateValid
    leaf6817InnerLogValid leaf6817CoversExact leaf6817LowerChecked

private noncomputable def leaf6818Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6818Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725920256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (795934917/536870912) }, upper := { exponent := 1, mantissa := (3083/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452199253/11451840512) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6818InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6818LocalValidity :
    LeafFacts leaf6818Box leaf6818Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6818Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725920256) }) = true
      norm_num [leaf6818Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6818CertificateValid :
    WideCertificateValid leaf6818Box leaf6818Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi333ValidityFacts
    leaf6818LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6818CoverageChecked :
    coverageCheck (innerAD leaf6818Box) leaf6818InnerLog = true := by
  rfl'

private theorem leaf6818InnerLogValid :
    leaf6818InnerLog.Valid 8 (innerAD leaf6818Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6818CoverageChecked

private noncomputable def leaf6818InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814803/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6818InputLogOnePlusV_eq :
    leaf6818InputLogOnePlusV = outerEnclosure 24
      (leaf6818Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6818RoundedFacts : LeafRoundedFacts 8
    leaf6818Certificate.logOnePlusV leaf6818InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6818InputLogOnePlusV_eq }

private noncomputable def leaf6818Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi333InputQChi innerPair376Input
    leaf6818InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6818LowerChecked :
    lowerCheck 24 leaf6818Box leaf6818Inputs = true := by
  rfl'

private theorem leaf6818CoversExact : CoversExact 8
    leaf6818Box leaf6818Certificate leaf6818InnerLog leaf6818Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi333RoundedFacts
    innerPair376RoundedFacts leaf6818RoundedFacts (by rfl)

private theorem leaf6818FlatSound : Sound leaf6818Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6818CertificateValid
    leaf6818InnerLogValid leaf6818CoversExact leaf6818LowerChecked

private noncomputable def leaf6819Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6819Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177749504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (798818325/536870912) }, upper := { exponent := 1, mantissa := (1547/1024) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356586495/34355499008) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf6819InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6819LocalValidity :
    LeafFacts leaf6819Box leaf6819Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6819Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177749504) }) = true
      norm_num [leaf6819Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6819CertificateValid :
    WideCertificateValid leaf6819Box leaf6819Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi334ValidityFacts
    leaf6819LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6819CoverageChecked :
    coverageCheck (innerAD leaf6819Box) leaf6819InnerLog = true := by
  rfl'

private theorem leaf6819InnerLogValid :
    leaf6819InnerLog.Valid 8 (innerAD leaf6819Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6819CoverageChecked

private noncomputable def leaf6819InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6819InputLogOnePlusV_eq :
    leaf6819InputLogOnePlusV = outerEnclosure 24
      (leaf6819Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6819RoundedFacts : LeafRoundedFacts 8
    leaf6819Certificate.logOnePlusV leaf6819InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6819InputLogOnePlusV_eq }

private noncomputable def leaf6819Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi334InputQChi innerPair376Input
    leaf6819InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6819LowerChecked :
    lowerCheck 24 leaf6819Box leaf6819Inputs = true := by
  rfl'

private theorem leaf6819CoversExact : CoversExact 8
    leaf6819Box leaf6819Certificate leaf6819InnerLog leaf6819Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi334RoundedFacts
    innerPair376RoundedFacts leaf6819RoundedFacts (by rfl)

private theorem leaf6819FlatSound : Sound leaf6819Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6819CertificateValid
    leaf6819InnerLogValid leaf6819CoversExact leaf6819LowerChecked

private noncomputable def leaf6820Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6820Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177731072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (803471095/536870912) }, upper := { exponent := 1, mantissa := (389/256) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356568063/34355462144) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf6820InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6820LocalValidity :
    LeafFacts leaf6820Box leaf6820Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6820Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177731072) }) = true
      norm_num [leaf6820Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6820CertificateValid :
    WideCertificateValid leaf6820Box leaf6820Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi334ValidityFacts
    leaf6820LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6820CoverageChecked :
    coverageCheck (innerAD leaf6820Box) leaf6820InnerLog = true := by
  rfl'

private theorem leaf6820InnerLogValid :
    leaf6820InnerLog.Valid 8 (innerAD leaf6820Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6820CoverageChecked

private noncomputable def leaf6820InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629621/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6820InputLogOnePlusV_eq :
    leaf6820InputLogOnePlusV = outerEnclosure 24
      (leaf6820Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6820RoundedFacts : LeafRoundedFacts 8
    leaf6820Certificate.logOnePlusV leaf6820InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6820InputLogOnePlusV_eq }

private noncomputable def leaf6820Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi334InputQChi innerPair376Input
    leaf6820InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6820LowerChecked :
    lowerCheck 24 leaf6820Box leaf6820Inputs = true := by
  rfl'

private theorem leaf6820CoversExact : CoversExact 8
    leaf6820Box leaf6820Certificate leaf6820InnerLog leaf6820Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi334RoundedFacts
    innerPair376RoundedFacts leaf6820RoundedFacts (by rfl)

private theorem leaf6820FlatSound : Sound leaf6820Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6820CertificateValid
    leaf6820InnerLogValid leaf6820CoversExact leaf6820LowerChecked

private noncomputable def leaf6821Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6821Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435827/268435456) }, vSqrt := { lower := (8191/8192), upper := (68716396541/68711209984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (785318735/536870912) }, upper := { exponent := 1, mantissa := (12169/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137427606525/137422419968) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6821InnerLog : WideLogData :=
  innerPair372Data

set_option maxRecDepth 1000000 in
private theorem leaf6821LocalValidity :
    LeafFacts leaf6821Box leaf6821Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6821Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68716396541/68711209984) }) = true
      norm_num [leaf6821Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6821CertificateValid :
    WideCertificateValid leaf6821Box leaf6821Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi327ValidityFacts
    leaf6821LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6821CoverageChecked :
    coverageCheck (innerAD leaf6821Box) leaf6821InnerLog = true := by
  rfl'

private theorem leaf6821InnerLogValid :
    leaf6821InnerLog.Valid 8 (innerAD leaf6821Box) :=
  wideLogDataValid_of_cachedCheck endpoint97PositiveFacts
    endpoint99PositiveFacts.valid leaf6821CoverageChecked

private noncomputable def leaf6821InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814857/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6821InputLogOnePlusV_eq :
    leaf6821InputLogOnePlusV = outerEnclosure 24
      (leaf6821Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6821RoundedFacts : LeafRoundedFacts 8
    leaf6821Certificate.logOnePlusV leaf6821InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6821InputLogOnePlusV_eq }

private noncomputable def leaf6821Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi327InputQChi innerPair372Input
    leaf6821InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6821LowerChecked :
    lowerCheck 24 leaf6821Box leaf6821Inputs = true := by
  rfl'

private theorem leaf6821CoversExact : CoversExact 8
    leaf6821Box leaf6821Certificate leaf6821InnerLog leaf6821Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi327RoundedFacts
    innerPair372RoundedFacts leaf6821RoundedFacts (by rfl)

private theorem leaf6821FlatSound : Sound leaf6821Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6821CertificateValid
    leaf6821InnerLogValid leaf6821CoversExact leaf6821LowerChecked

private noncomputable def leaf6822Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6822Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177784832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (789774909/536870912) }, upper := { exponent := 1, mantissa := (6119/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356621823/34355569664) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6822InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6822LocalValidity :
    LeafFacts leaf6822Box leaf6822Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6822Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177784832) }) = true
      norm_num [leaf6822Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6822CertificateValid :
    WideCertificateValid leaf6822Box leaf6822Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi327ValidityFacts
    leaf6822LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6822CoverageChecked :
    coverageCheck (innerAD leaf6822Box) leaf6822InnerLog = true := by
  rfl'

private theorem leaf6822InnerLogValid :
    leaf6822InnerLog.Valid 8 (innerAD leaf6822Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6822CoverageChecked

private noncomputable def leaf6822InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629595/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6822InputLogOnePlusV_eq :
    leaf6822InputLogOnePlusV = outerEnclosure 24
      (leaf6822Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6822RoundedFacts : LeafRoundedFacts 8
    leaf6822Certificate.logOnePlusV leaf6822InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6822InputLogOnePlusV_eq }

private noncomputable def leaf6822Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi327InputQChi innerPair375Input
    leaf6822InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6822LowerChecked :
    lowerCheck 24 leaf6822Box leaf6822Inputs = true := by
  rfl'

private theorem leaf6822CoversExact : CoversExact 8
    leaf6822Box leaf6822Certificate leaf6822InnerLog leaf6822Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi327RoundedFacts
    innerPair375RoundedFacts leaf6822RoundedFacts (by rfl)

private theorem leaf6822FlatSound : Sound leaf6822Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6822CertificateValid
    leaf6822InnerLogValid leaf6822CoversExact leaf6822LowerChecked

private noncomputable def leaf6823Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6823Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435829/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177772544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (792920445/536870912) }, upper := { exponent := 1, mantissa := (6143/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356609535/34355545088) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6823InnerLog : WideLogData :=
  innerPair375Data

set_option maxRecDepth 1000000 in
private theorem leaf6823LocalValidity :
    LeafFacts leaf6823Box leaf6823Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6823Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177772544) }) = true
      norm_num [leaf6823Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6823CertificateValid :
    WideCertificateValid leaf6823Box leaf6823Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi328ValidityFacts
    leaf6823LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6823CoverageChecked :
    coverageCheck (innerAD leaf6823Box) leaf6823InnerLog = true := by
  rfl'

private theorem leaf6823InnerLogValid :
    leaf6823InnerLog.Valid 8 (innerAD leaf6823Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint99PositiveFacts.valid leaf6823CoverageChecked

private noncomputable def leaf6823InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6823InputLogOnePlusV_eq :
    leaf6823InputLogOnePlusV = outerEnclosure 24
      (leaf6823Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6823RoundedFacts : LeafRoundedFacts 8
    leaf6823Certificate.logOnePlusV leaf6823InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6823InputLogOnePlusV_eq }

private noncomputable def leaf6823Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi328InputQChi innerPair375Input
    leaf6823InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6823LowerChecked :
    lowerCheck 24 leaf6823Box leaf6823Inputs = true := by
  rfl'

private theorem leaf6823CoversExact : CoversExact 8
    leaf6823Box leaf6823Certificate leaf6823InnerLog leaf6823Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi328RoundedFacts
    innerPair375RoundedFacts leaf6823RoundedFacts (by rfl)

private theorem leaf6823FlatSound : Sound leaf6823Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6823CertificateValid
    leaf6823InnerLogValid leaf6823CoversExact leaf6823LowerChecked

private noncomputable def leaf6824Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6824Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725918208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (797442151/536870912) }, upper := { exponent := 1, mantissa := (3089/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452197205/11451836416) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6824InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6824LocalValidity :
    LeafFacts leaf6824Box leaf6824Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6824Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725918208) }) = true
      norm_num [leaf6824Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6824CertificateValid :
    WideCertificateValid leaf6824Box leaf6824Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi328ValidityFacts
    leaf6824LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6824CoverageChecked :
    coverageCheck (innerAD leaf6824Box) leaf6824InnerLog = true := by
  rfl'

private theorem leaf6824InnerLogValid :
    leaf6824InnerLog.Valid 8 (innerAD leaf6824Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6824CoverageChecked

private noncomputable def leaf6824InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629609/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6824InputLogOnePlusV_eq :
    leaf6824InputLogOnePlusV = outerEnclosure 24
      (leaf6824Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6824RoundedFacts : LeafRoundedFacts 8
    leaf6824Certificate.logOnePlusV leaf6824InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6824InputLogOnePlusV_eq }

private noncomputable def leaf6824Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi328InputQChi innerPair376Input
    leaf6824InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6824LowerChecked :
    lowerCheck 24 leaf6824Box leaf6824Inputs = true := by
  rfl'

private theorem leaf6824CoversExact : CoversExact 8
    leaf6824Box leaf6824Certificate leaf6824InnerLog leaf6824Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi328RoundedFacts
    innerPair376RoundedFacts leaf6824RoundedFacts (by rfl)

private theorem leaf6824FlatSound : Sound leaf6824Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6824CertificateValid
    leaf6824InnerLogValid leaf6824CoversExact leaf6824LowerChecked

private noncomputable def leaf6825Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6825Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177767168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (794231083/536870912) }, upper := { exponent := 1, mantissa := (12307/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356604159/34355534336) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6825InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6825LocalValidity :
    LeafFacts leaf6825Box leaf6825Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6825Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177767168) }) = true
      norm_num [leaf6825Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6825CertificateValid :
    WideCertificateValid leaf6825Box leaf6825Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi327ValidityFacts
    leaf6825LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6825CoverageChecked :
    coverageCheck (innerAD leaf6825Box) leaf6825InnerLog = true := by
  rfl'

private theorem leaf6825InnerLogValid :
    leaf6825InnerLog.Valid 8 (innerAD leaf6825Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6825CoverageChecked

private noncomputable def leaf6825InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629603/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6825InputLogOnePlusV_eq :
    leaf6825InputLogOnePlusV = outerEnclosure 24
      (leaf6825Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6825RoundedFacts : LeafRoundedFacts 8
    leaf6825Certificate.logOnePlusV leaf6825InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6825InputLogOnePlusV_eq }

private noncomputable def leaf6825Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi327InputQChi innerPair376Input
    leaf6825InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6825LowerChecked :
    lowerCheck 24 leaf6825Box leaf6825Inputs = true := by
  rfl'

private theorem leaf6825CoversExact : CoversExact 8
    leaf6825Box leaf6825Certificate leaf6825InnerLog leaf6825Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi327RoundedFacts
    innerPair376RoundedFacts leaf6825RoundedFacts (by rfl)

private theorem leaf6825FlatSound : Sound leaf6825Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6825CertificateValid
    leaf6825InnerLogValid leaf6825CoversExact leaf6825LowerChecked

private noncomputable def leaf6826Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6826Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177749504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (798687257/536870912) }, upper := { exponent := 1, mantissa := (1547/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356586495/34355499008) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6826InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6826LocalValidity :
    LeafFacts leaf6826Box leaf6826Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6826Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177749504) }) = true
      norm_num [leaf6826Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6826CertificateValid :
    WideCertificateValid leaf6826Box leaf6826Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi327ValidityFacts
    leaf6826LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6826CoverageChecked :
    coverageCheck (innerAD leaf6826Box) leaf6826InnerLog = true := by
  rfl'

private theorem leaf6826InnerLogValid :
    leaf6826InnerLog.Valid 8 (innerAD leaf6826Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6826CoverageChecked

private noncomputable def leaf6826InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907403/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6826InputLogOnePlusV_eq :
    leaf6826InputLogOnePlusV = outerEnclosure 24
      (leaf6826Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6826RoundedFacts : LeafRoundedFacts 8
    leaf6826Certificate.logOnePlusV leaf6826InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6826InputLogOnePlusV_eq }

private noncomputable def leaf6826Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi327InputQChi innerPair376Input
    leaf6826InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6826LowerChecked :
    lowerCheck 24 leaf6826Box leaf6826Inputs = true := by
  rfl'

private theorem leaf6826CoversExact : CoversExact 8
    leaf6826Box leaf6826Certificate leaf6826InnerLog leaf6826Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi327RoundedFacts
    innerPair376RoundedFacts leaf6826RoundedFacts (by rfl)

private theorem leaf6826FlatSound : Sound leaf6826Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6826CertificateValid
    leaf6826InnerLogValid leaf6826CoversExact leaf6826LowerChecked

private noncomputable def leaf6827Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6827Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177736704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (801963857/536870912) }, upper := { exponent := 1, mantissa := (6213/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356573695/34355473408) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6827InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6827LocalValidity :
    LeafFacts leaf6827Box leaf6827Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6827Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177736704) }) = true
      norm_num [leaf6827Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6827CertificateValid :
    WideCertificateValid leaf6827Box leaf6827Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi328ValidityFacts
    leaf6827LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6827CoverageChecked :
    coverageCheck (innerAD leaf6827Box) leaf6827InnerLog = true := by
  rfl'

private theorem leaf6827InnerLogValid :
    leaf6827InnerLog.Valid 8 (innerAD leaf6827Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6827CoverageChecked

private noncomputable def leaf6827InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814809/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6827InputLogOnePlusV_eq :
    leaf6827InputLogOnePlusV = outerEnclosure 24
      (leaf6827Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6827RoundedFacts : LeafRoundedFacts 8
    leaf6827Certificate.logOnePlusV leaf6827InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6827InputLogOnePlusV_eq }

private noncomputable def leaf6827Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi328InputQChi innerPair376Input
    leaf6827InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6827LowerChecked :
    lowerCheck 24 leaf6827Box leaf6827Inputs = true := by
  rfl'

private theorem leaf6827CoversExact : CoversExact 8
    leaf6827Box leaf6827Certificate leaf6827InnerLog leaf6827Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi328RoundedFacts
    innerPair376RoundedFacts leaf6827RoundedFacts (by rfl)

private theorem leaf6827FlatSound : Sound leaf6827Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6827CertificateValid
    leaf6827InnerLogValid leaf6827CoversExact leaf6827LowerChecked

private noncomputable def leaf6828Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6828Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177718784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (806485563/536870912) }, upper := { exponent := 1, mantissa := (781/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356555775/34355437568) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6828InnerLog : WideLogData :=
  innerPair381Data

set_option maxRecDepth 1000000 in
private theorem leaf6828LocalValidity :
    LeafFacts leaf6828Box leaf6828Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6828Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177718784) }) = true
      norm_num [leaf6828Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6828CertificateValid :
    WideCertificateValid leaf6828Box leaf6828Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi328ValidityFacts
    leaf6828LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6828CoverageChecked :
    coverageCheck (innerAD leaf6828Box) leaf6828InnerLog = true := by
  rfl'

private theorem leaf6828InnerLogValid :
    leaf6828InnerLog.Valid 8 (innerAD leaf6828Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint482PositiveFacts.valid leaf6828CoverageChecked

private noncomputable def leaf6828InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629627/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6828InputLogOnePlusV_eq :
    leaf6828InputLogOnePlusV = outerEnclosure 24
      (leaf6828Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6828RoundedFacts : LeafRoundedFacts 8
    leaf6828Certificate.logOnePlusV leaf6828InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6828InputLogOnePlusV_eq }

private noncomputable def leaf6828Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi328InputQChi innerPair381Input
    leaf6828InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6828LowerChecked :
    lowerCheck 24 leaf6828Box leaf6828Inputs = true := by
  rfl'

private theorem leaf6828CoversExact : CoversExact 8
    leaf6828Box leaf6828Certificate leaf6828InnerLog leaf6828Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi328RoundedFacts
    innerPair381RoundedFacts leaf6828RoundedFacts (by rfl)

private theorem leaf6828FlatSound : Sound leaf6828Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6828CertificateValid
    leaf6828InnerLogValid leaf6828CoversExact leaf6828LowerChecked

private noncomputable def leaf6829Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6829Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435831/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177742592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (800522155/536870912) }, upper := { exponent := 1, mantissa := (12403/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356579583/34355485184) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6829InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6829LocalValidity :
    LeafFacts leaf6829Box leaf6829Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6829Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177742592) }) = true
      norm_num [leaf6829Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6829CertificateValid :
    WideCertificateValid leaf6829Box leaf6829Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi333ValidityFacts
    leaf6829LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6829CoverageChecked :
    coverageCheck (innerAD leaf6829Box) leaf6829InnerLog = true := by
  rfl'

private theorem leaf6829InnerLogValid :
    leaf6829InnerLog.Valid 8 (innerAD leaf6829Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6829CoverageChecked

private noncomputable def leaf6829InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629615/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6829InputLogOnePlusV_eq :
    leaf6829InputLogOnePlusV = outerEnclosure 24
      (leaf6829Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6829RoundedFacts : LeafRoundedFacts 8
    leaf6829Certificate.logOnePlusV leaf6829InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6829InputLogOnePlusV_eq }

private noncomputable def leaf6829Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi333InputQChi innerPair376Input
    leaf6829InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6829LowerChecked :
    lowerCheck 24 leaf6829Box leaf6829Inputs = true := by
  rfl'

private theorem leaf6829CoversExact : CoversExact 8
    leaf6829Box leaf6829Certificate leaf6829InnerLog leaf6829Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi333RoundedFacts
    innerPair376RoundedFacts leaf6829RoundedFacts (by rfl)

private theorem leaf6829FlatSound : Sound leaf6829Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6829CertificateValid
    leaf6829InnerLogValid leaf6829CoversExact leaf6829LowerChecked

private noncomputable def leaf6830Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6830Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177724416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (805109393/536870912) }, upper := { exponent := 1, mantissa := (6237/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356561407/34355448832) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6830InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6830LocalValidity :
    LeafFacts leaf6830Box leaf6830Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6830Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177724416) }) = true
      norm_num [leaf6830Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6830CertificateValid :
    WideCertificateValid leaf6830Box leaf6830Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi333ValidityFacts
    leaf6830LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6830CoverageChecked :
    coverageCheck (innerAD leaf6830Box) leaf6830InnerLog = true := by
  rfl'

private theorem leaf6830InnerLogValid :
    leaf6830InnerLog.Valid 8 (innerAD leaf6830Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6830CoverageChecked

private noncomputable def leaf6830InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453703/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6830InputLogOnePlusV_eq :
    leaf6830InputLogOnePlusV = outerEnclosure 24
      (leaf6830Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6830RoundedFacts : LeafRoundedFacts 8
    leaf6830Certificate.logOnePlusV leaf6830InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6830InputLogOnePlusV_eq }

private noncomputable def leaf6830Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi333InputQChi innerPair376Input
    leaf6830InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6830LowerChecked :
    lowerCheck 24 leaf6830Box leaf6830Inputs = true := by
  rfl'

private theorem leaf6830CoversExact : CoversExact 8
    leaf6830Box leaf6830Certificate leaf6830InnerLog leaf6830Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi333RoundedFacts
    innerPair376RoundedFacts leaf6830RoundedFacts (by rfl)

private theorem leaf6830FlatSound : Sound leaf6830Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6830CertificateValid
    leaf6830InnerLogValid leaf6830CoversExact leaf6830LowerChecked

private noncomputable def leaf6831Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6831Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435833/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177712640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (808123865/536870912) }, upper := { exponent := 1, mantissa := (1565/1024) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356549631/34355425280) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf6831InnerLog : WideLogData :=
  innerPair381Data

set_option maxRecDepth 1000000 in
private theorem leaf6831LocalValidity :
    LeafFacts leaf6831Box leaf6831Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6831Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177712640) }) = true
      norm_num [leaf6831Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6831CertificateValid :
    WideCertificateValid leaf6831Box leaf6831Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi334ValidityFacts
    leaf6831LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6831CoverageChecked :
    coverageCheck (innerAD leaf6831Box) leaf6831InnerLog = true := by
  rfl'

private theorem leaf6831InnerLogValid :
    leaf6831InnerLog.Valid 8 (innerAD leaf6831Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint482PositiveFacts.valid leaf6831CoverageChecked

private noncomputable def leaf6831InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814815/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6831InputLogOnePlusV_eq :
    leaf6831InputLogOnePlusV = outerEnclosure 24
      (leaf6831Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6831RoundedFacts : LeafRoundedFacts 8
    leaf6831Certificate.logOnePlusV leaf6831InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6831InputLogOnePlusV_eq }

private noncomputable def leaf6831Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi334InputQChi innerPair381Input
    leaf6831InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6831LowerChecked :
    lowerCheck 24 leaf6831Box leaf6831Inputs = true := by
  rfl'

private theorem leaf6831CoversExact : CoversExact 8
    leaf6831Box leaf6831Certificate leaf6831InnerLog leaf6831Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi334RoundedFacts
    innerPair381RoundedFacts leaf6831RoundedFacts (by rfl)

private theorem leaf6831FlatSound : Sound leaf6831Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6831CertificateValid
    leaf6831InnerLogValid leaf6831CoversExact leaf6831LowerChecked

private noncomputable def leaf6832Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6832Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177694208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (812776635/536870912) }, upper := { exponent := 1, mantissa := (787/512) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356531199/34355388416) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf6832InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6832LocalValidity :
    LeafFacts leaf6832Box leaf6832Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6832Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177694208) }) = true
      norm_num [leaf6832Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6832CertificateValid :
    WideCertificateValid leaf6832Box leaf6832Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi334ValidityFacts
    leaf6832LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6832CoverageChecked :
    coverageCheck (innerAD leaf6832Box) leaf6832InnerLog = true := by
  rfl'

private theorem leaf6832InnerLogValid :
    leaf6832InnerLog.Valid 8 (innerAD leaf6832Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6832CoverageChecked

private noncomputable def leaf6832InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629639/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6832InputLogOnePlusV_eq :
    leaf6832InputLogOnePlusV = outerEnclosure 24
      (leaf6832Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6832RoundedFacts : LeafRoundedFacts 8
    leaf6832Certificate.logOnePlusV leaf6832InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6832InputLogOnePlusV_eq }

private noncomputable def leaf6832Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi334InputQChi innerPair382Input
    leaf6832InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6832LowerChecked :
    lowerCheck 24 leaf6832Box leaf6832Inputs = true := by
  rfl'

private theorem leaf6832CoversExact : CoversExact 8
    leaf6832Box leaf6832Certificate leaf6832InnerLog leaf6832Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi334RoundedFacts
    innerPair382RoundedFacts leaf6832RoundedFacts (by rfl)

private theorem leaf6832FlatSound : Sound leaf6832Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6832CertificateValid
    leaf6832InnerLogValid leaf6832CoversExact leaf6832LowerChecked

private noncomputable def leaf6833Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6833Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435835/268435456) }, vSqrt := { lower := (8191/8192), upper := (5726278997/5725902080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (809696631/536870912) }, upper := { exponent := 1, mantissa := (12545/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11452181077/11451804160) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6833InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6833LocalValidity :
    LeafFacts leaf6833Box leaf6833Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6833Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726278997/5725902080) }) = true
      norm_num [leaf6833Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6833CertificateValid :
    WideCertificateValid leaf6833Box leaf6833Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi333ValidityFacts
    leaf6833LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6833CoverageChecked :
    coverageCheck (innerAD leaf6833Box) leaf6833InnerLog = true := by
  rfl'

private theorem leaf6833InnerLogValid :
    leaf6833InnerLog.Valid 8 (innerAD leaf6833Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6833CoverageChecked

private noncomputable def leaf6833InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629633/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6833InputLogOnePlusV_eq :
    leaf6833InputLogOnePlusV = outerEnclosure 24
      (leaf6833Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6833RoundedFacts : LeafRoundedFacts 8
    leaf6833Certificate.logOnePlusV leaf6833InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6833InputLogOnePlusV_eq }

private noncomputable def leaf6833Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi333InputQChi innerPair382Input
    leaf6833InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6833LowerChecked :
    lowerCheck 24 leaf6833Box leaf6833Inputs = true := by
  rfl'

private theorem leaf6833CoversExact : CoversExact 8
    leaf6833Box leaf6833Certificate leaf6833InnerLog leaf6833Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi333RoundedFacts
    innerPair382RoundedFacts leaf6833RoundedFacts (by rfl)

private theorem leaf6833FlatSound : Sound leaf6833Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6833CertificateValid
    leaf6833InnerLogValid leaf6833CoversExact leaf6833LowerChecked

private noncomputable def leaf6834Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6834Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177688064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (814283869/536870912) }, upper := { exponent := 1, mantissa := (1577/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356525055/34355376128) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6834InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6834LocalValidity :
    LeafFacts leaf6834Box leaf6834Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6834Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177688064) }) = true
      norm_num [leaf6834Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6834CertificateValid :
    WideCertificateValid leaf6834Box leaf6834Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi333ValidityFacts
    leaf6834LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6834CoverageChecked :
    coverageCheck (innerAD leaf6834Box) leaf6834InnerLog = true := by
  rfl'

private theorem leaf6834InnerLogValid :
    leaf6834InnerLog.Valid 8 (innerAD leaf6834Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6834CoverageChecked

private noncomputable def leaf6834InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814821/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6834InputLogOnePlusV_eq :
    leaf6834InputLogOnePlusV = outerEnclosure 24
      (leaf6834Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6834RoundedFacts : LeafRoundedFacts 8
    leaf6834Certificate.logOnePlusV leaf6834InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6834InputLogOnePlusV_eq }

private noncomputable def leaf6834Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi333InputQChi innerPair382Input
    leaf6834InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6834LowerChecked :
    lowerCheck 24 leaf6834Box leaf6834Inputs = true := by
  rfl'

private theorem leaf6834CoversExact : CoversExact 8
    leaf6834Box leaf6834Certificate leaf6834InnerLog leaf6834Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi333RoundedFacts
    innerPair382RoundedFacts leaf6834RoundedFacts (by rfl)

private theorem leaf6834FlatSound : Sound leaf6834Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6834CertificateValid
    leaf6834InnerLogValid leaf6834CoversExact leaf6834LowerChecked

private noncomputable def leaf6835Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6835Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435837/268435456) }, vSqrt := { lower := (8191/8192), upper := (399507837/399480832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (817429405/536870912) }, upper := { exponent := 1, mantissa := (1583/1024) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (798988669/798961664) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6835InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6835LocalValidity :
    LeafFacts leaf6835Box leaf6835Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6835Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (399507837/399480832) }) = true
      norm_num [leaf6835Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6835CertificateValid :
    WideCertificateValid leaf6835Box leaf6835Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi334ValidityFacts
    leaf6835LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6835CoverageChecked :
    coverageCheck (innerAD leaf6835Box) leaf6835InnerLog = true := by
  rfl'

private theorem leaf6835InnerLogValid :
    leaf6835InnerLog.Valid 8 (innerAD leaf6835Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6835CoverageChecked

private noncomputable def leaf6835InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726853/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6835InputLogOnePlusV_eq :
    leaf6835InputLogOnePlusV = outerEnclosure 24
      (leaf6835Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6835RoundedFacts : LeafRoundedFacts 8
    leaf6835Certificate.logOnePlusV leaf6835InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6835InputLogOnePlusV_eq }

private noncomputable def leaf6835Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi334InputQChi innerPair382Input
    leaf6835InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6835LowerChecked :
    lowerCheck 24 leaf6835Box leaf6835Inputs = true := by
  rfl'

private theorem leaf6835CoversExact : CoversExact 8
    leaf6835Box leaf6835Certificate leaf6835InnerLog leaf6835Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi334RoundedFacts
    innerPair382RoundedFacts leaf6835RoundedFacts (by rfl)

private theorem leaf6835FlatSound : Sound leaf6835Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6835CertificateValid
    leaf6835InnerLogValid leaf6835CoversExact leaf6835LowerChecked

private noncomputable def leaf6836Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6836Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (1010519823/1010450432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (822082175/536870912) }, upper := { exponent := 1, mantissa := (199/128) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2020970255/2020900864) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6836InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6836LocalValidity :
    LeafFacts leaf6836Box leaf6836Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6836Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1010519823/1010450432) }) = true
      norm_num [leaf6836Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6836CertificateValid :
    WideCertificateValid leaf6836Box leaf6836Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi334ValidityFacts
    leaf6836LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6836CoverageChecked :
    coverageCheck (innerAD leaf6836Box) leaf6836InnerLog = true := by
  rfl'

private theorem leaf6836InnerLogValid :
    leaf6836InnerLog.Valid 8 (innerAD leaf6836Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6836CoverageChecked

private noncomputable def leaf6836InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629657/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6836InputLogOnePlusV_eq :
    leaf6836InputLogOnePlusV = outerEnclosure 24
      (leaf6836Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6836RoundedFacts : LeafRoundedFacts 8
    leaf6836Certificate.logOnePlusV leaf6836InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6836InputLogOnePlusV_eq }

private noncomputable def leaf6836Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi334InputQChi innerPair382Input
    leaf6836InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6836LowerChecked :
    lowerCheck 24 leaf6836Box leaf6836Inputs = true := by
  rfl'

private theorem leaf6836CoversExact : CoversExact 8
    leaf6836Box leaf6836Certificate leaf6836InnerLog leaf6836Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi334RoundedFacts
    innerPair382RoundedFacts leaf6836RoundedFacts (by rfl)

private theorem leaf6836FlatSound : Sound leaf6836Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6836CertificateValid
    leaf6836InnerLogValid leaf6836CoversExact leaf6836LowerChecked

private noncomputable def component138Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node0_sound : Sound component138Node0Box :=
  sound_of_literal_split component138Node0Box leaf6774Box leaf6775Box
    .k (113/32) (by rfl) (by rfl)
    leaf6774FlatSound leaf6775FlatSound

private noncomputable def component138Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node1_sound : Sound component138Node1Box :=
  sound_of_literal_split component138Node1Box leaf6776Box leaf6777Box
    .k (113/32) (by rfl) (by rfl)
    leaf6776FlatSound leaf6777FlatSound

private noncomputable def component138Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node2_sound : Sound component138Node2Box :=
  sound_of_literal_split component138Node2Box component138Node0Box component138Node1Box
    .chi (65/128) (by rfl) (by rfl)
    component138Node0_sound component138Node1_sound

private noncomputable def component138Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node3_sound : Sound component138Node3Box :=
  sound_of_literal_split component138Node3Box leaf6778Box leaf6779Box
    .k (115/32) (by rfl) (by rfl)
    leaf6778FlatSound leaf6779FlatSound

private noncomputable def component138Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node4_sound : Sound component138Node4Box :=
  sound_of_literal_split component138Node4Box leaf6780Box leaf6781Box
    .k (115/32) (by rfl) (by rfl)
    leaf6780FlatSound leaf6781FlatSound

private noncomputable def component138Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node5_sound : Sound component138Node5Box :=
  sound_of_literal_split component138Node5Box component138Node3Box component138Node4Box
    .chi (65/128) (by rfl) (by rfl)
    component138Node3_sound component138Node4_sound

private noncomputable def component138Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node6_sound : Sound component138Node6Box :=
  sound_of_literal_split component138Node6Box component138Node2Box component138Node5Box
    .k (57/16) (by rfl) (by rfl)
    component138Node2_sound component138Node5_sound

private noncomputable def component138Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node7_sound : Sound component138Node7Box :=
  sound_of_literal_split component138Node7Box leaf6782Box leaf6783Box
    .k (113/32) (by rfl) (by rfl)
    leaf6782FlatSound leaf6783FlatSound

private noncomputable def component138Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node8_sound : Sound component138Node8Box :=
  sound_of_literal_split component138Node8Box leaf6784Box leaf6785Box
    .k (113/32) (by rfl) (by rfl)
    leaf6784FlatSound leaf6785FlatSound

private noncomputable def component138Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node9_sound : Sound component138Node9Box :=
  sound_of_literal_split component138Node9Box component138Node7Box component138Node8Box
    .chi (67/128) (by rfl) (by rfl)
    component138Node7_sound component138Node8_sound

private noncomputable def component138Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node10_sound : Sound component138Node10Box :=
  sound_of_literal_split component138Node10Box leaf6786Box leaf6787Box
    .k (115/32) (by rfl) (by rfl)
    leaf6786FlatSound leaf6787FlatSound

private noncomputable def component138Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node11_sound : Sound component138Node11Box :=
  sound_of_literal_split component138Node11Box leaf6788Box leaf6789Box
    .k (115/32) (by rfl) (by rfl)
    leaf6788FlatSound leaf6789FlatSound

private noncomputable def component138Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node12_sound : Sound component138Node12Box :=
  sound_of_literal_split component138Node12Box component138Node10Box component138Node11Box
    .chi (67/128) (by rfl) (by rfl)
    component138Node10_sound component138Node11_sound

private noncomputable def component138Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node13_sound : Sound component138Node13Box :=
  sound_of_literal_split component138Node13Box component138Node9Box component138Node12Box
    .k (57/16) (by rfl) (by rfl)
    component138Node9_sound component138Node12_sound

private noncomputable def component138Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node14_sound : Sound component138Node14Box :=
  sound_of_literal_split component138Node14Box component138Node6Box component138Node13Box
    .chi (33/64) (by rfl) (by rfl)
    component138Node6_sound component138Node13_sound

private noncomputable def component138Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node15_sound : Sound component138Node15Box :=
  sound_of_literal_split component138Node15Box leaf6790Box leaf6791Box
    .k (117/32) (by rfl) (by rfl)
    leaf6790FlatSound leaf6791FlatSound

private noncomputable def component138Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node16_sound : Sound component138Node16Box :=
  sound_of_literal_split component138Node16Box leaf6792Box leaf6793Box
    .k (117/32) (by rfl) (by rfl)
    leaf6792FlatSound leaf6793FlatSound

private noncomputable def component138Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node17_sound : Sound component138Node17Box :=
  sound_of_literal_split component138Node17Box component138Node15Box component138Node16Box
    .chi (65/128) (by rfl) (by rfl)
    component138Node15_sound component138Node16_sound

private noncomputable def component138Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node18_sound : Sound component138Node18Box :=
  sound_of_literal_split component138Node18Box leaf6794Box leaf6795Box
    .k (119/32) (by rfl) (by rfl)
    leaf6794FlatSound leaf6795FlatSound

private noncomputable def component138Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node19_sound : Sound component138Node19Box :=
  sound_of_literal_split component138Node19Box leaf6796Box leaf6797Box
    .k (119/32) (by rfl) (by rfl)
    leaf6796FlatSound leaf6797FlatSound

private noncomputable def component138Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node20_sound : Sound component138Node20Box :=
  sound_of_literal_split component138Node20Box component138Node18Box component138Node19Box
    .chi (65/128) (by rfl) (by rfl)
    component138Node18_sound component138Node19_sound

private noncomputable def component138Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node21_sound : Sound component138Node21Box :=
  sound_of_literal_split component138Node21Box component138Node17Box component138Node20Box
    .k (59/16) (by rfl) (by rfl)
    component138Node17_sound component138Node20_sound

private noncomputable def component138Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node22_sound : Sound component138Node22Box :=
  sound_of_literal_split component138Node22Box leaf6798Box leaf6799Box
    .k (117/32) (by rfl) (by rfl)
    leaf6798FlatSound leaf6799FlatSound

private noncomputable def component138Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node23_sound : Sound component138Node23Box :=
  sound_of_literal_split component138Node23Box leaf6800Box leaf6801Box
    .k (117/32) (by rfl) (by rfl)
    leaf6800FlatSound leaf6801FlatSound

private noncomputable def component138Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node24_sound : Sound component138Node24Box :=
  sound_of_literal_split component138Node24Box component138Node22Box component138Node23Box
    .chi (67/128) (by rfl) (by rfl)
    component138Node22_sound component138Node23_sound

private noncomputable def component138Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node25_sound : Sound component138Node25Box :=
  sound_of_literal_split component138Node25Box leaf6802Box leaf6803Box
    .k (119/32) (by rfl) (by rfl)
    leaf6802FlatSound leaf6803FlatSound

private noncomputable def component138Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (67/128), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node26_sound : Sound component138Node26Box :=
  sound_of_literal_split component138Node26Box leaf6804Box leaf6805Box
    .k (119/32) (by rfl) (by rfl)
    leaf6804FlatSound leaf6805FlatSound

private noncomputable def component138Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node27_sound : Sound component138Node27Box :=
  sound_of_literal_split component138Node27Box component138Node25Box component138Node26Box
    .chi (67/128) (by rfl) (by rfl)
    component138Node25_sound component138Node26_sound

private noncomputable def component138Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node28_sound : Sound component138Node28Box :=
  sound_of_literal_split component138Node28Box component138Node24Box component138Node27Box
    .k (59/16) (by rfl) (by rfl)
    component138Node24_sound component138Node27_sound

private noncomputable def component138Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node29_sound : Sound component138Node29Box :=
  sound_of_literal_split component138Node29Box component138Node21Box component138Node28Box
    .chi (33/64) (by rfl) (by rfl)
    component138Node21_sound component138Node28_sound

private noncomputable def component138Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component138Node30_sound : Sound component138Node30Box :=
  sound_of_literal_split component138Node30Box component138Node14Box component138Node29Box
    .k (29/8) (by rfl) (by rfl)
    component138Node14_sound component138Node29_sound

private noncomputable def component138Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node31_sound : Sound component138Node31Box :=
  sound_of_literal_split component138Node31Box leaf6806Box leaf6807Box
    .k (113/32) (by rfl) (by rfl)
    leaf6806FlatSound leaf6807FlatSound

private noncomputable def component138Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node32_sound : Sound component138Node32Box :=
  sound_of_literal_split component138Node32Box leaf6808Box leaf6809Box
    .k (113/32) (by rfl) (by rfl)
    leaf6808FlatSound leaf6809FlatSound

private noncomputable def component138Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node33_sound : Sound component138Node33Box :=
  sound_of_literal_split component138Node33Box component138Node31Box component138Node32Box
    .chi (69/128) (by rfl) (by rfl)
    component138Node31_sound component138Node32_sound

private noncomputable def component138Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node34_sound : Sound component138Node34Box :=
  sound_of_literal_split component138Node34Box leaf6810Box leaf6811Box
    .k (115/32) (by rfl) (by rfl)
    leaf6810FlatSound leaf6811FlatSound

private noncomputable def component138Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node35_sound : Sound component138Node35Box :=
  sound_of_literal_split component138Node35Box leaf6812Box leaf6813Box
    .k (115/32) (by rfl) (by rfl)
    leaf6812FlatSound leaf6813FlatSound

private noncomputable def component138Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node36_sound : Sound component138Node36Box :=
  sound_of_literal_split component138Node36Box component138Node34Box component138Node35Box
    .chi (69/128) (by rfl) (by rfl)
    component138Node34_sound component138Node35_sound

private noncomputable def component138Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node37_sound : Sound component138Node37Box :=
  sound_of_literal_split component138Node37Box component138Node33Box component138Node36Box
    .k (57/16) (by rfl) (by rfl)
    component138Node33_sound component138Node36_sound

private noncomputable def component138Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node38_sound : Sound component138Node38Box :=
  sound_of_literal_split component138Node38Box leaf6814Box leaf6815Box
    .k (113/32) (by rfl) (by rfl)
    leaf6814FlatSound leaf6815FlatSound

private noncomputable def component138Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node39_sound : Sound component138Node39Box :=
  sound_of_literal_split component138Node39Box component138Node38Box leaf6816Box
    .chi (71/128) (by rfl) (by rfl)
    component138Node38_sound leaf6816FlatSound

private noncomputable def component138Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node40_sound : Sound component138Node40Box :=
  sound_of_literal_split component138Node40Box leaf6817Box leaf6818Box
    .k (115/32) (by rfl) (by rfl)
    leaf6817FlatSound leaf6818FlatSound

private noncomputable def component138Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (71/128), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node41_sound : Sound component138Node41Box :=
  sound_of_literal_split component138Node41Box leaf6819Box leaf6820Box
    .k (115/32) (by rfl) (by rfl)
    leaf6819FlatSound leaf6820FlatSound

private noncomputable def component138Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node42_sound : Sound component138Node42Box :=
  sound_of_literal_split component138Node42Box component138Node40Box component138Node41Box
    .chi (71/128) (by rfl) (by rfl)
    component138Node40_sound component138Node41_sound

private noncomputable def component138Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node43_sound : Sound component138Node43Box :=
  sound_of_literal_split component138Node43Box component138Node39Box component138Node42Box
    .k (57/16) (by rfl) (by rfl)
    component138Node39_sound component138Node42_sound

private noncomputable def component138Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node44_sound : Sound component138Node44Box :=
  sound_of_literal_split component138Node44Box component138Node37Box component138Node43Box
    .chi (35/64) (by rfl) (by rfl)
    component138Node37_sound component138Node43_sound

private noncomputable def component138Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node45_sound : Sound component138Node45Box :=
  sound_of_literal_split component138Node45Box leaf6821Box leaf6822Box
    .k (117/32) (by rfl) (by rfl)
    leaf6821FlatSound leaf6822FlatSound

private noncomputable def component138Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node46_sound : Sound component138Node46Box :=
  sound_of_literal_split component138Node46Box leaf6823Box leaf6824Box
    .k (117/32) (by rfl) (by rfl)
    leaf6823FlatSound leaf6824FlatSound

private noncomputable def component138Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node47_sound : Sound component138Node47Box :=
  sound_of_literal_split component138Node47Box component138Node45Box component138Node46Box
    .chi (69/128) (by rfl) (by rfl)
    component138Node45_sound component138Node46_sound

private noncomputable def component138Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (17/32), chiHi := (69/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node48_sound : Sound component138Node48Box :=
  sound_of_literal_split component138Node48Box leaf6825Box leaf6826Box
    .k (119/32) (by rfl) (by rfl)
    leaf6825FlatSound leaf6826FlatSound

private noncomputable def component138Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (69/128), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node49_sound : Sound component138Node49Box :=
  sound_of_literal_split component138Node49Box leaf6827Box leaf6828Box
    .k (119/32) (by rfl) (by rfl)
    leaf6827FlatSound leaf6828FlatSound

private noncomputable def component138Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node50_sound : Sound component138Node50Box :=
  sound_of_literal_split component138Node50Box component138Node48Box component138Node49Box
    .chi (69/128) (by rfl) (by rfl)
    component138Node48_sound component138Node49_sound

private noncomputable def component138Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component138Node51_sound : Sound component138Node51Box :=
  sound_of_literal_split component138Node51Box component138Node47Box component138Node50Box
    .k (59/16) (by rfl) (by rfl)
    component138Node47_sound component138Node50_sound

private noncomputable def component138Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node52_sound : Sound component138Node52Box :=
  sound_of_literal_split component138Node52Box leaf6829Box leaf6830Box
    .k (117/32) (by rfl) (by rfl)
    leaf6829FlatSound leaf6830FlatSound

private noncomputable def component138Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (71/128), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node53_sound : Sound component138Node53Box :=
  sound_of_literal_split component138Node53Box leaf6831Box leaf6832Box
    .k (117/32) (by rfl) (by rfl)
    leaf6831FlatSound leaf6832FlatSound

private noncomputable def component138Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node54_sound : Sound component138Node54Box :=
  sound_of_literal_split component138Node54Box component138Node52Box component138Node53Box
    .chi (71/128) (by rfl) (by rfl)
    component138Node52_sound component138Node53_sound

private noncomputable def component138Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (35/64), chiHi := (71/128) }

set_option maxRecDepth 1000000 in
private theorem component138Node55_sound : Sound component138Node55Box :=
  sound_of_literal_split component138Node55Box leaf6833Box leaf6834Box
    .k (119/32) (by rfl) (by rfl)
    leaf6833FlatSound leaf6834FlatSound

private noncomputable def component138Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (71/128), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node56_sound : Sound component138Node56Box :=
  sound_of_literal_split component138Node56Box leaf6835Box leaf6836Box
    .k (119/32) (by rfl) (by rfl)
    leaf6835FlatSound leaf6836FlatSound

private noncomputable def component138Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node57_sound : Sound component138Node57Box :=
  sound_of_literal_split component138Node57Box component138Node55Box component138Node56Box
    .chi (71/128) (by rfl) (by rfl)
    component138Node55_sound component138Node56_sound

private noncomputable def component138Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node58_sound : Sound component138Node58Box :=
  sound_of_literal_split component138Node58Box component138Node54Box component138Node57Box
    .k (59/16) (by rfl) (by rfl)
    component138Node54_sound component138Node57_sound

private noncomputable def component138Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node59_sound : Sound component138Node59Box :=
  sound_of_literal_split component138Node59Box component138Node51Box component138Node58Box
    .chi (35/64) (by rfl) (by rfl)
    component138Node51_sound component138Node58_sound

private noncomputable def component138Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component138Node60_sound : Sound component138Node60Box :=
  sound_of_literal_split component138Node60Box component138Node44Box component138Node59Box
    .k (29/8) (by rfl) (by rfl)
    component138Node44_sound component138Node59_sound

noncomputable def component138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
theorem component138_sound : Sound component138Box :=
  sound_of_literal_split component138Box component138Node30Box component138Node60Box
    .chi (17/32) (by rfl) (by rfl)
    component138Node30_sound component138Node60_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
