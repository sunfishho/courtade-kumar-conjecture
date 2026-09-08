import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf5381Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5381Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714479360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2331922815/2147483648) }, upper := { exponent := 1, mantissa := (35905/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431891711/137428958720) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5381InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5381LocalValidity :
    LeafFacts leaf5381Box leaf5381Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5381Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714479360) }) = true
      norm_num [leaf5381Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5381CertificateValid :
    WideCertificateValid leaf5381Box leaf5381Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi289ValidityFacts
    leaf5381LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5381CoverageChecked :
    coverageCheck (innerAD leaf5381Box) leaf5381InnerLog = true := by
  rfl'

private theorem leaf5381InnerLogValid :
    leaf5381InnerLog.Valid 8 (innerAD leaf5381Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5381CoverageChecked

private noncomputable def leaf5381InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5381InputLogOnePlusV_eq :
    leaf5381InputLogOnePlusV = outerEnclosure 24
      (leaf5381Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5381RoundedFacts : LeafRoundedFacts 8
    leaf5381Certificate.logOnePlusV leaf5381InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5381InputLogOnePlusV_eq }

private noncomputable def leaf5381Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi289InputQChi innerPair250Input
    leaf5381InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5381LowerChecked :
    lowerCheck 24 leaf5381Box leaf5381Inputs = true := by
  rfl'

private theorem leaf5381CoversExact : CoversExact 8
    leaf5381Box leaf5381Certificate leaf5381InnerLog leaf5381Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi289RoundedFacts
    innerPair250RoundedFacts leaf5381RoundedFacts (by rfl)

private theorem leaf5381FlatSound : Sound leaf5381Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5381CertificateValid
    leaf5381InnerLogValid leaf5381CoversExact leaf5381LowerChecked

private noncomputable def leaf5382Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5382Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816351232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2337165373/2147483648) }, upper := { exponent := 1, mantissa := (17993/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633124425/19632702464) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5382InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5382LocalValidity :
    LeafFacts leaf5382Box leaf5382Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5382Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816351232) }) = true
      norm_num [leaf5382Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5382CertificateValid :
    WideCertificateValid leaf5382Box leaf5382Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi289ValidityFacts
    leaf5382LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5382CoverageChecked :
    coverageCheck (innerAD leaf5382Box) leaf5382InnerLog = true := by
  rfl'

private theorem leaf5382InnerLogValid :
    leaf5382InnerLog.Valid 8 (innerAD leaf5382Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5382CoverageChecked

private noncomputable def leaf5382InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5382InputLogOnePlusV_eq :
    leaf5382InputLogOnePlusV = outerEnclosure 24
      (leaf5382Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5382RoundedFacts : LeafRoundedFacts 8
    leaf5382Certificate.logOnePlusV leaf5382InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5382InputLogOnePlusV_eq }

private noncomputable def leaf5382Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi289InputQChi innerPair250Input
    leaf5382InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5382LowerChecked :
    lowerCheck 24 leaf5382Box leaf5382Inputs = true := by
  rfl'

private theorem leaf5382CoversExact : CoversExact 8
    leaf5382Box leaf5382Certificate leaf5382InnerLog leaf5382Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi289RoundedFacts
    innerPair250RoundedFacts leaf5382RoundedFacts (by rfl)

private theorem leaf5382FlatSound : Sound leaf5382Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5382CertificateValid
    leaf5382InnerLogValid leaf5382CoversExact leaf5382LowerChecked

private noncomputable def leaf5383Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5383Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634935296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2347650493/2147483648) }, upper := { exponent := 1, mantissa := (18073/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270203335/15269870592) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5383InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5383LocalValidity :
    LeafFacts leaf5383Box leaf5383Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5383Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634935296) }) = true
      norm_num [leaf5383Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5383CertificateValid :
    WideCertificateValid leaf5383Box leaf5383Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi290ValidityFacts
    leaf5383LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5383CoverageChecked :
    coverageCheck (innerAD leaf5383Box) leaf5383InnerLog = true := by
  rfl'

private theorem leaf5383InnerLogValid :
    leaf5383InnerLog.Valid 8 (innerAD leaf5383Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5383CoverageChecked

private noncomputable def leaf5383InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5383InputLogOnePlusV_eq :
    leaf5383InputLogOnePlusV = outerEnclosure 24
      (leaf5383Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5383RoundedFacts : LeafRoundedFacts 8
    leaf5383Certificate.logOnePlusV leaf5383InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5383InputLogOnePlusV_eq }

private noncomputable def leaf5383Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi290InputQChi innerPair250Input
    leaf5383InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5383LowerChecked :
    lowerCheck 24 leaf5383Box leaf5383Inputs = true := by
  rfl'

private theorem leaf5383CoversExact : CoversExact 8
    leaf5383Box leaf5383Certificate leaf5383InnerLog leaf5383Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi290RoundedFacts
    innerPair250RoundedFacts leaf5383RoundedFacts (by rfl)

private theorem leaf5383FlatSound : Sound leaf5383Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5383CertificateValid
    leaf5383InnerLogValid leaf5383CoversExact leaf5383LowerChecked

private noncomputable def leaf5384Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5384Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714396672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2352958583/2147483648) }, upper := { exponent := 1, mantissa := (9057/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431809023/137428793344) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5384InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5384LocalValidity :
    LeafFacts leaf5384Box leaf5384Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5384Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714396672) }) = true
      norm_num [leaf5384Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5384CertificateValid :
    WideCertificateValid leaf5384Box leaf5384Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi290ValidityFacts
    leaf5384LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5384CoverageChecked :
    coverageCheck (innerAD leaf5384Box) leaf5384InnerLog = true := by
  rfl'

private theorem leaf5384InnerLogValid :
    leaf5384InnerLog.Valid 8 (innerAD leaf5384Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5384CoverageChecked

private noncomputable def leaf5384InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5384InputLogOnePlusV_eq :
    leaf5384InputLogOnePlusV = outerEnclosure 24
      (leaf5384Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5384RoundedFacts : LeafRoundedFacts 8
    leaf5384Certificate.logOnePlusV leaf5384InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5384InputLogOnePlusV_eq }

private noncomputable def leaf5384Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5384InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5384LowerChecked :
    lowerCheck 24 leaf5384Box leaf5384Inputs = true := by
  rfl'

private theorem leaf5384CoversExact : CoversExact 8
    leaf5384Box leaf5384Certificate leaf5384InnerLog leaf5384Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5384RoundedFacts (by rfl)

private theorem leaf5384FlatSound : Sound leaf5384Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5384CertificateValid
    leaf5384InnerLogValid leaf5384CoversExact leaf5384LowerChecked

private noncomputable def leaf5385Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5385Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714437888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2342407931/2147483648) }, upper := { exponent := 1, mantissa := (36067/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431850239/137428875776) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5385InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5385LocalValidity :
    LeafFacts leaf5385Box leaf5385Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5385Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714437888) }) = true
      norm_num [leaf5385Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5385CertificateValid :
    WideCertificateValid leaf5385Box leaf5385Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi289ValidityFacts
    leaf5385LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5385CoverageChecked :
    coverageCheck (innerAD leaf5385Box) leaf5385InnerLog = true := by
  rfl'

private theorem leaf5385InnerLogValid :
    leaf5385InnerLog.Valid 8 (innerAD leaf5385Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5385CoverageChecked

private noncomputable def leaf5385InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5385InputLogOnePlusV_eq :
    leaf5385InputLogOnePlusV = outerEnclosure 24
      (leaf5385Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5385RoundedFacts : LeafRoundedFacts 8
    leaf5385Certificate.logOnePlusV leaf5385InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5385InputLogOnePlusV_eq }

private noncomputable def leaf5385Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi289InputQChi innerPair250Input
    leaf5385InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5385LowerChecked :
    lowerCheck 24 leaf5385Box leaf5385Inputs = true := by
  rfl'

private theorem leaf5385CoversExact : CoversExact 8
    leaf5385Box leaf5385Certificate leaf5385InnerLog leaf5385Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi289RoundedFacts
    innerPair250RoundedFacts leaf5385RoundedFacts (by rfl)

private theorem leaf5385FlatSound : Sound leaf5385Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5385CertificateValid
    leaf5385InnerLogValid leaf5385CoversExact leaf5385LowerChecked

private noncomputable def leaf5386Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5386Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714417152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2347650489/2147483648) }, upper := { exponent := 1, mantissa := (9037/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431829503/137428834304) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5386InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5386LocalValidity :
    LeafFacts leaf5386Box leaf5386Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5386Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714417152) }) = true
      norm_num [leaf5386Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5386CertificateValid :
    WideCertificateValid leaf5386Box leaf5386Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi289ValidityFacts
    leaf5386LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5386CoverageChecked :
    coverageCheck (innerAD leaf5386Box) leaf5386InnerLog = true := by
  rfl'

private theorem leaf5386InnerLogValid :
    leaf5386InnerLog.Valid 8 (innerAD leaf5386Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5386CoverageChecked

private noncomputable def leaf5386InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5386InputLogOnePlusV_eq :
    leaf5386InputLogOnePlusV = outerEnclosure 24
      (leaf5386Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5386RoundedFacts : LeafRoundedFacts 8
    leaf5386Certificate.logOnePlusV leaf5386InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5386InputLogOnePlusV_eq }

private noncomputable def leaf5386Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi289InputQChi innerPair250Input
    leaf5386InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5386LowerChecked :
    lowerCheck 24 leaf5386Box leaf5386Inputs = true := by
  rfl'

private theorem leaf5386CoversExact : CoversExact 8
    leaf5386Box leaf5386Certificate leaf5386InnerLog leaf5386Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi289RoundedFacts
    innerPair250RoundedFacts leaf5386RoundedFacts (by rfl)

private theorem leaf5386FlatSound : Sound leaf5386Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5386CertificateValid
    leaf5386InnerLogValid leaf5386CoversExact leaf5386LowerChecked

private noncomputable def leaf5387Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5387Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714375680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2358266673/2147483648) }, upper := { exponent := 1, mantissa := (18155/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431788031/137428751360) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5387InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5387LocalValidity :
    LeafFacts leaf5387Box leaf5387Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5387Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714375680) }) = true
      norm_num [leaf5387Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5387CertificateValid :
    WideCertificateValid leaf5387Box leaf5387Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi290ValidityFacts
    leaf5387LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5387CoverageChecked :
    coverageCheck (innerAD leaf5387Box) leaf5387InnerLog = true := by
  rfl'

private theorem leaf5387InnerLogValid :
    leaf5387InnerLog.Valid 8 (innerAD leaf5387Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5387CoverageChecked

private noncomputable def leaf5387InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5387InputLogOnePlusV_eq :
    leaf5387InputLogOnePlusV = outerEnclosure 24
      (leaf5387Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5387RoundedFacts : LeafRoundedFacts 8
    leaf5387Certificate.logOnePlusV leaf5387InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5387InputLogOnePlusV_eq }

private noncomputable def leaf5387Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5387InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5387LowerChecked :
    lowerCheck 24 leaf5387Box leaf5387Inputs = true := by
  rfl'

private theorem leaf5387CoversExact : CoversExact 8
    leaf5387Box leaf5387Certificate leaf5387InnerLog leaf5387Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5387RoundedFacts (by rfl)

private theorem leaf5387FlatSound : Sound leaf5387Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5387CertificateValid
    leaf5387InnerLogValid leaf5387CoversExact leaf5387LowerChecked

private noncomputable def leaf5388Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5388Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3272257731/3272112128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2363574763/2147483648) }, upper := { exponent := 1, mantissa := (4549/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6544369859/6544224256) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5388InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5388LocalValidity :
    LeafFacts leaf5388Box leaf5388Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5388Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3272257731/3272112128) }) = true
      norm_num [leaf5388Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5388CertificateValid :
    WideCertificateValid leaf5388Box leaf5388Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi290ValidityFacts
    leaf5388LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5388CoverageChecked :
    coverageCheck (innerAD leaf5388Box) leaf5388InnerLog = true := by
  rfl'

private theorem leaf5388InnerLogValid :
    leaf5388InnerLog.Valid 8 (innerAD leaf5388Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5388CoverageChecked

private noncomputable def leaf5388InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5388InputLogOnePlusV_eq :
    leaf5388InputLogOnePlusV = outerEnclosure 24
      (leaf5388Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5388RoundedFacts : LeafRoundedFacts 8
    leaf5388Certificate.logOnePlusV leaf5388InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5388InputLogOnePlusV_eq }

private noncomputable def leaf5388Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5388InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5388LowerChecked :
    lowerCheck 24 leaf5388Box leaf5388Inputs = true := by
  rfl'

private theorem leaf5388CoversExact : CoversExact 8
    leaf5388Box leaf5388Certificate leaf5388InnerLog leaf5388Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5388RoundedFacts (by rfl)

private theorem leaf5388FlatSound : Sound leaf5388Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5388CertificateValid
    leaf5388InnerLogValid leaf5388CoversExact leaf5388LowerChecked

private noncomputable def leaf5389Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5389Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742471/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216592128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2363378171/2147483648) }, upper := { exponent := 1, mantissa := (36387/32768) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433282849/4433184256) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5389InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5389LocalValidity :
    LeafFacts leaf5389Box leaf5389Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5389Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216592128) }) = true
      norm_num [leaf5389Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5389CertificateValid :
    WideCertificateValid leaf5389Box leaf5389Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi291ValidityFacts
    leaf5389LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5389CoverageChecked :
    coverageCheck (innerAD leaf5389Box) leaf5389InnerLog = true := by
  rfl'

private theorem leaf5389InnerLogValid :
    leaf5389InnerLog.Valid 8 (innerAD leaf5389Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5389CoverageChecked

private noncomputable def leaf5389InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5389InputLogOnePlusV_eq :
    leaf5389InputLogOnePlusV = outerEnclosure 24
      (leaf5389Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5389RoundedFacts : LeafRoundedFacts 8
    leaf5389Certificate.logOnePlusV leaf5389InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5389InputLogOnePlusV_eq }

private noncomputable def leaf5389Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5389InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5389LowerChecked :
    lowerCheck 24 leaf5389Box leaf5389Inputs = true := by
  rfl'

private theorem leaf5389CoversExact : CoversExact 8
    leaf5389Box leaf5389Certificate leaf5389InnerLog leaf5389Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5389RoundedFacts (by rfl)

private theorem leaf5389FlatSound : Sound leaf5389Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5389CertificateValid
    leaf5389InnerLogValid leaf5389CoversExact leaf5389LowerChecked

private noncomputable def leaf5390Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5390Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634926080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2368751793/2147483648) }, upper := { exponent := 1, mantissa := (18235/16384) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270194119/15269852160) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5390InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5390LocalValidity :
    LeafFacts leaf5390Box leaf5390Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5390Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634926080) }) = true
      norm_num [leaf5390Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5390CertificateValid :
    WideCertificateValid leaf5390Box leaf5390Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi291ValidityFacts
    leaf5390LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5390CoverageChecked :
    coverageCheck (innerAD leaf5390Box) leaf5390InnerLog = true := by
  rfl'

private theorem leaf5390InnerLogValid :
    leaf5390InnerLog.Valid 8 (innerAD leaf5390Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5390CoverageChecked

private noncomputable def leaf5390InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5390InputLogOnePlusV_eq :
    leaf5390InputLogOnePlusV = outerEnclosure 24
      (leaf5390Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5390RoundedFacts : LeafRoundedFacts 8
    leaf5390Certificate.logOnePlusV leaf5390InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5390InputLogOnePlusV_eq }

private noncomputable def leaf5390Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5390InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5390LowerChecked :
    lowerCheck 24 leaf5390Box leaf5390Inputs = true := by
  rfl'

private theorem leaf5390CoversExact : CoversExact 8
    leaf5390Box leaf5390Certificate leaf5390InnerLog leaf5390Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5390RoundedFacts (by rfl)

private theorem leaf5390FlatSound : Sound leaf5390Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5390CertificateValid
    leaf5390InnerLogValid leaf5390CoversExact leaf5390LowerChecked

private noncomputable def leaf5391Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5391Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742473/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714294272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2379105849/2147483648) }, upper := { exponent := 1, mantissa := (9157/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431706623/137428588544) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf5391InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5391LocalValidity :
    LeafFacts leaf5391Box leaf5391Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5391Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714294272) }) = true
      norm_num [leaf5391Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5391CertificateValid :
    WideCertificateValid leaf5391Box leaf5391Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi292ValidityFacts
    leaf5391LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5391CoverageChecked :
    coverageCheck (innerAD leaf5391Box) leaf5391InnerLog = true := by
  rfl'

private theorem leaf5391InnerLogValid :
    leaf5391InnerLog.Valid 8 (innerAD leaf5391Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5391CoverageChecked

private noncomputable def leaf5391InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5391InputLogOnePlusV_eq :
    leaf5391InputLogOnePlusV = outerEnclosure 24
      (leaf5391Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5391RoundedFacts : LeafRoundedFacts 8
    leaf5391Certificate.logOnePlusV leaf5391InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5391InputLogOnePlusV_eq }

private noncomputable def leaf5391Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi292InputQChi innerPair256Input
    leaf5391InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5391LowerChecked :
    lowerCheck 24 leaf5391Box leaf5391Inputs = true := by
  rfl'

private theorem leaf5391CoversExact : CoversExact 8
    leaf5391Box leaf5391Certificate leaf5391InnerLog leaf5391Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi292RoundedFacts
    innerPair256RoundedFacts leaf5391RoundedFacts (by rfl)

private theorem leaf5391FlatSound : Sound leaf5391Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5391CertificateValid
    leaf5391InnerLogValid leaf5391CoversExact leaf5391LowerChecked

private noncomputable def leaf5392Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5392Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714272768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2384545003/2147483648) }, upper := { exponent := 1, mantissa := (4589/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431685119/137428545536) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf5392InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5392LocalValidity :
    LeafFacts leaf5392Box leaf5392Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5392Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714272768) }) = true
      norm_num [leaf5392Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5392CertificateValid :
    WideCertificateValid leaf5392Box leaf5392Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi292ValidityFacts
    leaf5392LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5392CoverageChecked :
    coverageCheck (innerAD leaf5392Box) leaf5392InnerLog = true := by
  rfl'

private theorem leaf5392InnerLogValid :
    leaf5392InnerLog.Valid 8 (innerAD leaf5392Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5392CoverageChecked

private noncomputable def leaf5392InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5392InputLogOnePlusV_eq :
    leaf5392InputLogOnePlusV = outerEnclosure 24
      (leaf5392Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5392RoundedFacts : LeafRoundedFacts 8
    leaf5392Certificate.logOnePlusV leaf5392InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5392InputLogOnePlusV_eq }

private noncomputable def leaf5392Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi292InputQChi innerPair256Input
    leaf5392InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5392LowerChecked :
    lowerCheck 24 leaf5392Box leaf5392Inputs = true := by
  rfl'

private theorem leaf5392CoversExact : CoversExact 8
    leaf5392Box leaf5392Certificate leaf5392InnerLog leaf5392Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi292RoundedFacts
    innerPair256RoundedFacts leaf5392RoundedFacts (by rfl)

private theorem leaf5392FlatSound : Sound leaf5392Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5392CertificateValid
    leaf5392InnerLogValid leaf5392CoversExact leaf5392LowerChecked

private noncomputable def leaf5393Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5393Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816330496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2374125415/2147483648) }, upper := { exponent := 1, mantissa := (36553/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633103689/19632660992) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5393InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5393LocalValidity :
    LeafFacts leaf5393Box leaf5393Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5393Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816330496) }) = true
      norm_num [leaf5393Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5393CertificateValid :
    WideCertificateValid leaf5393Box leaf5393Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi291ValidityFacts
    leaf5393LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5393CoverageChecked :
    coverageCheck (innerAD leaf5393Box) leaf5393InnerLog = true := by
  rfl'

private theorem leaf5393InnerLogValid :
    leaf5393InnerLog.Valid 8 (innerAD leaf5393Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5393CoverageChecked

private noncomputable def leaf5393InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5393InputLogOnePlusV_eq :
    leaf5393InputLogOnePlusV = outerEnclosure 24
      (leaf5393Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5393RoundedFacts : LeafRoundedFacts 8
    leaf5393Certificate.logOnePlusV leaf5393InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5393InputLogOnePlusV_eq }

private noncomputable def leaf5393Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5393InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5393LowerChecked :
    lowerCheck 24 leaf5393Box leaf5393Inputs = true := by
  rfl'

private theorem leaf5393CoversExact : CoversExact 8
    leaf5393Box leaf5393Certificate leaf5393InnerLog leaf5393Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5393RoundedFacts (by rfl)

private theorem leaf5393FlatSound : Sound leaf5393Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5393CertificateValid
    leaf5393InnerLogValid leaf5393CoversExact leaf5393LowerChecked

private noncomputable def leaf5394Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5394Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714292224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2379499037/2147483648) }, upper := { exponent := 1, mantissa := (9159/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431704575/137428584448) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5394InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5394LocalValidity :
    LeafFacts leaf5394Box leaf5394Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5394Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714292224) }) = true
      norm_num [leaf5394Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5394CertificateValid :
    WideCertificateValid leaf5394Box leaf5394Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi291ValidityFacts
    leaf5394LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5394CoverageChecked :
    coverageCheck (innerAD leaf5394Box) leaf5394InnerLog = true := by
  rfl'

private theorem leaf5394InnerLogValid :
    leaf5394InnerLog.Valid 8 (innerAD leaf5394Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5394CoverageChecked

private noncomputable def leaf5394InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5394InputLogOnePlusV_eq :
    leaf5394InputLogOnePlusV = outerEnclosure 24
      (leaf5394Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5394RoundedFacts : LeafRoundedFacts 8
    leaf5394Certificate.logOnePlusV leaf5394InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5394InputLogOnePlusV_eq }

private noncomputable def leaf5394Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5394InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5394LowerChecked :
    lowerCheck 24 leaf5394Box leaf5394Inputs = true := by
  rfl'

private theorem leaf5394CoversExact : CoversExact 8
    leaf5394Box leaf5394Certificate leaf5394InnerLog leaf5394Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5394RoundedFacts (by rfl)

private theorem leaf5394FlatSound : Sound leaf5394Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5394CertificateValid
    leaf5394InnerLogValid leaf5394CoversExact leaf5394LowerChecked

private noncomputable def leaf5395Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5395Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714251264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2389984157/2147483648) }, upper := { exponent := 1, mantissa := (9199/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431663615/137428502528) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5395InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5395LocalValidity :
    LeafFacts leaf5395Box leaf5395Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5395Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714251264) }) = true
      norm_num [leaf5395Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5395CertificateValid :
    WideCertificateValid leaf5395Box leaf5395Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi292ValidityFacts
    leaf5395LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5395CoverageChecked :
    coverageCheck (innerAD leaf5395Box) leaf5395InnerLog = true := by
  rfl'

private theorem leaf5395InnerLogValid :
    leaf5395InnerLog.Valid 8 (innerAD leaf5395Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5395CoverageChecked

private noncomputable def leaf5395InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5395InputLogOnePlusV_eq :
    leaf5395InputLogOnePlusV = outerEnclosure 24
      (leaf5395Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5395RoundedFacts : LeafRoundedFacts 8
    leaf5395Certificate.logOnePlusV leaf5395InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5395InputLogOnePlusV_eq }

private noncomputable def leaf5395Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi292InputQChi innerPair256Input
    leaf5395InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5395LowerChecked :
    lowerCheck 24 leaf5395Box leaf5395Inputs = true := by
  rfl'

private theorem leaf5395CoversExact : CoversExact 8
    leaf5395Box leaf5395Certificate leaf5395InnerLog leaf5395Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi292RoundedFacts
    innerPair256RoundedFacts leaf5395RoundedFacts (by rfl)

private theorem leaf5395FlatSound : Sound leaf5395Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5395CertificateValid
    leaf5395InnerLogValid leaf5395CoversExact leaf5395LowerChecked

private noncomputable def leaf5396Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5396Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714229760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2395423311/2147483648) }, upper := { exponent := 1, mantissa := (2305/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431642111/137428459520) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5396InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5396LocalValidity :
    LeafFacts leaf5396Box leaf5396Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5396Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714229760) }) = true
      norm_num [leaf5396Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5396CertificateValid :
    WideCertificateValid leaf5396Box leaf5396Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi292ValidityFacts
    leaf5396LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5396CoverageChecked :
    coverageCheck (innerAD leaf5396Box) leaf5396InnerLog = true := by
  rfl'

private theorem leaf5396InnerLogValid :
    leaf5396InnerLog.Valid 8 (innerAD leaf5396Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5396CoverageChecked

private noncomputable def leaf5396InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5396InputLogOnePlusV_eq :
    leaf5396InputLogOnePlusV = outerEnclosure 24
      (leaf5396Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5396RoundedFacts : LeafRoundedFacts 8
    leaf5396Certificate.logOnePlusV leaf5396InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5396InputLogOnePlusV_eq }

private noncomputable def leaf5396Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi292InputQChi innerPair257Input
    leaf5396InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5396LowerChecked :
    lowerCheck 24 leaf5396Box leaf5396Inputs = true := by
  rfl'

private theorem leaf5396CoversExact : CoversExact 8
    leaf5396Box leaf5396Certificate leaf5396InnerLog leaf5396Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi292RoundedFacts
    innerPair257RoundedFacts leaf5396RoundedFacts (by rfl)

private theorem leaf5396FlatSound : Sound leaf5396Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5396CertificateValid
    leaf5396InnerLogValid leaf5396CoversExact leaf5396LowerChecked

private noncomputable def leaf5397Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5397Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742475/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714396416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2352893047/2147483648) }, upper := { exponent := 1, mantissa := (36229/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431808767/137428792832) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5397InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5397LocalValidity :
    LeafFacts leaf5397Box leaf5397Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5397Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714396416) }) = true
      norm_num [leaf5397Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5397CertificateValid :
    WideCertificateValid leaf5397Box leaf5397Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi289ValidityFacts
    leaf5397LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5397CoverageChecked :
    coverageCheck (innerAD leaf5397Box) leaf5397InnerLog = true := by
  rfl'

private theorem leaf5397InnerLogValid :
    leaf5397InnerLog.Valid 8 (innerAD leaf5397Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5397CoverageChecked

private noncomputable def leaf5397InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5397InputLogOnePlusV_eq :
    leaf5397InputLogOnePlusV = outerEnclosure 24
      (leaf5397Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5397RoundedFacts : LeafRoundedFacts 8
    leaf5397Certificate.logOnePlusV leaf5397InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5397InputLogOnePlusV_eq }

private noncomputable def leaf5397Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5397InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5397LowerChecked :
    lowerCheck 24 leaf5397Box leaf5397Inputs = true := by
  rfl'

private theorem leaf5397CoversExact : CoversExact 8
    leaf5397Box leaf5397Certificate leaf5397InnerLog leaf5397Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5397RoundedFacts (by rfl)

private theorem leaf5397FlatSound : Sound leaf5397Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5397CertificateValid
    leaf5397InnerLogValid leaf5397CoversExact leaf5397LowerChecked

private noncomputable def leaf5398Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5398Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714375680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2358135605/2147483648) }, upper := { exponent := 1, mantissa := (18155/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431788031/137428751360) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5398InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5398LocalValidity :
    LeafFacts leaf5398Box leaf5398Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5398Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714375680) }) = true
      norm_num [leaf5398Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5398CertificateValid :
    WideCertificateValid leaf5398Box leaf5398Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi289ValidityFacts
    leaf5398LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5398CoverageChecked :
    coverageCheck (innerAD leaf5398Box) leaf5398InnerLog = true := by
  rfl'

private theorem leaf5398InnerLogValid :
    leaf5398InnerLog.Valid 8 (innerAD leaf5398Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5398CoverageChecked

private noncomputable def leaf5398InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5398InputLogOnePlusV_eq :
    leaf5398InputLogOnePlusV = outerEnclosure 24
      (leaf5398Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5398RoundedFacts : LeafRoundedFacts 8
    leaf5398Certificate.logOnePlusV leaf5398InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5398InputLogOnePlusV_eq }

private noncomputable def leaf5398Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5398InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5398LowerChecked :
    lowerCheck 24 leaf5398Box leaf5398Inputs = true := by
  rfl'

private theorem leaf5398CoversExact : CoversExact 8
    leaf5398Box leaf5398Certificate leaf5398InnerLog leaf5398Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5398RoundedFacts (by rfl)

private theorem leaf5398FlatSound : Sound leaf5398Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5398CertificateValid
    leaf5398InnerLogValid leaf5398CoversExact leaf5398LowerChecked

private noncomputable def leaf5399Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5399Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742477/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714333696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2368882853/2147483648) }, upper := { exponent := 1, mantissa := (18237/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431746047/137428667392) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5399InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5399LocalValidity :
    LeafFacts leaf5399Box leaf5399Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5399Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714333696) }) = true
      norm_num [leaf5399Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5399CertificateValid :
    WideCertificateValid leaf5399Box leaf5399Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi290ValidityFacts
    leaf5399LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5399CoverageChecked :
    coverageCheck (innerAD leaf5399Box) leaf5399InnerLog = true := by
  rfl'

private theorem leaf5399InnerLogValid :
    leaf5399InnerLog.Valid 8 (innerAD leaf5399Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5399CoverageChecked

private noncomputable def leaf5399InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5399InputLogOnePlusV_eq :
    leaf5399InputLogOnePlusV = outerEnclosure 24
      (leaf5399Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5399RoundedFacts : LeafRoundedFacts 8
    leaf5399Certificate.logOnePlusV leaf5399InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5399InputLogOnePlusV_eq }

private noncomputable def leaf5399Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5399InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5399LowerChecked :
    lowerCheck 24 leaf5399Box leaf5399Inputs = true := by
  rfl'

private theorem leaf5399CoversExact : CoversExact 8
    leaf5399Box leaf5399Certificate leaf5399InnerLog leaf5399Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5399RoundedFacts (by rfl)

private theorem leaf5399FlatSound : Sound leaf5399Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5399CertificateValid
    leaf5399InnerLogValid leaf5399CoversExact leaf5399LowerChecked

private noncomputable def leaf5400Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5400Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714312704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2374190943/2147483648) }, upper := { exponent := 1, mantissa := (9139/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431725055/137428625408) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5400InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5400LocalValidity :
    LeafFacts leaf5400Box leaf5400Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5400Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714312704) }) = true
      norm_num [leaf5400Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5400CertificateValid :
    WideCertificateValid leaf5400Box leaf5400Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi290ValidityFacts
    leaf5400LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5400CoverageChecked :
    coverageCheck (innerAD leaf5400Box) leaf5400InnerLog = true := by
  rfl'

private theorem leaf5400InnerLogValid :
    leaf5400InnerLog.Valid 8 (innerAD leaf5400Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5400CoverageChecked

private noncomputable def leaf5400InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5400InputLogOnePlusV_eq :
    leaf5400InputLogOnePlusV = outerEnclosure 24
      (leaf5400Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5400RoundedFacts : LeafRoundedFacts 8
    leaf5400Certificate.logOnePlusV leaf5400InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5400InputLogOnePlusV_eq }

private noncomputable def leaf5400Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5400InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5400LowerChecked :
    lowerCheck 24 leaf5400Box leaf5400Inputs = true := by
  rfl'

private theorem leaf5400CoversExact : CoversExact 8
    leaf5400Box leaf5400Certificate leaf5400InnerLog leaf5400Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5400RoundedFacts (by rfl)

private theorem leaf5400FlatSound : Sound leaf5400Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5400CertificateValid
    leaf5400InnerLogValid leaf5400CoversExact leaf5400LowerChecked

private noncomputable def leaf5401Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5401Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714354944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2363378163/2147483648) }, upper := { exponent := 1, mantissa := (36391/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431767295/137428709888) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5401InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5401LocalValidity :
    LeafFacts leaf5401Box leaf5401Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5401Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714354944) }) = true
      norm_num [leaf5401Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5401CertificateValid :
    WideCertificateValid leaf5401Box leaf5401Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi289ValidityFacts
    leaf5401LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5401CoverageChecked :
    coverageCheck (innerAD leaf5401Box) leaf5401InnerLog = true := by
  rfl'

private theorem leaf5401InnerLogValid :
    leaf5401InnerLog.Valid 8 (innerAD leaf5401Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5401CoverageChecked

private noncomputable def leaf5401InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5401InputLogOnePlusV_eq :
    leaf5401InputLogOnePlusV = outerEnclosure 24
      (leaf5401Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5401RoundedFacts : LeafRoundedFacts 8
    leaf5401Certificate.logOnePlusV leaf5401InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5401InputLogOnePlusV_eq }

private noncomputable def leaf5401Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5401InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5401LowerChecked :
    lowerCheck 24 leaf5401Box leaf5401Inputs = true := by
  rfl'

private theorem leaf5401CoversExact : CoversExact 8
    leaf5401Box leaf5401Certificate leaf5401InnerLog leaf5401Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5401RoundedFacts (by rfl)

private theorem leaf5401FlatSound : Sound leaf5401Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5401CertificateValid
    leaf5401InnerLogValid leaf5401CoversExact leaf5401LowerChecked

private noncomputable def leaf5402Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5402Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714334208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2368620721/2147483648) }, upper := { exponent := 1, mantissa := (4559/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431746559/137428668416) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5402InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5402LocalValidity :
    LeafFacts leaf5402Box leaf5402Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5402Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714334208) }) = true
      norm_num [leaf5402Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5402CertificateValid :
    WideCertificateValid leaf5402Box leaf5402Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi289ValidityFacts
    leaf5402LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5402CoverageChecked :
    coverageCheck (innerAD leaf5402Box) leaf5402InnerLog = true := by
  rfl'

private theorem leaf5402InnerLogValid :
    leaf5402InnerLog.Valid 8 (innerAD leaf5402Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5402CoverageChecked

private noncomputable def leaf5402InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5402InputLogOnePlusV_eq :
    leaf5402InputLogOnePlusV = outerEnclosure 24
      (leaf5402Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5402RoundedFacts : LeafRoundedFacts 8
    leaf5402Certificate.logOnePlusV leaf5402InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5402InputLogOnePlusV_eq }

private noncomputable def leaf5402Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi289InputQChi innerPair256Input
    leaf5402InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5402LowerChecked :
    lowerCheck 24 leaf5402Box leaf5402Inputs = true := by
  rfl'

private theorem leaf5402CoversExact : CoversExact 8
    leaf5402Box leaf5402Certificate leaf5402InnerLog leaf5402Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi289RoundedFacts
    innerPair256RoundedFacts leaf5402RoundedFacts (by rfl)

private theorem leaf5402FlatSound : Sound leaf5402Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5402CertificateValid
    leaf5402InnerLogValid leaf5402CoversExact leaf5402LowerChecked

private noncomputable def leaf5403Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5403Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (532693119/532668928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2379499033/2147483648) }, upper := { exponent := 1, mantissa := (18319/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1065362047/1065337856) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5403InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5403LocalValidity :
    LeafFacts leaf5403Box leaf5403Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5403Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (532693119/532668928) }) = true
      norm_num [leaf5403Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5403CertificateValid :
    WideCertificateValid leaf5403Box leaf5403Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi290ValidityFacts
    leaf5403LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5403CoverageChecked :
    coverageCheck (innerAD leaf5403Box) leaf5403InnerLog = true := by
  rfl'

private theorem leaf5403InnerLogValid :
    leaf5403InnerLog.Valid 8 (innerAD leaf5403Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5403CoverageChecked

private noncomputable def leaf5403InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5403InputLogOnePlusV_eq :
    leaf5403InputLogOnePlusV = outerEnclosure 24
      (leaf5403Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5403RoundedFacts : LeafRoundedFacts 8
    leaf5403Certificate.logOnePlusV leaf5403InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5403InputLogOnePlusV_eq }

private noncomputable def leaf5403Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5403InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5403LowerChecked :
    lowerCheck 24 leaf5403Box leaf5403Inputs = true := by
  rfl'

private theorem leaf5403CoversExact : CoversExact 8
    leaf5403Box leaf5403Certificate leaf5403InnerLog leaf5403Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5403RoundedFacts (by rfl)

private theorem leaf5403FlatSound : Sound leaf5403Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5403CertificateValid
    leaf5403InnerLogValid leaf5403CoversExact leaf5403LowerChecked

private noncomputable def leaf5404Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5404Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714270720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2384807123/2147483648) }, upper := { exponent := 1, mantissa := (2295/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431683071/137428541440) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5404InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5404LocalValidity :
    LeafFacts leaf5404Box leaf5404Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5404Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714270720) }) = true
      norm_num [leaf5404Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5404CertificateValid :
    WideCertificateValid leaf5404Box leaf5404Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi290ValidityFacts
    leaf5404LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5404CoverageChecked :
    coverageCheck (innerAD leaf5404Box) leaf5404InnerLog = true := by
  rfl'

private theorem leaf5404InnerLogValid :
    leaf5404InnerLog.Valid 8 (innerAD leaf5404Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5404CoverageChecked

private noncomputable def leaf5404InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5404InputLogOnePlusV_eq :
    leaf5404InputLogOnePlusV = outerEnclosure 24
      (leaf5404Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5404RoundedFacts : LeafRoundedFacts 8
    leaf5404Certificate.logOnePlusV leaf5404InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5404InputLogOnePlusV_eq }

private noncomputable def leaf5404Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi290InputQChi innerPair256Input
    leaf5404InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5404LowerChecked :
    lowerCheck 24 leaf5404Box leaf5404Inputs = true := by
  rfl'

private theorem leaf5404CoversExact : CoversExact 8
    leaf5404Box leaf5404Certificate leaf5404InnerLog leaf5404Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi290RoundedFacts
    innerPair256RoundedFacts leaf5404RoundedFacts (by rfl)

private theorem leaf5404FlatSound : Sound leaf5404Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5404CertificateValid
    leaf5404InnerLogValid leaf5404CoversExact leaf5404LowerChecked

private noncomputable def leaf5405Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5405Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904756992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2384872659/2147483648) }, upper := { exponent := 1, mantissa := (36719/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810561109/45809513984) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5405InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5405LocalValidity :
    LeafFacts leaf5405Box leaf5405Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5405Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904756992) }) = true
      norm_num [leaf5405Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5405CertificateValid :
    WideCertificateValid leaf5405Box leaf5405Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi291ValidityFacts
    leaf5405LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5405CoverageChecked :
    coverageCheck (innerAD leaf5405Box) leaf5405InnerLog = true := by
  rfl'

private theorem leaf5405InnerLogValid :
    leaf5405InnerLog.Valid 8 (innerAD leaf5405Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5405CoverageChecked

private noncomputable def leaf5405InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5405InputLogOnePlusV_eq :
    leaf5405InputLogOnePlusV = outerEnclosure 24
      (leaf5405Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5405RoundedFacts : LeafRoundedFacts 8
    leaf5405Certificate.logOnePlusV leaf5405InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5405InputLogOnePlusV_eq }

private noncomputable def leaf5405Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5405InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5405LowerChecked :
    lowerCheck 24 leaf5405Box leaf5405Inputs = true := by
  rfl'

private theorem leaf5405CoversExact : CoversExact 8
    leaf5405Box leaf5405Certificate leaf5405InnerLog leaf5405Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5405RoundedFacts (by rfl)

private theorem leaf5405FlatSound : Sound leaf5405Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5405CertificateValid
    leaf5405InnerLogValid leaf5405CoversExact leaf5405LowerChecked

private noncomputable def leaf5406Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5406Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714249728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2390246281/2147483648) }, upper := { exponent := 1, mantissa := (18401/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431662079/137428499456) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5406InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5406LocalValidity :
    LeafFacts leaf5406Box leaf5406Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5406Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714249728) }) = true
      norm_num [leaf5406Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5406CertificateValid :
    WideCertificateValid leaf5406Box leaf5406Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi291ValidityFacts
    leaf5406LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5406CoverageChecked :
    coverageCheck (innerAD leaf5406Box) leaf5406InnerLog = true := by
  rfl'

private theorem leaf5406InnerLogValid :
    leaf5406InnerLog.Valid 8 (innerAD leaf5406Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5406CoverageChecked

private noncomputable def leaf5406InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5406InputLogOnePlusV_eq :
    leaf5406InputLogOnePlusV = outerEnclosure 24
      (leaf5406Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5406RoundedFacts : LeafRoundedFacts 8
    leaf5406Certificate.logOnePlusV leaf5406InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5406InputLogOnePlusV_eq }

private noncomputable def leaf5406Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5406InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5406LowerChecked :
    lowerCheck 24 leaf5406Box leaf5406Inputs = true := by
  rfl'

private theorem leaf5406CoversExact : CoversExact 8
    leaf5406Box leaf5406Certificate leaf5406InnerLog leaf5406Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5406RoundedFacts (by rfl)

private theorem leaf5406FlatSound : Sound leaf5406Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5406CertificateValid
    leaf5406InnerLogValid leaf5406CoversExact leaf5406LowerChecked

private noncomputable def leaf5407Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5407Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714208256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2400862465/2147483648) }, upper := { exponent := 1, mantissa := (9241/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431620607/137428416512) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5407InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5407LocalValidity :
    LeafFacts leaf5407Box leaf5407Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5407Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714208256) }) = true
      norm_num [leaf5407Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5407CertificateValid :
    WideCertificateValid leaf5407Box leaf5407Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi292ValidityFacts
    leaf5407LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5407CoverageChecked :
    coverageCheck (innerAD leaf5407Box) leaf5407InnerLog = true := by
  rfl'

private theorem leaf5407InnerLogValid :
    leaf5407InnerLog.Valid 8 (innerAD leaf5407Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5407CoverageChecked

private noncomputable def leaf5407InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5407InputLogOnePlusV_eq :
    leaf5407InputLogOnePlusV = outerEnclosure 24
      (leaf5407Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5407RoundedFacts : LeafRoundedFacts 8
    leaf5407Certificate.logOnePlusV leaf5407InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5407InputLogOnePlusV_eq }

private noncomputable def leaf5407Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi292InputQChi innerPair257Input
    leaf5407InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5407LowerChecked :
    lowerCheck 24 leaf5407Box leaf5407Inputs = true := by
  rfl'

private theorem leaf5407CoversExact : CoversExact 8
    leaf5407Box leaf5407Certificate leaf5407InnerLog leaf5407Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi292RoundedFacts
    innerPair257RoundedFacts leaf5407RoundedFacts (by rfl)

private theorem leaf5407FlatSound : Sound leaf5407Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5407CertificateValid
    leaf5407InnerLogValid leaf5407CoversExact leaf5407LowerChecked

private noncomputable def leaf5408Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5408Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714186752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2406301619/2147483648) }, upper := { exponent := 1, mantissa := (4631/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431599103/137428373504) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5408InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5408LocalValidity :
    LeafFacts leaf5408Box leaf5408Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5408Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714186752) }) = true
      norm_num [leaf5408Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5408CertificateValid :
    WideCertificateValid leaf5408Box leaf5408Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi292ValidityFacts
    leaf5408LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5408CoverageChecked :
    coverageCheck (innerAD leaf5408Box) leaf5408InnerLog = true := by
  rfl'

private theorem leaf5408InnerLogValid :
    leaf5408InnerLog.Valid 8 (innerAD leaf5408Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5408CoverageChecked

private noncomputable def leaf5408InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5408InputLogOnePlusV_eq :
    leaf5408InputLogOnePlusV = outerEnclosure 24
      (leaf5408Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5408RoundedFacts : LeafRoundedFacts 8
    leaf5408Certificate.logOnePlusV leaf5408InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5408InputLogOnePlusV_eq }

private noncomputable def leaf5408Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi292InputQChi innerPair257Input
    leaf5408InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5408LowerChecked :
    lowerCheck 24 leaf5408Box leaf5408Inputs = true := by
  rfl'

private theorem leaf5408CoversExact : CoversExact 8
    leaf5408Box leaf5408Certificate leaf5408InnerLog leaf5408Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi292RoundedFacts
    innerPair257RoundedFacts leaf5408RoundedFacts (by rfl)

private theorem leaf5408FlatSound : Sound leaf5408Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5408CertificateValid
    leaf5408InnerLogValid leaf5408CoversExact leaf5408LowerChecked

private noncomputable def leaf5409Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5409Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714228480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2395619903/2147483648) }, upper := { exponent := 1, mantissa := (36885/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431640831/137428456960) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5409InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5409LocalValidity :
    LeafFacts leaf5409Box leaf5409Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5409Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714228480) }) = true
      norm_num [leaf5409Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5409CertificateValid :
    WideCertificateValid leaf5409Box leaf5409Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi291ValidityFacts
    leaf5409LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5409CoverageChecked :
    coverageCheck (innerAD leaf5409Box) leaf5409InnerLog = true := by
  rfl'

private theorem leaf5409InnerLogValid :
    leaf5409InnerLog.Valid 8 (innerAD leaf5409Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5409CoverageChecked

private noncomputable def leaf5409InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5409InputLogOnePlusV_eq :
    leaf5409InputLogOnePlusV = outerEnclosure 24
      (leaf5409Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5409RoundedFacts : LeafRoundedFacts 8
    leaf5409Certificate.logOnePlusV leaf5409InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5409InputLogOnePlusV_eq }

private noncomputable def leaf5409Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi291InputQChi innerPair300Input
    leaf5409InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5409LowerChecked :
    lowerCheck 24 leaf5409Box leaf5409Inputs = true := by
  rfl'

private theorem leaf5409CoversExact : CoversExact 8
    leaf5409Box leaf5409Certificate leaf5409InnerLog leaf5409Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi291RoundedFacts
    innerPair300RoundedFacts leaf5409RoundedFacts (by rfl)

private theorem leaf5409FlatSound : Sound leaf5409Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5409CertificateValid
    leaf5409InnerLogValid leaf5409CoversExact leaf5409LowerChecked

private noncomputable def leaf5410Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5410Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904735744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2400993525/2147483648) }, upper := { exponent := 1, mantissa := (4621/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810539861/45809471488) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5410InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5410LocalValidity :
    LeafFacts leaf5410Box leaf5410Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5410Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904735744) }) = true
      norm_num [leaf5410Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5410CertificateValid :
    WideCertificateValid leaf5410Box leaf5410Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi291ValidityFacts
    leaf5410LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5410CoverageChecked :
    coverageCheck (innerAD leaf5410Box) leaf5410InnerLog = true := by
  rfl'

private theorem leaf5410InnerLogValid :
    leaf5410InnerLog.Valid 8 (innerAD leaf5410Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5410CoverageChecked

private noncomputable def leaf5410InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5410InputLogOnePlusV_eq :
    leaf5410InputLogOnePlusV = outerEnclosure 24
      (leaf5410Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5410RoundedFacts : LeafRoundedFacts 8
    leaf5410Certificate.logOnePlusV leaf5410InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5410InputLogOnePlusV_eq }

private noncomputable def leaf5410Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi291InputQChi innerPair257Input
    leaf5410InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5410LowerChecked :
    lowerCheck 24 leaf5410Box leaf5410Inputs = true := by
  rfl'

private theorem leaf5410CoversExact : CoversExact 8
    leaf5410Box leaf5410Certificate leaf5410InnerLog leaf5410Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi291RoundedFacts
    innerPair257RoundedFacts leaf5410RoundedFacts (by rfl)

private theorem leaf5410FlatSound : Sound leaf5410Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5410CertificateValid
    leaf5410InnerLogValid leaf5410CoversExact leaf5410LowerChecked

private noncomputable def leaf5411Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5411Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714165248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2411740773/2147483648) }, upper := { exponent := 1, mantissa := (9283/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431577599/137428330496) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5411InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5411LocalValidity :
    LeafFacts leaf5411Box leaf5411Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5411Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714165248) }) = true
      norm_num [leaf5411Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5411CertificateValid :
    WideCertificateValid leaf5411Box leaf5411Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi292ValidityFacts
    leaf5411LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5411CoverageChecked :
    coverageCheck (innerAD leaf5411Box) leaf5411InnerLog = true := by
  rfl'

private theorem leaf5411InnerLogValid :
    leaf5411InnerLog.Valid 8 (innerAD leaf5411Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5411CoverageChecked

private noncomputable def leaf5411InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5411InputLogOnePlusV_eq :
    leaf5411InputLogOnePlusV = outerEnclosure 24
      (leaf5411Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5411RoundedFacts : LeafRoundedFacts 8
    leaf5411Certificate.logOnePlusV leaf5411InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5411InputLogOnePlusV_eq }

private noncomputable def leaf5411Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi292InputQChi innerPair257Input
    leaf5411InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5411LowerChecked :
    lowerCheck 24 leaf5411Box leaf5411Inputs = true := by
  rfl'

private theorem leaf5411CoversExact : CoversExact 8
    leaf5411Box leaf5411Certificate leaf5411InnerLog leaf5411Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi292RoundedFacts
    innerPair257RoundedFacts leaf5411RoundedFacts (by rfl)

private theorem leaf5411FlatSound : Sound leaf5411Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5411CertificateValid
    leaf5411InnerLogValid leaf5411CoversExact leaf5411LowerChecked

private noncomputable def leaf5412Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5412Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714143744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2417179927/2147483648) }, upper := { exponent := 1, mantissa := (1163/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431556095/137428287488) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5412InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5412LocalValidity :
    LeafFacts leaf5412Box leaf5412Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5412Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714143744) }) = true
      norm_num [leaf5412Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5412CertificateValid :
    WideCertificateValid leaf5412Box leaf5412Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi292ValidityFacts
    leaf5412LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5412CoverageChecked :
    coverageCheck (innerAD leaf5412Box) leaf5412InnerLog = true := by
  rfl'

private theorem leaf5412InnerLogValid :
    leaf5412InnerLog.Valid 8 (innerAD leaf5412Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5412CoverageChecked

private noncomputable def leaf5412InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5412InputLogOnePlusV_eq :
    leaf5412InputLogOnePlusV = outerEnclosure 24
      (leaf5412Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5412RoundedFacts : LeafRoundedFacts 8
    leaf5412Certificate.logOnePlusV leaf5412InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5412InputLogOnePlusV_eq }

private noncomputable def leaf5412Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi292InputQChi innerPair264Input
    leaf5412InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5412LowerChecked :
    lowerCheck 24 leaf5412Box leaf5412Inputs = true := by
  rfl'

private theorem leaf5412CoversExact : CoversExact 8
    leaf5412Box leaf5412Certificate leaf5412InnerLog leaf5412Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi292RoundedFacts
    innerPair264RoundedFacts leaf5412RoundedFacts (by rfl)

private theorem leaf5412FlatSound : Sound leaf5412Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5412CertificateValid
    leaf5412InnerLogValid leaf5412CoversExact leaf5412LowerChecked

private noncomputable def leaf5413Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5413Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357105408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1197400295/1073741824) }, upper := { exponent := 1, mantissa := (18477/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715827967/68714210816) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5413InnerLog : WideLogData :=
  innerPair641Data

set_option maxRecDepth 1000000 in
private theorem leaf5413LocalValidity :
    LeafFacts leaf5413Box leaf5413Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5413Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357105408) }) = true
      norm_num [leaf5413Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5413CertificateValid :
    WideCertificateValid leaf5413Box leaf5413Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi293ValidityFacts
    leaf5413LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5413CoverageChecked :
    coverageCheck (innerAD leaf5413Box) leaf5413InnerLog = true := by
  rfl'

private theorem leaf5413InnerLogValid :
    leaf5413InnerLog.Valid 8 (innerAD leaf5413Box) :=
  wideLogDataValid_of_cachedCheck endpoint381PositiveFacts
    endpoint382PositiveFacts.valid leaf5413CoverageChecked

private noncomputable def leaf5413InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5413InputLogOnePlusV_eq :
    leaf5413InputLogOnePlusV = outerEnclosure 24
      (leaf5413Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5413RoundedFacts : LeafRoundedFacts 8
    leaf5413Certificate.logOnePlusV leaf5413InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5413InputLogOnePlusV_eq }

private noncomputable def leaf5413Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi293InputQChi innerPair641Input
    leaf5413InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5413LowerChecked :
    lowerCheck 24 leaf5413Box leaf5413Inputs = true := by
  rfl'

private theorem leaf5413CoversExact : CoversExact 8
    leaf5413Box leaf5413Certificate leaf5413InnerLog leaf5413Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi293RoundedFacts
    innerPair641RoundedFacts leaf5413RoundedFacts (by rfl)

private theorem leaf5413FlatSound : Sound leaf5413Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5413CertificateValid
    leaf5413InnerLogValid leaf5413CoversExact leaf5413LowerChecked

private noncomputable def leaf5414Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5414Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357074432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1205264133/1073741824) }, upper := { exponent := 1, mantissa := (9299/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715796991/68714148864) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5414InnerLog : WideLogData :=
  innerPair642Data

set_option maxRecDepth 1000000 in
private theorem leaf5414LocalValidity :
    LeafFacts leaf5414Box leaf5414Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5414Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357074432) }) = true
      norm_num [leaf5414Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5414CertificateValid :
    WideCertificateValid leaf5414Box leaf5414Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi294ValidityFacts
    leaf5414LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5414CoverageChecked :
    coverageCheck (innerAD leaf5414Box) leaf5414InnerLog = true := by
  rfl'

private theorem leaf5414InnerLogValid :
    leaf5414InnerLog.Valid 8 (innerAD leaf5414Box) :=
  wideLogDataValid_of_cachedCheck endpoint383PositiveFacts
    endpoint384PositiveFacts.valid leaf5414CoverageChecked

private noncomputable def leaf5414InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5414InputLogOnePlusV_eq :
    leaf5414InputLogOnePlusV = outerEnclosure 24
      (leaf5414Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5414RoundedFacts : LeafRoundedFacts 8
    leaf5414Certificate.logOnePlusV leaf5414InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5414InputLogOnePlusV_eq }

private noncomputable def leaf5414Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi294InputQChi innerPair642Input
    leaf5414InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5414LowerChecked :
    lowerCheck 24 leaf5414Box leaf5414Inputs = true := by
  rfl'

private theorem leaf5414CoversExact : CoversExact 8
    leaf5414Box leaf5414Certificate leaf5414InnerLog leaf5414Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi294RoundedFacts
    innerPair642RoundedFacts leaf5414RoundedFacts (by rfl)

private theorem leaf5414FlatSound : Sound leaf5414Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5414CertificateValid
    leaf5414InnerLogValid leaf5414CoversExact leaf5414LowerChecked

private noncomputable def leaf5415Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5415Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742479/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714189056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2405842899/2147483648) }, upper := { exponent := 1, mantissa := (37039/32768) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431601407/137428378112) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf5415InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5415LocalValidity :
    LeafFacts leaf5415Box leaf5415Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5415Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714189056) }) = true
      norm_num [leaf5415Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5415CertificateValid :
    WideCertificateValid leaf5415Box leaf5415Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi293ValidityFacts
    leaf5415LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5415CoverageChecked :
    coverageCheck (innerAD leaf5415Box) leaf5415InnerLog = true := by
  rfl'

private theorem leaf5415InnerLogValid :
    leaf5415InnerLog.Valid 8 (innerAD leaf5415Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5415CoverageChecked

private noncomputable def leaf5415InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5415InputLogOnePlusV_eq :
    leaf5415InputLogOnePlusV = outerEnclosure 24
      (leaf5415Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5415RoundedFacts : LeafRoundedFacts 8
    leaf5415Certificate.logOnePlusV leaf5415InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5415InputLogOnePlusV_eq }

private noncomputable def leaf5415Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi293InputQChi innerPair257Input
    leaf5415InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5415LowerChecked :
    lowerCheck 24 leaf5415Box leaf5415Inputs = true := by
  rfl'

private theorem leaf5415CoversExact : CoversExact 8
    leaf5415Box leaf5415Certificate leaf5415InnerLog leaf5415Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi293RoundedFacts
    innerPair257RoundedFacts leaf5415RoundedFacts (by rfl)

private theorem leaf5415FlatSound : Sound leaf5415Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5415CertificateValid
    leaf5415InnerLogValid leaf5415CoversExact leaf5415LowerChecked

private noncomputable def leaf5416Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5416Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742481/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904722432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2411347585/2147483648) }, upper := { exponent := 1, mantissa := (9281/8192) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810526549/45809444864) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf5416InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf5416LocalValidity :
    LeafFacts leaf5416Box leaf5416Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5416Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904722432) }) = true
      norm_num [leaf5416Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5416CertificateValid :
    WideCertificateValid leaf5416Box leaf5416Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi293ValidityFacts
    leaf5416LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5416CoverageChecked :
    coverageCheck (innerAD leaf5416Box) leaf5416InnerLog = true := by
  rfl'

private theorem leaf5416InnerLogValid :
    leaf5416InnerLog.Valid 8 (innerAD leaf5416Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf5416CoverageChecked

private noncomputable def leaf5416InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629477/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5416InputLogOnePlusV_eq :
    leaf5416InputLogOnePlusV = outerEnclosure 24
      (leaf5416Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5416RoundedFacts : LeafRoundedFacts 8
    leaf5416Certificate.logOnePlusV leaf5416InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5416InputLogOnePlusV_eq }

private noncomputable def leaf5416Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi293InputQChi innerPair257Input
    leaf5416InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5416LowerChecked :
    lowerCheck 24 leaf5416Box leaf5416Inputs = true := by
  rfl'

private theorem leaf5416CoversExact : CoversExact 8
    leaf5416Box leaf5416Certificate leaf5416InnerLog leaf5416Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi293RoundedFacts
    innerPair257RoundedFacts leaf5416RoundedFacts (by rfl)

private theorem leaf5416FlatSound : Sound leaf5416Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5416CertificateValid
    leaf5416InnerLogValid leaf5416CoversExact leaf5416LowerChecked

private noncomputable def leaf5417Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5417Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357052416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1210834351/1073741824) }, upper := { exponent := 1, mantissa := (4671/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715774975/68714104832) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5417InnerLog : WideLogData :=
  innerPair643Data

set_option maxRecDepth 1000000 in
private theorem leaf5417LocalValidity :
    LeafFacts leaf5417Box leaf5417Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5417Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357052416) }) = true
      norm_num [leaf5417Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5417CertificateValid :
    WideCertificateValid leaf5417Box leaf5417Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi294ValidityFacts
    leaf5417LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5417CoverageChecked :
    coverageCheck (innerAD leaf5417Box) leaf5417InnerLog = true := by
  rfl'

private theorem leaf5417InnerLogValid :
    leaf5417InnerLog.Valid 8 (innerAD leaf5417Box) :=
  wideLogDataValid_of_cachedCheck endpoint385PositiveFacts
    endpoint386PositiveFacts.valid leaf5417CoverageChecked

private noncomputable def leaf5417InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5417InputLogOnePlusV_eq :
    leaf5417InputLogOnePlusV = outerEnclosure 24
      (leaf5417Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5417RoundedFacts : LeafRoundedFacts 8
    leaf5417Certificate.logOnePlusV leaf5417InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5417InputLogOnePlusV_eq }

private noncomputable def leaf5417Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi294InputQChi innerPair643Input
    leaf5417InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5417LowerChecked :
    lowerCheck 24 leaf5417Box leaf5417Inputs = true := by
  rfl'

private theorem leaf5417CoversExact : CoversExact 8
    leaf5417Box leaf5417Certificate leaf5417InnerLog leaf5417Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi294RoundedFacts
    innerPair643RoundedFacts leaf5417RoundedFacts (by rfl)

private theorem leaf5417FlatSound : Sound leaf5417Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5417CertificateValid
    leaf5417InnerLogValid leaf5417CoversExact leaf5417LowerChecked

private noncomputable def leaf5418Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5418Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357043456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1213127971/1073741824) }, upper := { exponent := 1, mantissa := (18719/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715766015/68714086912) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5418InnerLog : WideLogData :=
  innerPair644Data

set_option maxRecDepth 1000000 in
private theorem leaf5418LocalValidity :
    LeafFacts leaf5418Box leaf5418Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5418Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357043456) }) = true
      norm_num [leaf5418Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5418CertificateValid :
    WideCertificateValid leaf5418Box leaf5418Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi295ValidityFacts
    leaf5418LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5418CoverageChecked :
    coverageCheck (innerAD leaf5418Box) leaf5418InnerLog = true := by
  rfl'

private theorem leaf5418InnerLogValid :
    leaf5418InnerLog.Valid 8 (innerAD leaf5418Box) :=
  wideLogDataValid_of_cachedCheck endpoint387PositiveFacts
    endpoint388PositiveFacts.valid leaf5418CoverageChecked

private noncomputable def leaf5418InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629491/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5418InputLogOnePlusV_eq :
    leaf5418InputLogOnePlusV = outerEnclosure 24
      (leaf5418Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5418RoundedFacts : LeafRoundedFacts 8
    leaf5418Certificate.logOnePlusV leaf5418InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5418InputLogOnePlusV_eq }

private noncomputable def leaf5418Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi295InputQChi innerPair644Input
    leaf5418InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5418LowerChecked :
    lowerCheck 24 leaf5418Box leaf5418Inputs = true := by
  rfl'

private theorem leaf5418CoversExact : CoversExact 8
    leaf5418Box leaf5418Certificate leaf5418InnerLog leaf5418Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi295RoundedFacts
    innerPair644RoundedFacts leaf5418RoundedFacts (by rfl)

private theorem leaf5418FlatSound : Sound leaf5418Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5418CertificateValid
    leaf5418InnerLogValid leaf5418CoversExact leaf5418LowerChecked

private noncomputable def leaf5419Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5419Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908144640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1220991809/1073741824) }, upper := { exponent := 1, mantissa := (2355/2048) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816533577/9816289280) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf5419InnerLog : WideLogData :=
  innerPair646Data

set_option maxRecDepth 1000000 in
private theorem leaf5419LocalValidity :
    LeafFacts leaf5419Box leaf5419Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5419Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908144640) }) = true
      norm_num [leaf5419Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5419CertificateValid :
    WideCertificateValid leaf5419Box leaf5419Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi296ValidityFacts
    leaf5419LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5419CoverageChecked :
    coverageCheck (innerAD leaf5419Box) leaf5419InnerLog = true := by
  rfl'

private theorem leaf5419InnerLogValid :
    leaf5419InnerLog.Valid 8 (innerAD leaf5419Box) :=
  wideLogDataValid_of_cachedCheck endpoint389PositiveFacts
    endpoint390PositiveFacts.valid leaf5419CoverageChecked

private noncomputable def leaf5419InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814749/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5419InputLogOnePlusV_eq :
    leaf5419InputLogOnePlusV = outerEnclosure 24
      (leaf5419Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5419RoundedFacts : LeafRoundedFacts 8
    leaf5419Certificate.logOnePlusV leaf5419InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5419InputLogOnePlusV_eq }

private noncomputable def leaf5419Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi296InputQChi innerPair646Input
    leaf5419InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5419LowerChecked :
    lowerCheck 24 leaf5419Box leaf5419Inputs = true := by
  rfl'

private theorem leaf5419CoversExact : CoversExact 8
    leaf5419Box leaf5419Certificate leaf5419InnerLog leaf5419Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi296RoundedFacts
    innerPair646RoundedFacts leaf5419RoundedFacts (by rfl)

private theorem leaf5419FlatSound : Sound leaf5419Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5419CertificateValid
    leaf5419InnerLogValid leaf5419CoversExact leaf5419LowerChecked

private noncomputable def leaf5420Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5420Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871329/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357021184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1218763721/1073741824) }, upper := { exponent := 1, mantissa := (9403/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715743743/68714042368) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5420InnerLog : WideLogData :=
  innerPair561Data

set_option maxRecDepth 1000000 in
private theorem leaf5420LocalValidity :
    LeafFacts leaf5420Box leaf5420Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5420Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357021184) }) = true
      norm_num [leaf5420Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5420CertificateValid :
    WideCertificateValid leaf5420Box leaf5420Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi295ValidityFacts
    leaf5420LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5420CoverageChecked :
    coverageCheck (innerAD leaf5420Box) leaf5420InnerLog = true := by
  rfl'

private theorem leaf5420InnerLogValid :
    leaf5420InnerLog.Valid 8 (innerAD leaf5420Box) :=
  wideLogDataValid_of_cachedCheck endpoint292PositiveFacts
    endpoint298PositiveFacts.valid leaf5420CoverageChecked

private noncomputable def leaf5420InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453687/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5420InputLogOnePlusV_eq :
    leaf5420InputLogOnePlusV = outerEnclosure 24
      (leaf5420Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5420RoundedFacts : LeafRoundedFacts 8
    leaf5420Certificate.logOnePlusV leaf5420InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5420InputLogOnePlusV_eq }

private noncomputable def leaf5420Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi295InputQChi innerPair561Input
    leaf5420InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5420LowerChecked :
    lowerCheck 24 leaf5420Box leaf5420Inputs = true := by
  rfl'

private theorem leaf5420CoversExact : CoversExact 8
    leaf5420Box leaf5420Certificate leaf5420InnerLog leaf5420Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi295RoundedFacts
    innerPair561RoundedFacts leaf5420RoundedFacts (by rfl)

private theorem leaf5420FlatSound : Sound leaf5420Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5420CertificateValid
    leaf5420InnerLogValid leaf5420CoversExact leaf5420LowerChecked

private noncomputable def leaf5421Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5421Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356989952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1226693091/1073741824) }, upper := { exponent := 1, mantissa := (1183/1024) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715712511/68713979904) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf5421InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5421LocalValidity :
    LeafFacts leaf5421Box leaf5421Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5421Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356989952) }) = true
      norm_num [leaf5421Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5421CertificateValid :
    WideCertificateValid leaf5421Box leaf5421Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi296ValidityFacts
    leaf5421LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5421CoverageChecked :
    coverageCheck (innerAD leaf5421Box) leaf5421InnerLog = true := by
  rfl'

private theorem leaf5421InnerLogValid :
    leaf5421InnerLog.Valid 8 (innerAD leaf5421Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5421CoverageChecked

private noncomputable def leaf5421InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf5421InputLogOnePlusV_eq :
    leaf5421InputLogOnePlusV = outerEnclosure 24
      (leaf5421Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5421RoundedFacts : LeafRoundedFacts 8
    leaf5421Certificate.logOnePlusV leaf5421InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5421InputLogOnePlusV_eq }

private noncomputable def leaf5421Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi296InputQChi innerPair264Input
    leaf5421InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5421LowerChecked :
    lowerCheck 24 leaf5421Box leaf5421Inputs = true := by
  rfl'

private theorem leaf5421CoversExact : CoversExact 8
    leaf5421Box leaf5421Certificate leaf5421InnerLog leaf5421Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi296RoundedFacts
    innerPair264RoundedFacts leaf5421RoundedFacts (by rfl)

private theorem leaf5421FlatSound : Sound leaf5421Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5421CertificateValid
    leaf5421InnerLogValid leaf5421CoversExact leaf5421LowerChecked

private noncomputable def leaf5422Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5422Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742483/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714145536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2416852271/2147483648) }, upper := { exponent := 1, mantissa := (37209/32768) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431557887/137428291072) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5422InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5422LocalValidity :
    LeafFacts leaf5422Box leaf5422Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5422Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714145536) }) = true
      norm_num [leaf5422Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5422CertificateValid :
    WideCertificateValid leaf5422Box leaf5422Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi293ValidityFacts
    leaf5422LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5422CoverageChecked :
    coverageCheck (innerAD leaf5422Box) leaf5422InnerLog = true := by
  rfl'

private theorem leaf5422InnerLogValid :
    leaf5422InnerLog.Valid 8 (innerAD leaf5422Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5422CoverageChecked

private noncomputable def leaf5422InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5422InputLogOnePlusV_eq :
    leaf5422InputLogOnePlusV = outerEnclosure 24
      (leaf5422Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5422RoundedFacts : LeafRoundedFacts 8
    leaf5422Certificate.logOnePlusV leaf5422InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5422InputLogOnePlusV_eq }

private noncomputable def leaf5422Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5422InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5422LowerChecked :
    lowerCheck 24 leaf5422Box leaf5422Inputs = true := by
  rfl'

private theorem leaf5422CoversExact : CoversExact 8
    leaf5422Box leaf5422Certificate leaf5422InnerLog leaf5422Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5422RoundedFacts (by rfl)

private theorem leaf5422FlatSound : Sound leaf5422Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5422CertificateValid
    leaf5422InnerLogValid leaf5422CoversExact leaf5422LowerChecked

private noncomputable def leaf5423Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5423Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714123776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2422356957/2147483648) }, upper := { exponent := 1, mantissa := (18647/16384) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431536127/137428247552) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5423InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5423LocalValidity :
    LeafFacts leaf5423Box leaf5423Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5423Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714123776) }) = true
      norm_num [leaf5423Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5423CertificateValid :
    WideCertificateValid leaf5423Box leaf5423Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi293ValidityFacts
    leaf5423LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5423CoverageChecked :
    coverageCheck (innerAD leaf5423Box) leaf5423InnerLog = true := by
  rfl'

private theorem leaf5423InnerLogValid :
    leaf5423InnerLog.Valid 8 (innerAD leaf5423Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5423CoverageChecked

private noncomputable def leaf5423InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5423InputLogOnePlusV_eq :
    leaf5423InputLogOnePlusV = outerEnclosure 24
      (leaf5423Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5423RoundedFacts : LeafRoundedFacts 8
    leaf5423Certificate.logOnePlusV leaf5423InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5423InputLogOnePlusV_eq }

private noncomputable def leaf5423Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5423InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5423LowerChecked :
    lowerCheck 24 leaf5423Box leaf5423Inputs = true := by
  rfl'

private theorem leaf5423CoversExact : CoversExact 8
    leaf5423Box leaf5423Certificate leaf5423InnerLog leaf5423Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5423RoundedFacts (by rfl)

private theorem leaf5423FlatSound : Sound leaf5423Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5423CertificateValid
    leaf5423InnerLogValid leaf5423CoversExact leaf5423LowerChecked

private noncomputable def leaf5424Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5424Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742485/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904694272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2432842077/2147483648) }, upper := { exponent := 1, mantissa := (18727/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810498389/45809388544) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf5424InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5424LocalValidity :
    LeafFacts leaf5424Box leaf5424Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5424Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904694272) }) = true
      norm_num [leaf5424Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5424CertificateValid :
    WideCertificateValid leaf5424Box leaf5424Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi294ValidityFacts
    leaf5424LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5424CoverageChecked :
    coverageCheck (innerAD leaf5424Box) leaf5424InnerLog = true := by
  rfl'

private theorem leaf5424InnerLogValid :
    leaf5424InnerLog.Valid 8 (innerAD leaf5424Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5424CoverageChecked

private noncomputable def leaf5424InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5424InputLogOnePlusV_eq :
    leaf5424InputLogOnePlusV = outerEnclosure 24
      (leaf5424Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5424RoundedFacts : LeafRoundedFacts 8
    leaf5424Certificate.logOnePlusV leaf5424InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5424InputLogOnePlusV_eq }

private noncomputable def leaf5424Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi294InputQChi innerPair264Input
    leaf5424InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5424LowerChecked :
    lowerCheck 24 leaf5424Box leaf5424Inputs = true := by
  rfl'

private theorem leaf5424CoversExact : CoversExact 8
    leaf5424Box leaf5424Certificate leaf5424InnerLog leaf5424Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi294RoundedFacts
    innerPair264RoundedFacts leaf5424RoundedFacts (by rfl)

private theorem leaf5424FlatSound : Sound leaf5424Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5424CertificateValid
    leaf5424InnerLogValid leaf5424CoversExact leaf5424LowerChecked

private noncomputable def leaf5425Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5425Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816294400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2438412295/2147483648) }, upper := { exponent := 1, mantissa := (9385/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633067593/19632588800) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf5425InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5425LocalValidity :
    LeafFacts leaf5425Box leaf5425Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5425Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816294400) }) = true
      norm_num [leaf5425Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5425CertificateValid :
    WideCertificateValid leaf5425Box leaf5425Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi294ValidityFacts
    leaf5425LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5425CoverageChecked :
    coverageCheck (innerAD leaf5425Box) leaf5425InnerLog = true := by
  rfl'

private theorem leaf5425InnerLogValid :
    leaf5425InnerLog.Valid 8 (innerAD leaf5425Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5425CoverageChecked

private noncomputable def leaf5425InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5425InputLogOnePlusV_eq :
    leaf5425InputLogOnePlusV = outerEnclosure 24
      (leaf5425Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5425RoundedFacts : LeafRoundedFacts 8
    leaf5425Certificate.logOnePlusV leaf5425InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5425InputLogOnePlusV_eq }

private noncomputable def leaf5425Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi294InputQChi innerPair264Input
    leaf5425InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5425LowerChecked :
    lowerCheck 24 leaf5425Box leaf5425Inputs = true := by
  rfl'

private theorem leaf5425CoversExact : CoversExact 8
    leaf5425Box leaf5425Certificate leaf5425InnerLog leaf5425Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi294RoundedFacts
    innerPair264RoundedFacts leaf5425RoundedFacts (by rfl)

private theorem leaf5425FlatSound : Sound leaf5425Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5425CertificateValid
    leaf5425InnerLogValid leaf5425CoversExact leaf5425LowerChecked

private noncomputable def leaf5426Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5426Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742487/1073741824) }, vSqrt := { lower := (8191/8192), upper := (35185567/35183872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2427861643/2147483648) }, upper := { exponent := 1, mantissa := (37379/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (70369439/70367744) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5426InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5426LocalValidity :
    LeafFacts leaf5426Box leaf5426Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5426Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (35185567/35183872) }) = true
      norm_num [leaf5426Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5426CertificateValid :
    WideCertificateValid leaf5426Box leaf5426Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi293ValidityFacts
    leaf5426LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5426CoverageChecked :
    coverageCheck (innerAD leaf5426Box) leaf5426InnerLog = true := by
  rfl'

private theorem leaf5426InnerLogValid :
    leaf5426InnerLog.Valid 8 (innerAD leaf5426Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5426CoverageChecked

private noncomputable def leaf5426InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5426InputLogOnePlusV_eq :
    leaf5426InputLogOnePlusV = outerEnclosure 24
      (leaf5426Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5426RoundedFacts : LeafRoundedFacts 8
    leaf5426Certificate.logOnePlusV leaf5426InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5426InputLogOnePlusV_eq }

private noncomputable def leaf5426Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5426InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5426LowerChecked :
    lowerCheck 24 leaf5426Box leaf5426Inputs = true := by
  rfl'

private theorem leaf5426CoversExact : CoversExact 8
    leaf5426Box leaf5426Certificate leaf5426InnerLog leaf5426Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5426RoundedFacts (by rfl)

private theorem leaf5426FlatSound : Sound leaf5426Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5426CertificateValid
    leaf5426InnerLogValid leaf5426CoversExact leaf5426LowerChecked

private noncomputable def leaf5427Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5427Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714080256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2433366329/2147483648) }, upper := { exponent := 1, mantissa := (4683/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431492607/137428160512) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5427InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5427LocalValidity :
    LeafFacts leaf5427Box leaf5427Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5427Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714080256) }) = true
      norm_num [leaf5427Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5427CertificateValid :
    WideCertificateValid leaf5427Box leaf5427Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi293ValidityFacts
    leaf5427LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5427CoverageChecked :
    coverageCheck (innerAD leaf5427Box) leaf5427InnerLog = true := by
  rfl'

private theorem leaf5427InnerLogValid :
    leaf5427InnerLog.Valid 8 (innerAD leaf5427Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5427CoverageChecked

private noncomputable def leaf5427InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5427InputLogOnePlusV_eq :
    leaf5427InputLogOnePlusV = outerEnclosure 24
      (leaf5427Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5427RoundedFacts : LeafRoundedFacts 8
    leaf5427Certificate.logOnePlusV leaf5427InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5427InputLogOnePlusV_eq }

private noncomputable def leaf5427Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi293InputQChi innerPair264Input
    leaf5427InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5427LowerChecked :
    lowerCheck 24 leaf5427Box leaf5427Inputs = true := by
  rfl'

private theorem leaf5427CoversExact : CoversExact 8
    leaf5427Box leaf5427Certificate leaf5427InnerLog leaf5427Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi293RoundedFacts
    innerPair264RoundedFacts leaf5427RoundedFacts (by rfl)

private theorem leaf5427FlatSound : Sound leaf5427Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5427CertificateValid
    leaf5427InnerLogValid leaf5427CoversExact leaf5427LowerChecked

private noncomputable def leaf5428Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5428Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742489/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714038784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2443982513/2147483648) }, upper := { exponent := 1, mantissa := (18813/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431451135/137428077568) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5428InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5428LocalValidity :
    LeafFacts leaf5428Box leaf5428Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5428Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714038784) }) = true
      norm_num [leaf5428Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5428CertificateValid :
    WideCertificateValid leaf5428Box leaf5428Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi294ValidityFacts
    leaf5428LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5428CoverageChecked :
    coverageCheck (innerAD leaf5428Box) leaf5428InnerLog = true := by
  rfl'

private theorem leaf5428InnerLogValid :
    leaf5428InnerLog.Valid 8 (innerAD leaf5428Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5428CoverageChecked

private noncomputable def leaf5428InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5428InputLogOnePlusV_eq :
    leaf5428InputLogOnePlusV = outerEnclosure 24
      (leaf5428Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5428RoundedFacts : LeafRoundedFacts 8
    leaf5428Certificate.logOnePlusV leaf5428InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5428InputLogOnePlusV_eq }

private noncomputable def leaf5428Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi294InputQChi innerPair264Input
    leaf5428InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5428LowerChecked :
    lowerCheck 24 leaf5428Box leaf5428Inputs = true := by
  rfl'

private theorem leaf5428CoversExact : CoversExact 8
    leaf5428Box leaf5428Certificate leaf5428InnerLog leaf5428Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi294RoundedFacts
    innerPair264RoundedFacts leaf5428RoundedFacts (by rfl)

private theorem leaf5428FlatSound : Sound leaf5428Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5428CertificateValid
    leaf5428InnerLogValid leaf5428CoversExact leaf5428LowerChecked

private noncomputable def leaf5429Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5429Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (7635268039/7634890752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2449552731/2147483648) }, upper := { exponent := 1, mantissa := (2357/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15270158791/15269781504) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5429InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5429LocalValidity :
    LeafFacts leaf5429Box leaf5429Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5429Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7635268039/7634890752) }) = true
      norm_num [leaf5429Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5429CertificateValid :
    WideCertificateValid leaf5429Box leaf5429Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi294ValidityFacts
    leaf5429LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5429CoverageChecked :
    coverageCheck (innerAD leaf5429Box) leaf5429InnerLog = true := by
  rfl'

private theorem leaf5429InnerLogValid :
    leaf5429InnerLog.Valid 8 (innerAD leaf5429Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5429CoverageChecked

private noncomputable def leaf5429InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5429InputLogOnePlusV_eq :
    leaf5429InputLogOnePlusV = outerEnclosure 24
      (leaf5429Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5429RoundedFacts : LeafRoundedFacts 8
    leaf5429Certificate.logOnePlusV leaf5429InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5429InputLogOnePlusV_eq }

private noncomputable def leaf5429Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi294InputQChi innerPair264Input
    leaf5429InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5429LowerChecked :
    lowerCheck 24 leaf5429Box leaf5429Inputs = true := by
  rfl'

private theorem leaf5429CoversExact : CoversExact 8
    leaf5429Box leaf5429Certificate leaf5429InnerLog leaf5429Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi294RoundedFacts
    innerPair264RoundedFacts leaf5429RoundedFacts (by rfl)

private theorem leaf5429FlatSound : Sound leaf5429Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5429CertificateValid
    leaf5429InnerLogValid leaf5429CoversExact leaf5429LowerChecked

private noncomputable def leaf5430Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5430Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871331/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2020999936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1224399471/1073741824) }, upper := { exponent := 1, mantissa := (18893/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042101263/4041999872) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5430InnerLog : WideLogData :=
  innerPair649Data

set_option maxRecDepth 1000000 in
private theorem leaf5430LocalValidity :
    LeafFacts leaf5430Box leaf5430Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5430Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2020999936) }) = true
      norm_num [leaf5430Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5430CertificateValid :
    WideCertificateValid leaf5430Box leaf5430Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi295ValidityFacts
    leaf5430LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5430CoverageChecked :
    coverageCheck (innerAD leaf5430Box) leaf5430InnerLog = true := by
  rfl'

private theorem leaf5430InnerLogValid :
    leaf5430InnerLog.Valid 8 (innerAD leaf5430Box) :=
  wideLogDataValid_of_cachedCheck endpoint391PositiveFacts
    endpoint392PositiveFacts.valid leaf5430CoverageChecked

private noncomputable def leaf5430InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814751/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5430InputLogOnePlusV_eq :
    leaf5430InputLogOnePlusV = outerEnclosure 24
      (leaf5430Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5430RoundedFacts : LeafRoundedFacts 8
    leaf5430Certificate.logOnePlusV leaf5430InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5430InputLogOnePlusV_eq }

private noncomputable def leaf5430Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi295InputQChi innerPair649Input
    leaf5430InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5430LowerChecked :
    lowerCheck 24 leaf5430Box leaf5430Inputs = true := by
  rfl'

private theorem leaf5430CoversExact : CoversExact 8
    leaf5430Box leaf5430Certificate leaf5430InnerLog leaf5430Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi295RoundedFacts
    innerPair649RoundedFacts leaf5430RoundedFacts (by rfl)

private theorem leaf5430FlatSound : Sound leaf5430Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5430CertificateValid
    leaf5430InnerLogValid leaf5430CoversExact leaf5430LowerChecked

private noncomputable def leaf5431Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5431Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871333/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356967424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1232394373/1073741824) }, upper := { exponent := 1, mantissa := (2377/2048) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715689983/68713934848) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf5431InnerLog : WideLogData :=
  innerPair650Data

set_option maxRecDepth 1000000 in
private theorem leaf5431LocalValidity :
    LeafFacts leaf5431Box leaf5431Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5431Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356967424) }) = true
      norm_num [leaf5431Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5431CertificateValid :
    WideCertificateValid leaf5431Box leaf5431Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi296ValidityFacts
    leaf5431LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5431CoverageChecked :
    coverageCheck (innerAD leaf5431Box) leaf5431InnerLog = true := by
  rfl'

private theorem leaf5431InnerLogValid :
    leaf5431InnerLog.Valid 8 (innerAD leaf5431Box) :=
  wideLogDataValid_of_cachedCheck endpoint393PositiveFacts
    endpoint394PositiveFacts.valid leaf5431CoverageChecked

private noncomputable def leaf5431InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5431InputLogOnePlusV_eq :
    leaf5431InputLogOnePlusV = outerEnclosure 24
      (leaf5431Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5431RoundedFacts : LeafRoundedFacts 8
    leaf5431Certificate.logOnePlusV leaf5431InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5431InputLogOnePlusV_eq }

private noncomputable def leaf5431Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi296InputQChi innerPair650Input
    leaf5431InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5431LowerChecked :
    lowerCheck 24 leaf5431Box leaf5431Inputs = true := by
  rfl'

private theorem leaf5431CoversExact : CoversExact 8
    leaf5431Box leaf5431Certificate leaf5431InnerLog leaf5431Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi296RoundedFacts
    innerPair650RoundedFacts leaf5431RoundedFacts (by rfl)

private theorem leaf5431FlatSound : Sound leaf5431Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5431CertificateValid
    leaf5431InnerLogValid leaf5431CoversExact leaf5431LowerChecked

private noncomputable def leaf5432Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5432Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742491/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68713975552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2460103383/2147483648) }, upper := { exponent := 1, mantissa := (37873/32768) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431387903/137427951104) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf5432InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf5432LocalValidity :
    LeafFacts leaf5432Box leaf5432Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5432Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68713975552) }) = true
      norm_num [leaf5432Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5432CertificateValid :
    WideCertificateValid leaf5432Box leaf5432Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi295ValidityFacts
    leaf5432LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5432CoverageChecked :
    coverageCheck (innerAD leaf5432Box) leaf5432InnerLog = true := by
  rfl'

private theorem leaf5432InnerLogValid :
    leaf5432InnerLog.Valid 8 (innerAD leaf5432Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf5432CoverageChecked

private noncomputable def leaf5432InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907375/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5432InputLogOnePlusV_eq :
    leaf5432InputLogOnePlusV = outerEnclosure 24
      (leaf5432Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5432RoundedFacts : LeafRoundedFacts 8
    leaf5432Certificate.logOnePlusV leaf5432InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5432InputLogOnePlusV_eq }

private noncomputable def leaf5432Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi295InputQChi innerPair264Input
    leaf5432InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5432LowerChecked :
    lowerCheck 24 leaf5432Box leaf5432Inputs = true := by
  rfl'

private theorem leaf5432CoversExact : CoversExact 8
    leaf5432Box leaf5432Certificate leaf5432InnerLog leaf5432Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi295RoundedFacts
    innerPair264RoundedFacts leaf5432RoundedFacts (by rfl)

private theorem leaf5432FlatSound : Sound leaf5432Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5432CertificateValid
    leaf5432InnerLogValid leaf5432CoversExact leaf5432LowerChecked

private noncomputable def leaf5433Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5433Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742493/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816279040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2465739133/2147483648) }, upper := { exponent := 1, mantissa := (4745/4096) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633052233/19632558080) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf5433InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf5433LocalValidity :
    LeafFacts leaf5433Box leaf5433Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5433Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816279040) }) = true
      norm_num [leaf5433Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5433CertificateValid :
    WideCertificateValid leaf5433Box leaf5433Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi295ValidityFacts
    leaf5433LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5433CoverageChecked :
    coverageCheck (innerAD leaf5433Box) leaf5433InnerLog = true := by
  rfl'

private theorem leaf5433InnerLogValid :
    leaf5433InnerLog.Valid 8 (innerAD leaf5433Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf5433CoverageChecked

private noncomputable def leaf5433InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629503/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5433InputLogOnePlusV_eq :
    leaf5433InputLogOnePlusV = outerEnclosure 24
      (leaf5433Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5433RoundedFacts : LeafRoundedFacts 8
    leaf5433Certificate.logOnePlusV leaf5433InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5433InputLogOnePlusV_eq }

private noncomputable def leaf5433Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi295InputQChi innerPair265Input
    leaf5433InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5433LowerChecked :
    lowerCheck 24 leaf5433Box leaf5433Inputs = true := by
  rfl'

private theorem leaf5433CoversExact : CoversExact 8
    leaf5433Box leaf5433Certificate leaf5433InnerLog leaf5433Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi295RoundedFacts
    innerPair265RoundedFacts leaf5433RoundedFacts (by rfl)

private theorem leaf5433FlatSound : Sound leaf5433Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5433CertificateValid
    leaf5433InnerLogValid leaf5433CoversExact leaf5433LowerChecked

private noncomputable def leaf5434Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5434Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871335/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34356944896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1238095655/1073741824) }, upper := { exponent := 1, mantissa := (597/512) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715667455/68713889792) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf5434InnerLog : WideLogData :=
  innerPair653Data

set_option maxRecDepth 1000000 in
private theorem leaf5434LocalValidity :
    LeafFacts leaf5434Box leaf5434Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5434Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34356944896) }) = true
      norm_num [leaf5434Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5434CertificateValid :
    WideCertificateValid leaf5434Box leaf5434Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi296ValidityFacts
    leaf5434LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5434CoverageChecked :
    coverageCheck (innerAD leaf5434Box) leaf5434InnerLog = true := by
  rfl'

private theorem leaf5434InnerLogValid :
    leaf5434InnerLog.Valid 8 (innerAD leaf5434Box) :=
  wideLogDataValid_of_cachedCheck endpoint395PositiveFacts
    endpoint396PositiveFacts.valid leaf5434CoverageChecked

private noncomputable def leaf5434InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629515/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5434InputLogOnePlusV_eq :
    leaf5434InputLogOnePlusV = outerEnclosure 24
      (leaf5434Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5434RoundedFacts : LeafRoundedFacts 8
    leaf5434Certificate.logOnePlusV leaf5434InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5434InputLogOnePlusV_eq }

private noncomputable def leaf5434Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi296InputQChi innerPair653Input
    leaf5434InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5434LowerChecked :
    lowerCheck 24 leaf5434Box leaf5434Inputs = true := by
  rfl'

private theorem leaf5434CoversExact : CoversExact 8
    leaf5434Box leaf5434Certificate leaf5434InnerLog leaf5434Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi296RoundedFacts
    innerPair653RoundedFacts leaf5434RoundedFacts (by rfl)

private theorem leaf5434FlatSound : Sound leaf5434Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5434CertificateValid
    leaf5434InnerLogValid leaf5434CoversExact leaf5434LowerChecked

private noncomputable def component109Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node0_sound : Sound component109Node0Box :=
  sound_of_literal_split component109Node0Box leaf5381Box leaf5382Box
    .k (241/64) (by rfl) (by rfl)
    leaf5381FlatSound leaf5382FlatSound

private noncomputable def component109Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node1_sound : Sound component109Node1Box :=
  sound_of_literal_split component109Node1Box leaf5383Box leaf5384Box
    .k (241/64) (by rfl) (by rfl)
    leaf5383FlatSound leaf5384FlatSound

private noncomputable def component109Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node2_sound : Sound component109Node2Box :=
  sound_of_literal_split component109Node2Box component109Node0Box component109Node1Box
    .chi (81/256) (by rfl) (by rfl)
    component109Node0_sound component109Node1_sound

private noncomputable def component109Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node3_sound : Sound component109Node3Box :=
  sound_of_literal_split component109Node3Box leaf5385Box leaf5386Box
    .k (243/64) (by rfl) (by rfl)
    leaf5385FlatSound leaf5386FlatSound

private noncomputable def component109Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node4_sound : Sound component109Node4Box :=
  sound_of_literal_split component109Node4Box leaf5387Box leaf5388Box
    .k (243/64) (by rfl) (by rfl)
    leaf5387FlatSound leaf5388FlatSound

private noncomputable def component109Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node5_sound : Sound component109Node5Box :=
  sound_of_literal_split component109Node5Box component109Node3Box component109Node4Box
    .chi (81/256) (by rfl) (by rfl)
    component109Node3_sound component109Node4_sound

private noncomputable def component109Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node6_sound : Sound component109Node6Box :=
  sound_of_literal_split component109Node6Box component109Node2Box component109Node5Box
    .k (121/32) (by rfl) (by rfl)
    component109Node2_sound component109Node5_sound

private noncomputable def component109Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node7_sound : Sound component109Node7Box :=
  sound_of_literal_split component109Node7Box leaf5389Box leaf5390Box
    .k (241/64) (by rfl) (by rfl)
    leaf5389FlatSound leaf5390FlatSound

private noncomputable def component109Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node8_sound : Sound component109Node8Box :=
  sound_of_literal_split component109Node8Box leaf5391Box leaf5392Box
    .k (241/64) (by rfl) (by rfl)
    leaf5391FlatSound leaf5392FlatSound

private noncomputable def component109Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node9_sound : Sound component109Node9Box :=
  sound_of_literal_split component109Node9Box component109Node7Box component109Node8Box
    .chi (83/256) (by rfl) (by rfl)
    component109Node7_sound component109Node8_sound

private noncomputable def component109Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node10_sound : Sound component109Node10Box :=
  sound_of_literal_split component109Node10Box leaf5393Box leaf5394Box
    .k (243/64) (by rfl) (by rfl)
    leaf5393FlatSound leaf5394FlatSound

private noncomputable def component109Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node11_sound : Sound component109Node11Box :=
  sound_of_literal_split component109Node11Box leaf5395Box leaf5396Box
    .k (243/64) (by rfl) (by rfl)
    leaf5395FlatSound leaf5396FlatSound

private noncomputable def component109Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node12_sound : Sound component109Node12Box :=
  sound_of_literal_split component109Node12Box component109Node10Box component109Node11Box
    .chi (83/256) (by rfl) (by rfl)
    component109Node10_sound component109Node11_sound

private noncomputable def component109Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node13_sound : Sound component109Node13Box :=
  sound_of_literal_split component109Node13Box component109Node9Box component109Node12Box
    .k (121/32) (by rfl) (by rfl)
    component109Node9_sound component109Node12_sound

private noncomputable def component109Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node14_sound : Sound component109Node14Box :=
  sound_of_literal_split component109Node14Box component109Node6Box component109Node13Box
    .chi (41/128) (by rfl) (by rfl)
    component109Node6_sound component109Node13_sound

private noncomputable def component109Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node15_sound : Sound component109Node15Box :=
  sound_of_literal_split component109Node15Box leaf5397Box leaf5398Box
    .k (245/64) (by rfl) (by rfl)
    leaf5397FlatSound leaf5398FlatSound

private noncomputable def component109Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node16_sound : Sound component109Node16Box :=
  sound_of_literal_split component109Node16Box leaf5399Box leaf5400Box
    .k (245/64) (by rfl) (by rfl)
    leaf5399FlatSound leaf5400FlatSound

private noncomputable def component109Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node17_sound : Sound component109Node17Box :=
  sound_of_literal_split component109Node17Box component109Node15Box component109Node16Box
    .chi (81/256) (by rfl) (by rfl)
    component109Node15_sound component109Node16_sound

private noncomputable def component109Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node18_sound : Sound component109Node18Box :=
  sound_of_literal_split component109Node18Box leaf5401Box leaf5402Box
    .k (247/64) (by rfl) (by rfl)
    leaf5401FlatSound leaf5402FlatSound

private noncomputable def component109Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node19_sound : Sound component109Node19Box :=
  sound_of_literal_split component109Node19Box leaf5403Box leaf5404Box
    .k (247/64) (by rfl) (by rfl)
    leaf5403FlatSound leaf5404FlatSound

private noncomputable def component109Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node20_sound : Sound component109Node20Box :=
  sound_of_literal_split component109Node20Box component109Node18Box component109Node19Box
    .chi (81/256) (by rfl) (by rfl)
    component109Node18_sound component109Node19_sound

private noncomputable def component109Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node21_sound : Sound component109Node21Box :=
  sound_of_literal_split component109Node21Box component109Node17Box component109Node20Box
    .k (123/32) (by rfl) (by rfl)
    component109Node17_sound component109Node20_sound

private noncomputable def component109Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node22_sound : Sound component109Node22Box :=
  sound_of_literal_split component109Node22Box leaf5405Box leaf5406Box
    .k (245/64) (by rfl) (by rfl)
    leaf5405FlatSound leaf5406FlatSound

private noncomputable def component109Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node23_sound : Sound component109Node23Box :=
  sound_of_literal_split component109Node23Box leaf5407Box leaf5408Box
    .k (245/64) (by rfl) (by rfl)
    leaf5407FlatSound leaf5408FlatSound

private noncomputable def component109Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node24_sound : Sound component109Node24Box :=
  sound_of_literal_split component109Node24Box component109Node22Box component109Node23Box
    .chi (83/256) (by rfl) (by rfl)
    component109Node22_sound component109Node23_sound

private noncomputable def component109Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node25_sound : Sound component109Node25Box :=
  sound_of_literal_split component109Node25Box leaf5409Box leaf5410Box
    .k (247/64) (by rfl) (by rfl)
    leaf5409FlatSound leaf5410FlatSound

private noncomputable def component109Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (83/256), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node26_sound : Sound component109Node26Box :=
  sound_of_literal_split component109Node26Box leaf5411Box leaf5412Box
    .k (247/64) (by rfl) (by rfl)
    leaf5411FlatSound leaf5412FlatSound

private noncomputable def component109Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node27_sound : Sound component109Node27Box :=
  sound_of_literal_split component109Node27Box component109Node25Box component109Node26Box
    .chi (83/256) (by rfl) (by rfl)
    component109Node25_sound component109Node26_sound

private noncomputable def component109Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node28_sound : Sound component109Node28Box :=
  sound_of_literal_split component109Node28Box component109Node24Box component109Node27Box
    .k (123/32) (by rfl) (by rfl)
    component109Node24_sound component109Node27_sound

private noncomputable def component109Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node29_sound : Sound component109Node29Box :=
  sound_of_literal_split component109Node29Box component109Node21Box component109Node28Box
    .chi (41/128) (by rfl) (by rfl)
    component109Node21_sound component109Node28_sound

private noncomputable def component109Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component109Node30_sound : Sound component109Node30Box :=
  sound_of_literal_split component109Node30Box component109Node14Box component109Node29Box
    .k (61/16) (by rfl) (by rfl)
    component109Node14_sound component109Node29_sound

private noncomputable def component109Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node31_sound : Sound component109Node31Box :=
  sound_of_literal_split component109Node31Box leaf5413Box leaf5414Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5413FlatSound leaf5414FlatSound

private noncomputable def component109Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (21/64), chiHi := (85/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node32_sound : Sound component109Node32Box :=
  sound_of_literal_split component109Node32Box leaf5415Box leaf5416Box
    .k (243/64) (by rfl) (by rfl)
    leaf5415FlatSound leaf5416FlatSound

private noncomputable def component109Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node33_sound : Sound component109Node33Box :=
  sound_of_literal_split component109Node33Box component109Node32Box leaf5417Box
    .chi (85/256) (by rfl) (by rfl)
    component109Node32_sound leaf5417FlatSound

private noncomputable def component109Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node34_sound : Sound component109Node34Box :=
  sound_of_literal_split component109Node34Box component109Node31Box component109Node33Box
    .k (121/32) (by rfl) (by rfl)
    component109Node31_sound component109Node33_sound

private noncomputable def component109Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node35_sound : Sound component109Node35Box :=
  sound_of_literal_split component109Node35Box leaf5418Box leaf5419Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5418FlatSound leaf5419FlatSound

private noncomputable def component109Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node36_sound : Sound component109Node36Box :=
  sound_of_literal_split component109Node36Box leaf5420Box leaf5421Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5420FlatSound leaf5421FlatSound

private noncomputable def component109Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node37_sound : Sound component109Node37Box :=
  sound_of_literal_split component109Node37Box component109Node35Box component109Node36Box
    .k (121/32) (by rfl) (by rfl)
    component109Node35_sound component109Node36_sound

private noncomputable def component109Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node38_sound : Sound component109Node38Box :=
  sound_of_literal_split component109Node38Box component109Node34Box component109Node37Box
    .chi (43/128) (by rfl) (by rfl)
    component109Node34_sound component109Node37_sound

private noncomputable def component109Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (21/64), chiHi := (85/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node39_sound : Sound component109Node39Box :=
  sound_of_literal_split component109Node39Box leaf5422Box leaf5423Box
    .k (245/64) (by rfl) (by rfl)
    leaf5422FlatSound leaf5423FlatSound

private noncomputable def component109Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (85/256), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node40_sound : Sound component109Node40Box :=
  sound_of_literal_split component109Node40Box leaf5424Box leaf5425Box
    .k (245/64) (by rfl) (by rfl)
    leaf5424FlatSound leaf5425FlatSound

private noncomputable def component109Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node41_sound : Sound component109Node41Box :=
  sound_of_literal_split component109Node41Box component109Node39Box component109Node40Box
    .chi (85/256) (by rfl) (by rfl)
    component109Node39_sound component109Node40_sound

private noncomputable def component109Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (21/64), chiHi := (85/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node42_sound : Sound component109Node42Box :=
  sound_of_literal_split component109Node42Box leaf5426Box leaf5427Box
    .k (247/64) (by rfl) (by rfl)
    leaf5426FlatSound leaf5427FlatSound

private noncomputable def component109Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (85/256), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node43_sound : Sound component109Node43Box :=
  sound_of_literal_split component109Node43Box leaf5428Box leaf5429Box
    .k (247/64) (by rfl) (by rfl)
    leaf5428FlatSound leaf5429FlatSound

private noncomputable def component109Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node44_sound : Sound component109Node44Box :=
  sound_of_literal_split component109Node44Box component109Node42Box component109Node43Box
    .chi (85/256) (by rfl) (by rfl)
    component109Node42_sound component109Node43_sound

private noncomputable def component109Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component109Node45_sound : Sound component109Node45Box :=
  sound_of_literal_split component109Node45Box component109Node41Box component109Node44Box
    .k (123/32) (by rfl) (by rfl)
    component109Node41_sound component109Node44_sound

private noncomputable def component109Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node46_sound : Sound component109Node46Box :=
  sound_of_literal_split component109Node46Box leaf5430Box leaf5431Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5430FlatSound leaf5431FlatSound

private noncomputable def component109Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (43/128), chiHi := (87/256) }

set_option maxRecDepth 1000000 in
private theorem component109Node47_sound : Sound component109Node47Box :=
  sound_of_literal_split component109Node47Box leaf5432Box leaf5433Box
    .k (247/64) (by rfl) (by rfl)
    leaf5432FlatSound leaf5433FlatSound

private noncomputable def component109Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node48_sound : Sound component109Node48Box :=
  sound_of_literal_split component109Node48Box component109Node47Box leaf5434Box
    .chi (87/256) (by rfl) (by rfl)
    component109Node47_sound leaf5434FlatSound

private noncomputable def component109Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node49_sound : Sound component109Node49Box :=
  sound_of_literal_split component109Node49Box component109Node46Box component109Node48Box
    .k (123/32) (by rfl) (by rfl)
    component109Node46_sound component109Node48_sound

private noncomputable def component109Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node50_sound : Sound component109Node50Box :=
  sound_of_literal_split component109Node50Box component109Node45Box component109Node49Box
    .chi (43/128) (by rfl) (by rfl)
    component109Node45_sound component109Node49_sound

private noncomputable def component109Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component109Node51_sound : Sound component109Node51Box :=
  sound_of_literal_split component109Node51Box component109Node38Box component109Node50Box
    .k (61/16) (by rfl) (by rfl)
    component109Node38_sound component109Node50_sound

noncomputable def component109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
theorem component109_sound : Sound component109Box :=
  sound_of_literal_split component109Box component109Node30Box component109Node51Box
    .chi (21/64) (by rfl) (by rfl)
    component109Node30_sound component109Node51_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
