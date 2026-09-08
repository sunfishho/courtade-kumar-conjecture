import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
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

private noncomputable def leaf5247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871299/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357395200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1124004479/1073741824) }, upper := { exponent := 1, mantissa := (17345/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716117759/68714790400) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5247InnerLog : WideLogData :=
  innerPair242Data

set_option maxRecDepth 1000000 in
private theorem leaf5247LocalValidity :
    LeafFacts leaf5247Box leaf5247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357395200) }) = true
      norm_num [leaf5247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5247CertificateValid :
    WideCertificateValid leaf5247Box leaf5247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi289ValidityFacts
    leaf5247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5247CoverageChecked :
    coverageCheck (innerAD leaf5247Box) leaf5247InnerLog = true := by
  rfl'

private theorem leaf5247InnerLogValid :
    leaf5247InnerLog.Valid 8 (innerAD leaf5247Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint73PositiveFacts.valid leaf5247CoverageChecked

private noncomputable def leaf5247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5247InputLogOnePlusV_eq :
    leaf5247InputLogOnePlusV = outerEnclosure 24
      (leaf5247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5247RoundedFacts : LeafRoundedFacts 8
    leaf5247Certificate.logOnePlusV leaf5247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5247InputLogOnePlusV_eq }

private noncomputable def leaf5247Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi289InputQChi innerPair242Input
    leaf5247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5247LowerChecked :
    lowerCheck 24 leaf5247Box leaf5247Inputs = true := by
  rfl'

private theorem leaf5247CoversExact : CoversExact 8
    leaf5247Box leaf5247Certificate leaf5247InnerLog leaf5247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi289RoundedFacts
    innerPair242RoundedFacts leaf5247RoundedFacts (by rfl)

private theorem leaf5247FlatSound : Sound leaf5247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5247CertificateValid
    leaf5247InnerLogValid leaf5247CoversExact leaf5247LowerChecked

private noncomputable def leaf5248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357366272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1131344061/1073741824) }, upper := { exponent := 1, mantissa := (8729/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716088831/68714732544) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5248InnerLog : WideLogData :=
  innerPair551Data

set_option maxRecDepth 1000000 in
private theorem leaf5248LocalValidity :
    LeafFacts leaf5248Box leaf5248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357366272) }) = true
      norm_num [leaf5248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5248CertificateValid :
    WideCertificateValid leaf5248Box leaf5248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi290ValidityFacts
    leaf5248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5248CoverageChecked :
    coverageCheck (innerAD leaf5248Box) leaf5248InnerLog = true := by
  rfl'

private theorem leaf5248InnerLogValid :
    leaf5248InnerLog.Valid 8 (innerAD leaf5248Box) :=
  wideLogDataValid_of_cachedCheck endpoint284PositiveFacts
    endpoint289PositiveFacts.valid leaf5248CoverageChecked

private noncomputable def leaf5248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5248InputLogOnePlusV_eq :
    leaf5248InputLogOnePlusV = outerEnclosure 24
      (leaf5248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5248RoundedFacts : LeafRoundedFacts 8
    leaf5248Certificate.logOnePlusV leaf5248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5248InputLogOnePlusV_eq }

private noncomputable def leaf5248Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi290InputQChi innerPair551Input
    leaf5248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5248LowerChecked :
    lowerCheck 24 leaf5248Box leaf5248Inputs = true := by
  rfl'

private theorem leaf5248CoversExact : CoversExact 8
    leaf5248Box leaf5248Certificate leaf5248InnerLog leaf5248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi290RoundedFacts
    innerPair551RoundedFacts leaf5248RoundedFacts (by rfl)

private theorem leaf5248FlatSound : Sound leaf5248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5248CertificateValid
    leaf5248InnerLogValid leaf5248CoversExact leaf5248LowerChecked

private noncomputable def leaf5249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871301/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908196352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1129247037/1073741824) }, upper := { exponent := 1, mantissa := (8713/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816585289/9816392704) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5249InnerLog : WideLogData :=
  innerPair628Data

set_option maxRecDepth 1000000 in
private theorem leaf5249LocalValidity :
    LeafFacts leaf5249Box leaf5249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908196352) }) = true
      norm_num [leaf5249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5249CertificateValid :
    WideCertificateValid leaf5249Box leaf5249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi289ValidityFacts
    leaf5249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5249CoverageChecked :
    coverageCheck (innerAD leaf5249Box) leaf5249InnerLog = true := by
  rfl'

private theorem leaf5249InnerLogValid :
    leaf5249InnerLog.Valid 8 (innerAD leaf5249Box) :=
  wideLogDataValid_of_cachedCheck endpoint357PositiveFacts
    endpoint363PositiveFacts.valid leaf5249CoverageChecked

private noncomputable def leaf5249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5249InputLogOnePlusV_eq :
    leaf5249InputLogOnePlusV = outerEnclosure 24
      (leaf5249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5249RoundedFacts : LeafRoundedFacts 8
    leaf5249Certificate.logOnePlusV leaf5249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5249InputLogOnePlusV_eq }

private noncomputable def leaf5249Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi289InputQChi innerPair628Input
    leaf5249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5249LowerChecked :
    lowerCheck 24 leaf5249Box leaf5249Inputs = true := by
  rfl'

private theorem leaf5249CoversExact : CoversExact 8
    leaf5249Box leaf5249Certificate leaf5249InnerLog leaf5249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi289RoundedFacts
    innerPair628RoundedFacts leaf5249RoundedFacts (by rfl)

private theorem leaf5249FlatSound : Sound leaf5249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5249CertificateValid
    leaf5249InnerLogValid leaf5249CoversExact leaf5249LowerChecked

private noncomputable def leaf5250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357345280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1136652151/1073741824) }, upper := { exponent := 1, mantissa := (4385/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716067839/68714690560) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5250InnerLog : WideLogData :=
  innerPair629Data

set_option maxRecDepth 1000000 in
private theorem leaf5250LocalValidity :
    LeafFacts leaf5250Box leaf5250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357345280) }) = true
      norm_num [leaf5250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5250CertificateValid :
    WideCertificateValid leaf5250Box leaf5250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi290ValidityFacts
    leaf5250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5250CoverageChecked :
    coverageCheck (innerAD leaf5250Box) leaf5250InnerLog = true := by
  rfl'

private theorem leaf5250InnerLogValid :
    leaf5250InnerLog.Valid 8 (innerAD leaf5250Box) :=
  wideLogDataValid_of_cachedCheck endpoint358PositiveFacts
    endpoint336PositiveFacts.valid leaf5250CoverageChecked

private noncomputable def leaf5250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5250InputLogOnePlusV_eq :
    leaf5250InputLogOnePlusV = outerEnclosure 24
      (leaf5250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5250RoundedFacts : LeafRoundedFacts 8
    leaf5250Certificate.logOnePlusV leaf5250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5250InputLogOnePlusV_eq }

private noncomputable def leaf5250Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi290InputQChi innerPair629Input
    leaf5250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5250LowerChecked :
    lowerCheck 24 leaf5250Box leaf5250Inputs = true := by
  rfl'

private theorem leaf5250CoversExact : CoversExact 8
    leaf5250Box leaf5250Certificate leaf5250InnerLog leaf5250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi290RoundedFacts
    innerPair629RoundedFacts leaf5250RoundedFacts (by rfl)

private theorem leaf5250FlatSound : Sound leaf5250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5250CertificateValid
    leaf5250InnerLogValid leaf5250CoversExact leaf5250LowerChecked

private noncomputable def leaf5251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357337344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1138683643/1073741824) }, upper := { exponent := 1, mantissa := (17571/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716059903/68714674688) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5251InnerLog : WideLogData :=
  innerPair335Data

set_option maxRecDepth 1000000 in
private theorem leaf5251LocalValidity :
    LeafFacts leaf5251Box leaf5251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357337344) }) = true
      norm_num [leaf5251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5251CertificateValid :
    WideCertificateValid leaf5251Box leaf5251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi291ValidityFacts
    leaf5251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5251CoverageChecked :
    coverageCheck (innerAD leaf5251Box) leaf5251InnerLog = true := by
  rfl'

private theorem leaf5251InnerLogValid :
    leaf5251InnerLog.Valid 8 (innerAD leaf5251Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint88PositiveFacts.valid leaf5251CoverageChecked

private noncomputable def leaf5251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5251InputLogOnePlusV_eq :
    leaf5251InputLogOnePlusV = outerEnclosure 24
      (leaf5251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5251RoundedFacts : LeafRoundedFacts 8
    leaf5251Certificate.logOnePlusV leaf5251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5251InputLogOnePlusV_eq }

private noncomputable def leaf5251Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi291InputQChi innerPair335Input
    leaf5251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5251LowerChecked :
    lowerCheck 24 leaf5251Box leaf5251Inputs = true := by
  rfl'

private theorem leaf5251CoversExact : CoversExact 8
    leaf5251Box leaf5251Certificate leaf5251InnerLog leaf5251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi291RoundedFacts
    innerPair335RoundedFacts leaf5251RoundedFacts (by rfl)

private theorem leaf5251FlatSound : Sound leaf5251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5251CertificateValid
    leaf5251InnerLogValid leaf5251CoversExact leaf5251LowerChecked

private noncomputable def leaf5252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357308416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1146023225/1073741824) }, upper := { exponent := 1, mantissa := (4421/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716030975/68714616832) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5252InnerLog : WideLogData :=
  innerPair255Data

set_option maxRecDepth 1000000 in
private theorem leaf5252LocalValidity :
    LeafFacts leaf5252Box leaf5252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357308416) }) = true
      norm_num [leaf5252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5252CertificateValid :
    WideCertificateValid leaf5252Box leaf5252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi292ValidityFacts
    leaf5252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5252CoverageChecked :
    coverageCheck (innerAD leaf5252Box) leaf5252InnerLog = true := by
  rfl'

private theorem leaf5252InnerLogValid :
    leaf5252InnerLog.Valid 8 (innerAD leaf5252Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint337PositiveFacts.valid leaf5252CoverageChecked

private noncomputable def leaf5252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5252InputLogOnePlusV_eq :
    leaf5252InputLogOnePlusV = outerEnclosure 24
      (leaf5252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5252RoundedFacts : LeafRoundedFacts 8
    leaf5252Certificate.logOnePlusV leaf5252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5252InputLogOnePlusV_eq }

private noncomputable def leaf5252Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi292InputQChi innerPair255Input
    leaf5252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5252LowerChecked :
    lowerCheck 24 leaf5252Box leaf5252Inputs = true := by
  rfl'

private theorem leaf5252CoversExact : CoversExact 8
    leaf5252Box leaf5252Certificate leaf5252InnerLog leaf5252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi292RoundedFacts
    innerPair255RoundedFacts leaf5252RoundedFacts (by rfl)

private theorem leaf5252FlatSound : Sound leaf5252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5252CertificateValid
    leaf5252InnerLogValid leaf5252CoversExact leaf5252LowerChecked

private noncomputable def leaf5253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357316096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1144057265/1073741824) }, upper := { exponent := 1, mantissa := (8827/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716038655/68714632192) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5253InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf5253LocalValidity :
    LeafFacts leaf5253Box leaf5253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357316096) }) = true
      norm_num [leaf5253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5253CertificateValid :
    WideCertificateValid leaf5253Box leaf5253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi291ValidityFacts
    leaf5253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5253CoverageChecked :
    coverageCheck (innerAD leaf5253Box) leaf5253InnerLog = true := by
  rfl'

private theorem leaf5253InnerLogValid :
    leaf5253InnerLog.Valid 8 (innerAD leaf5253Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf5253CoverageChecked

private noncomputable def leaf5253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5253InputLogOnePlusV_eq :
    leaf5253InputLogOnePlusV = outerEnclosure 24
      (leaf5253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5253RoundedFacts : LeafRoundedFacts 8
    leaf5253Certificate.logOnePlusV leaf5253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5253InputLogOnePlusV_eq }

private noncomputable def leaf5253Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi291InputQChi innerPair253Input
    leaf5253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5253LowerChecked :
    lowerCheck 24 leaf5253Box leaf5253Inputs = true := by
  rfl'

private theorem leaf5253CoversExact : CoversExact 8
    leaf5253Box leaf5253Certificate leaf5253InnerLog leaf5253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi291RoundedFacts
    innerPair253RoundedFacts leaf5253RoundedFacts (by rfl)

private theorem leaf5253FlatSound : Sound leaf5253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5253CertificateValid
    leaf5253InnerLogValid leaf5253CoversExact leaf5253LowerChecked

private noncomputable def leaf5254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357286912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1151462379/1073741824) }, upper := { exponent := 1, mantissa := (2221/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716009471/68714573824) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5254InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5254LocalValidity :
    LeafFacts leaf5254Box leaf5254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357286912) }) = true
      norm_num [leaf5254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5254CertificateValid :
    WideCertificateValid leaf5254Box leaf5254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi292ValidityFacts
    leaf5254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5254CoverageChecked :
    coverageCheck (innerAD leaf5254Box) leaf5254InnerLog = true := by
  rfl'

private theorem leaf5254InnerLogValid :
    leaf5254InnerLog.Valid 8 (innerAD leaf5254Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5254CoverageChecked

private noncomputable def leaf5254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5254InputLogOnePlusV_eq :
    leaf5254InputLogOnePlusV = outerEnclosure 24
      (leaf5254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5254RoundedFacts : LeafRoundedFacts 8
    leaf5254Certificate.logOnePlusV leaf5254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5254InputLogOnePlusV_eq }

private noncomputable def leaf5254Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi292InputQChi innerPair249Input
    leaf5254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5254LowerChecked :
    lowerCheck 24 leaf5254Box leaf5254Inputs = true := by
  rfl'

private theorem leaf5254CoversExact : CoversExact 8
    leaf5254Box leaf5254Certificate leaf5254InnerLog leaf5254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi292RoundedFacts
    innerPair249RoundedFacts leaf5254RoundedFacts (by rfl)

private theorem leaf5254FlatSound : Sound leaf5254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5254CertificateValid
    leaf5254InnerLogValid leaf5254CoversExact leaf5254LowerChecked

private noncomputable def leaf5255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871303/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357353728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1134489595/1073741824) }, upper := { exponent := 1, mantissa := (17507/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716076287/68714707456) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5255InnerLog : WideLogData :=
  innerPair336Data

set_option maxRecDepth 1000000 in
private theorem leaf5255LocalValidity :
    LeafFacts leaf5255Box leaf5255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357353728) }) = true
      norm_num [leaf5255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5255CertificateValid :
    WideCertificateValid leaf5255Box leaf5255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi289ValidityFacts
    leaf5255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5255CoverageChecked :
    coverageCheck (innerAD leaf5255Box) leaf5255InnerLog = true := by
  rfl'

private theorem leaf5255InnerLogValid :
    leaf5255InnerLog.Valid 8 (innerAD leaf5255Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint289PositiveFacts.valid leaf5255CoverageChecked

private noncomputable def leaf5255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5255InputLogOnePlusV_eq :
    leaf5255InputLogOnePlusV = outerEnclosure 24
      (leaf5255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5255RoundedFacts : LeafRoundedFacts 8
    leaf5255Certificate.logOnePlusV leaf5255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5255InputLogOnePlusV_eq }

private noncomputable def leaf5255Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi289InputQChi innerPair336Input
    leaf5255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5255LowerChecked :
    lowerCheck 24 leaf5255Box leaf5255Inputs = true := by
  rfl'

private theorem leaf5255CoversExact : CoversExact 8
    leaf5255Box leaf5255Certificate leaf5255InnerLog leaf5255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi289RoundedFacts
    innerPair336RoundedFacts leaf5255RoundedFacts (by rfl)

private theorem leaf5255FlatSound : Sound leaf5255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5255CertificateValid
    leaf5255InnerLogValid leaf5255CoversExact leaf5255LowerChecked

private noncomputable def leaf5256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908189184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1141960241/1073741824) }, upper := { exponent := 1, mantissa := (8811/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816578121/9816378368) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5256InnerLog : WideLogData :=
  innerPair253Data

set_option maxRecDepth 1000000 in
private theorem leaf5256LocalValidity :
    LeafFacts leaf5256Box leaf5256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908189184) }) = true
      norm_num [leaf5256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5256CertificateValid :
    WideCertificateValid leaf5256Box leaf5256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi290ValidityFacts
    leaf5256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5256CoverageChecked :
    coverageCheck (innerAD leaf5256Box) leaf5256InnerLog = true := by
  rfl'

private theorem leaf5256InnerLogValid :
    leaf5256InnerLog.Valid 8 (innerAD leaf5256Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint88PositiveFacts.valid leaf5256CoverageChecked

private noncomputable def leaf5256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5256InputLogOnePlusV_eq :
    leaf5256InputLogOnePlusV = outerEnclosure 24
      (leaf5256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5256RoundedFacts : LeafRoundedFacts 8
    leaf5256Certificate.logOnePlusV leaf5256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5256InputLogOnePlusV_eq }

private noncomputable def leaf5256Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi290InputQChi innerPair253Input
    leaf5256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5256LowerChecked :
    lowerCheck 24 leaf5256Box leaf5256Inputs = true := by
  rfl'

private theorem leaf5256CoversExact : CoversExact 8
    leaf5256Box leaf5256Certificate leaf5256InnerLog leaf5256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi290RoundedFacts
    innerPair253RoundedFacts leaf5256RoundedFacts (by rfl)

private theorem leaf5256FlatSound : Sound leaf5256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5256CertificateValid
    leaf5256InnerLogValid leaf5256CoversExact leaf5256LowerChecked

private noncomputable def leaf5257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871305/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357332992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1139732153/1073741824) }, upper := { exponent := 1, mantissa := (4397/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716055551/68714665984) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5257InnerLog : WideLogData :=
  innerPair631Data

set_option maxRecDepth 1000000 in
private theorem leaf5257LocalValidity :
    LeafFacts leaf5257Box leaf5257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357332992) }) = true
      norm_num [leaf5257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5257CertificateValid :
    WideCertificateValid leaf5257Box leaf5257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi289ValidityFacts
    leaf5257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5257CoverageChecked :
    coverageCheck (innerAD leaf5257Box) leaf5257InnerLog = true := by
  rfl'

private theorem leaf5257InnerLogValid :
    leaf5257InnerLog.Valid 8 (innerAD leaf5257Box) :=
  wideLogDataValid_of_cachedCheck endpoint364PositiveFacts
    endpoint365PositiveFacts.valid leaf5257CoverageChecked

private noncomputable def leaf5257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5257InputLogOnePlusV_eq :
    leaf5257InputLogOnePlusV = outerEnclosure 24
      (leaf5257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5257RoundedFacts : LeafRoundedFacts 8
    leaf5257Certificate.logOnePlusV leaf5257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5257InputLogOnePlusV_eq }

private noncomputable def leaf5257Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi289InputQChi innerPair631Input
    leaf5257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5257LowerChecked :
    lowerCheck 24 leaf5257Box leaf5257Inputs = true := by
  rfl'

private theorem leaf5257CoversExact : CoversExact 8
    leaf5257Box leaf5257Certificate leaf5257InnerLog leaf5257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi289RoundedFacts
    innerPair631RoundedFacts leaf5257RoundedFacts (by rfl)

private theorem leaf5257FlatSound : Sound leaf5257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5257CertificateValid
    leaf5257InnerLogValid leaf5257CoversExact leaf5257LowerChecked

private noncomputable def leaf5258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357303296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1147268331/1073741824) }, upper := { exponent := 1, mantissa := (2213/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716025855/68714606592) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5258InnerLog : WideLogData :=
  innerPair633Data

set_option maxRecDepth 1000000 in
private theorem leaf5258LocalValidity :
    LeafFacts leaf5258Box leaf5258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357303296) }) = true
      norm_num [leaf5258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5258CertificateValid :
    WideCertificateValid leaf5258Box leaf5258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi290ValidityFacts
    leaf5258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5258CoverageChecked :
    coverageCheck (innerAD leaf5258Box) leaf5258InnerLog = true := by
  rfl'

private theorem leaf5258InnerLogValid :
    leaf5258InnerLog.Valid 8 (innerAD leaf5258Box) :=
  wideLogDataValid_of_cachedCheck endpoint366PositiveFacts
    endpoint345PositiveFacts.valid leaf5258CoverageChecked

private noncomputable def leaf5258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5258InputLogOnePlusV_eq :
    leaf5258InputLogOnePlusV = outerEnclosure 24
      (leaf5258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5258RoundedFacts : LeafRoundedFacts 8
    leaf5258Certificate.logOnePlusV leaf5258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5258InputLogOnePlusV_eq }

private noncomputable def leaf5258Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi290InputQChi innerPair633Input
    leaf5258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5258LowerChecked :
    lowerCheck 24 leaf5258Box leaf5258Inputs = true := by
  rfl'

private theorem leaf5258CoversExact : CoversExact 8
    leaf5258Box leaf5258Certificate leaf5258InnerLog leaf5258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi290RoundedFacts
    innerPair633RoundedFacts leaf5258RoundedFacts (by rfl)

private theorem leaf5258FlatSound : Sound leaf5258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5258CertificateValid
    leaf5258InnerLogValid leaf5258CoversExact leaf5258LowerChecked

private noncomputable def leaf5259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2021017344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1149430887/1073741824) }, upper := { exponent := 1, mantissa := (17737/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042118671/4042034688) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5259InnerLog : WideLogData :=
  innerPair554Data

set_option maxRecDepth 1000000 in
private theorem leaf5259LocalValidity :
    LeafFacts leaf5259Box leaf5259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2021017344) }) = true
      norm_num [leaf5259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5259CertificateValid :
    WideCertificateValid leaf5259Box leaf5259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi291ValidityFacts
    leaf5259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5259CoverageChecked :
    coverageCheck (innerAD leaf5259Box) leaf5259InnerLog = true := by
  rfl'

private theorem leaf5259InnerLogValid :
    leaf5259InnerLog.Valid 8 (innerAD leaf5259Box) :=
  wideLogDataValid_of_cachedCheck endpoint289PositiveFacts
    endpoint337PositiveFacts.valid leaf5259CoverageChecked

private noncomputable def leaf5259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5259InputLogOnePlusV_eq :
    leaf5259InputLogOnePlusV = outerEnclosure 24
      (leaf5259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5259RoundedFacts : LeafRoundedFacts 8
    leaf5259Certificate.logOnePlusV leaf5259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5259InputLogOnePlusV_eq }

private noncomputable def leaf5259Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi291InputQChi innerPair554Input
    leaf5259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5259LowerChecked :
    lowerCheck 24 leaf5259Box leaf5259Inputs = true := by
  rfl'

private theorem leaf5259CoversExact : CoversExact 8
    leaf5259Box leaf5259Certificate leaf5259InnerLog leaf5259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi291RoundedFacts
    innerPair554RoundedFacts leaf5259RoundedFacts (by rfl)

private theorem leaf5259FlatSound : Sound leaf5259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5259CertificateValid
    leaf5259InnerLogValid leaf5259CoversExact leaf5259LowerChecked

private noncomputable def leaf5260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357265408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1156901533/1073741824) }, upper := { exponent := 1, mantissa := (4463/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715987967/68714530816) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5260InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5260LocalValidity :
    LeafFacts leaf5260Box leaf5260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357265408) }) = true
      norm_num [leaf5260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5260CertificateValid :
    WideCertificateValid leaf5260Box leaf5260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi292ValidityFacts
    leaf5260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5260CoverageChecked :
    coverageCheck (innerAD leaf5260Box) leaf5260InnerLog = true := by
  rfl'

private theorem leaf5260InnerLogValid :
    leaf5260InnerLog.Valid 8 (innerAD leaf5260Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5260CoverageChecked

private noncomputable def leaf5260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5260InputLogOnePlusV_eq :
    leaf5260InputLogOnePlusV = outerEnclosure 24
      (leaf5260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5260RoundedFacts : LeafRoundedFacts 8
    leaf5260Certificate.logOnePlusV leaf5260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5260InputLogOnePlusV_eq }

private noncomputable def leaf5260Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi292InputQChi innerPair249Input
    leaf5260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5260LowerChecked :
    lowerCheck 24 leaf5260Box leaf5260Inputs = true := by
  rfl'

private theorem leaf5260CoversExact : CoversExact 8
    leaf5260Box leaf5260Certificate leaf5260InnerLog leaf5260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi292RoundedFacts
    innerPair249RoundedFacts leaf5260RoundedFacts (by rfl)

private theorem leaf5260FlatSound : Sound leaf5260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5260CertificateValid
    leaf5260InnerLogValid leaf5260CoversExact leaf5260LowerChecked

private noncomputable def leaf5261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357273600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1154804509/1073741824) }, upper := { exponent := 1, mantissa := (4455/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715996159/68714547200) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5261InnerLog : WideLogData :=
  innerPair632Data

set_option maxRecDepth 1000000 in
private theorem leaf5261LocalValidity :
    LeafFacts leaf5261Box leaf5261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357273600) }) = true
      norm_num [leaf5261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5261CertificateValid :
    WideCertificateValid leaf5261Box leaf5261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi291ValidityFacts
    leaf5261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5261CoverageChecked :
    coverageCheck (innerAD leaf5261Box) leaf5261InnerLog = true := by
  rfl'

private theorem leaf5261InnerLogValid :
    leaf5261InnerLog.Valid 8 (innerAD leaf5261Box) :=
  wideLogDataValid_of_cachedCheck endpoint365PositiveFacts
    endpoint367PositiveFacts.valid leaf5261CoverageChecked

private noncomputable def leaf5261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5261InputLogOnePlusV_eq :
    leaf5261InputLogOnePlusV = outerEnclosure 24
      (leaf5261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5261RoundedFacts : LeafRoundedFacts 8
    leaf5261Certificate.logOnePlusV leaf5261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5261InputLogOnePlusV_eq }

private noncomputable def leaf5261Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi291InputQChi innerPair632Input
    leaf5261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5261LowerChecked :
    lowerCheck 24 leaf5261Box leaf5261Inputs = true := by
  rfl'

private theorem leaf5261CoversExact : CoversExact 8
    leaf5261Box leaf5261Certificate leaf5261InnerLog leaf5261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi291RoundedFacts
    innerPair632RoundedFacts leaf5261RoundedFacts (by rfl)

private theorem leaf5261FlatSound : Sound leaf5261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5261CertificateValid
    leaf5261InnerLogValid leaf5261CoversExact leaf5261LowerChecked

private noncomputable def leaf5262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357243904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1162340687/1073741824) }, upper := { exponent := 1, mantissa := (1121/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715966463/68714487808) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5262InnerLog : WideLogData :=
  innerPair618Data

set_option maxRecDepth 1000000 in
private theorem leaf5262LocalValidity :
    LeafFacts leaf5262Box leaf5262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357243904) }) = true
      norm_num [leaf5262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5262CertificateValid :
    WideCertificateValid leaf5262Box leaf5262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi292ValidityFacts
    leaf5262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5262CoverageChecked :
    coverageCheck (innerAD leaf5262Box) leaf5262InnerLog = true := by
  rfl'

private theorem leaf5262InnerLogValid :
    leaf5262InnerLog.Valid 8 (innerAD leaf5262Box) :=
  wideLogDataValid_of_cachedCheck endpoint345PositiveFacts
    endpoint342PositiveFacts.valid leaf5262CoverageChecked

private noncomputable def leaf5262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5262InputLogOnePlusV_eq :
    leaf5262InputLogOnePlusV = outerEnclosure 24
      (leaf5262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5262RoundedFacts : LeafRoundedFacts 8
    leaf5262Certificate.logOnePlusV leaf5262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5262InputLogOnePlusV_eq }

private noncomputable def leaf5262Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi292InputQChi innerPair618Input
    leaf5262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5262LowerChecked :
    lowerCheck 24 leaf5262Box leaf5262Inputs = true := by
  rfl'

private theorem leaf5262CoversExact : CoversExact 8
    leaf5262Box leaf5262Certificate leaf5262InnerLog leaf5262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi292RoundedFacts
    innerPair618RoundedFacts leaf5262RoundedFacts (by rfl)

private theorem leaf5262FlatSound : Sound leaf5262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5262CertificateValid
    leaf5262InnerLogValid leaf5262CoversExact leaf5262LowerChecked

private noncomputable def leaf5263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908182784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1153362807/1073741824) }, upper := { exponent := 1, mantissa := (17797/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816571721/9816365568) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5263InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5263LocalValidity :
    LeafFacts leaf5263Box leaf5263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908182784) }) = true
      norm_num [leaf5263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5263CertificateValid :
    WideCertificateValid leaf5263Box leaf5263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi293ValidityFacts
    leaf5263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5263CoverageChecked :
    coverageCheck (innerAD leaf5263Box) leaf5263InnerLog = true := by
  rfl'

private theorem leaf5263InnerLogValid :
    leaf5263InnerLog.Valid 8 (innerAD leaf5263Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5263CoverageChecked

private noncomputable def leaf5263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5263InputLogOnePlusV_eq :
    leaf5263InputLogOnePlusV = outerEnclosure 24
      (leaf5263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5263RoundedFacts : LeafRoundedFacts 8
    leaf5263Certificate.logOnePlusV leaf5263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5263InputLogOnePlusV_eq }

private noncomputable def leaf5263Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi293InputQChi innerPair249Input
    leaf5263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5263LowerChecked :
    lowerCheck 24 leaf5263Box leaf5263Inputs = true := by
  rfl'

private theorem leaf5263CoversExact : CoversExact 8
    leaf5263Box leaf5263Certificate leaf5263InnerLog leaf5263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi293RoundedFacts
    innerPair249RoundedFacts leaf5263RoundedFacts (by rfl)

private theorem leaf5263FlatSound : Sound leaf5263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5263CertificateValid
    leaf5263InnerLogValid leaf5263CoversExact leaf5263LowerChecked

private noncomputable def leaf5264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357250560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1160702389/1073741824) }, upper := { exponent := 1, mantissa := (8955/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715973119/68714501120) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5264InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5264LocalValidity :
    LeafFacts leaf5264Box leaf5264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357250560) }) = true
      norm_num [leaf5264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5264CertificateValid :
    WideCertificateValid leaf5264Box leaf5264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi294ValidityFacts
    leaf5264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5264CoverageChecked :
    coverageCheck (innerAD leaf5264Box) leaf5264InnerLog = true := by
  rfl'

private theorem leaf5264InnerLogValid :
    leaf5264InnerLog.Valid 8 (innerAD leaf5264Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5264CoverageChecked

private noncomputable def leaf5264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf5264InputLogOnePlusV_eq :
    leaf5264InputLogOnePlusV = outerEnclosure 24
      (leaf5264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5264RoundedFacts : LeafRoundedFacts 8
    leaf5264Certificate.logOnePlusV leaf5264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5264InputLogOnePlusV_eq }

private noncomputable def leaf5264Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi294InputQChi innerPair249Input
    leaf5264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5264LowerChecked :
    lowerCheck 24 leaf5264Box leaf5264Inputs = true := by
  rfl'

private theorem leaf5264CoversExact : CoversExact 8
    leaf5264Box leaf5264Certificate leaf5264InnerLog leaf5264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi294RoundedFacts
    innerPair249RoundedFacts leaf5264RoundedFacts (by rfl)

private theorem leaf5264FlatSound : Sound leaf5264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5264CertificateValid
    leaf5264InnerLogValid leaf5264CoversExact leaf5264LowerChecked

private noncomputable def leaf5265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357257728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1158867493/1073741824) }, upper := { exponent := 1, mantissa := (8941/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715980287/68714515456) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5265InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5265LocalValidity :
    LeafFacts leaf5265Box leaf5265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357257728) }) = true
      norm_num [leaf5265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5265CertificateValid :
    WideCertificateValid leaf5265Box leaf5265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi293ValidityFacts
    leaf5265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5265CoverageChecked :
    coverageCheck (innerAD leaf5265Box) leaf5265InnerLog = true := by
  rfl'

private theorem leaf5265InnerLogValid :
    leaf5265InnerLog.Valid 8 (innerAD leaf5265Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5265CoverageChecked

private noncomputable def leaf5265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5265InputLogOnePlusV_eq :
    leaf5265InputLogOnePlusV = outerEnclosure 24
      (leaf5265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5265RoundedFacts : LeafRoundedFacts 8
    leaf5265Certificate.logOnePlusV leaf5265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5265InputLogOnePlusV_eq }

private noncomputable def leaf5265Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi293InputQChi innerPair249Input
    leaf5265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5265LowerChecked :
    lowerCheck 24 leaf5265Box leaf5265Inputs = true := by
  rfl'

private theorem leaf5265CoversExact : CoversExact 8
    leaf5265Box leaf5265Certificate leaf5265InnerLog leaf5265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi293RoundedFacts
    innerPair249RoundedFacts leaf5265RoundedFacts (by rfl)

private theorem leaf5265FlatSound : Sound leaf5265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5265CertificateValid
    leaf5265InnerLogValid leaf5265CoversExact leaf5265LowerChecked

private noncomputable def leaf5266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357228544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1166272607/1073741824) }, upper := { exponent := 1, mantissa := (4499/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715951103/68714457088) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5266InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5266LocalValidity :
    LeafFacts leaf5266Box leaf5266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357228544) }) = true
      norm_num [leaf5266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5266CertificateValid :
    WideCertificateValid leaf5266Box leaf5266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi294ValidityFacts
    leaf5266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5266CoverageChecked :
    coverageCheck (innerAD leaf5266Box) leaf5266InnerLog = true := by
  rfl'

private theorem leaf5266InnerLogValid :
    leaf5266InnerLog.Valid 8 (innerAD leaf5266Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5266CoverageChecked

private noncomputable def leaf5266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5266InputLogOnePlusV_eq :
    leaf5266InputLogOnePlusV = outerEnclosure 24
      (leaf5266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5266RoundedFacts : LeafRoundedFacts 8
    leaf5266Certificate.logOnePlusV leaf5266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5266InputLogOnePlusV_eq }

private noncomputable def leaf5266Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi294InputQChi innerPair612Input
    leaf5266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5266LowerChecked :
    lowerCheck 24 leaf5266Box leaf5266Inputs = true := by
  rfl'

private theorem leaf5266CoversExact : CoversExact 8
    leaf5266Box leaf5266Certificate leaf5266InnerLog leaf5266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi294RoundedFacts
    innerPair612RoundedFacts leaf5266RoundedFacts (by rfl)

private theorem leaf5266FlatSound : Sound leaf5266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5266CertificateValid
    leaf5266InnerLogValid leaf5266CoversExact leaf5266LowerChecked

private noncomputable def leaf5267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (8191/8192), upper := (1108345889/1108297472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1168041971/1073741824) }, upper := { exponent := 1, mantissa := (18023/16384) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2216643361/2216594944) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5267InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5267LocalValidity :
    LeafFacts leaf5267Box leaf5267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1108345889/1108297472) }) = true
      norm_num [leaf5267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5267CertificateValid :
    WideCertificateValid leaf5267Box leaf5267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi295ValidityFacts
    leaf5267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5267CoverageChecked :
    coverageCheck (innerAD leaf5267Box) leaf5267InnerLog = true := by
  rfl'

private theorem leaf5267InnerLogValid :
    leaf5267InnerLog.Valid 8 (innerAD leaf5267Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5267CoverageChecked

private noncomputable def leaf5267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5267InputLogOnePlusV_eq :
    leaf5267InputLogOnePlusV = outerEnclosure 24
      (leaf5267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5267RoundedFacts : LeafRoundedFacts 8
    leaf5267Certificate.logOnePlusV leaf5267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5267InputLogOnePlusV_eq }

private noncomputable def leaf5267Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi295InputQChi innerPair612Input
    leaf5267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5267LowerChecked :
    lowerCheck 24 leaf5267Box leaf5267Inputs = true := by
  rfl'

private theorem leaf5267CoversExact : CoversExact 8
    leaf5267Box leaf5267Certificate leaf5267InnerLog leaf5267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi295RoundedFacts
    innerPair612RoundedFacts leaf5267RoundedFacts (by rfl)

private theorem leaf5267FlatSound : Sound leaf5267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5267CertificateValid
    leaf5267InnerLogValid leaf5267CoversExact leaf5267LowerChecked

private noncomputable def leaf5268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357192704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1175381553/1073741824) }, upper := { exponent := 1, mantissa := (2267/2048) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715915263/68714385408) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf5268InnerLog : WideLogData :=
  innerPair259Data

set_option maxRecDepth 1000000 in
private theorem leaf5268LocalValidity :
    LeafFacts leaf5268Box leaf5268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357192704) }) = true
      norm_num [leaf5268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5268CertificateValid :
    WideCertificateValid leaf5268Box leaf5268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi296ValidityFacts
    leaf5268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5268CoverageChecked :
    coverageCheck (innerAD leaf5268Box) leaf5268InnerLog = true := by
  rfl'

private theorem leaf5268InnerLogValid :
    leaf5268InnerLog.Valid 8 (innerAD leaf5268Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint80PositiveFacts.valid leaf5268CoverageChecked

private noncomputable def leaf5268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5268InputLogOnePlusV_eq :
    leaf5268InputLogOnePlusV = outerEnclosure 24
      (leaf5268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5268RoundedFacts : LeafRoundedFacts 8
    leaf5268Certificate.logOnePlusV leaf5268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5268InputLogOnePlusV_eq }

private noncomputable def leaf5268Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi296InputQChi innerPair259Input
    leaf5268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5268LowerChecked :
    lowerCheck 24 leaf5268Box leaf5268Inputs = true := by
  rfl'

private theorem leaf5268CoversExact : CoversExact 8
    leaf5268Box leaf5268Certificate leaf5268InnerLog leaf5268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi296RoundedFacts
    innerPair259RoundedFacts leaf5268RoundedFacts (by rfl)

private theorem leaf5268FlatSound : Sound leaf5268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5268CertificateValid
    leaf5268InnerLogValid leaf5268CoversExact leaf5268LowerChecked

private noncomputable def leaf5269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357199360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1173677721/1073741824) }, upper := { exponent := 1, mantissa := (9055/8192) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715921919/68714398720) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5269InnerLog : WideLogData :=
  innerPair611Data

set_option maxRecDepth 1000000 in
private theorem leaf5269LocalValidity :
    LeafFacts leaf5269Box leaf5269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357199360) }) = true
      norm_num [leaf5269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5269CertificateValid :
    WideCertificateValid leaf5269Box leaf5269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi295ValidityFacts
    leaf5269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5269CoverageChecked :
    coverageCheck (innerAD leaf5269Box) leaf5269InnerLog = true := by
  rfl'

private theorem leaf5269InnerLogValid :
    leaf5269InnerLog.Valid 8 (innerAD leaf5269Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint80PositiveFacts.valid leaf5269CoverageChecked

private noncomputable def leaf5269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5269InputLogOnePlusV_eq :
    leaf5269InputLogOnePlusV = outerEnclosure 24
      (leaf5269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5269RoundedFacts : LeafRoundedFacts 8
    leaf5269Certificate.logOnePlusV leaf5269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5269InputLogOnePlusV_eq }

private noncomputable def leaf5269Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi295InputQChi innerPair611Input
    leaf5269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5269LowerChecked :
    lowerCheck 24 leaf5269Box leaf5269Inputs = true := by
  rfl'

private theorem leaf5269CoversExact : CoversExact 8
    leaf5269Box leaf5269Certificate leaf5269InnerLog leaf5269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi295RoundedFacts
    innerPair611RoundedFacts leaf5269RoundedFacts (by rfl)

private theorem leaf5269FlatSound : Sound leaf5269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5269CertificateValid
    leaf5269InnerLogValid leaf5269CoversExact leaf5269LowerChecked

private noncomputable def leaf5270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908167168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1181082835/1073741824) }, upper := { exponent := 1, mantissa := (1139/1024) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816556105/9816334336) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf5270InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5270LocalValidity :
    LeafFacts leaf5270Box leaf5270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908167168) }) = true
      norm_num [leaf5270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5270CertificateValid :
    WideCertificateValid leaf5270Box leaf5270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi296ValidityFacts
    leaf5270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5270CoverageChecked :
    coverageCheck (innerAD leaf5270Box) leaf5270InnerLog = true := by
  rfl'

private theorem leaf5270InnerLogValid :
    leaf5270InnerLog.Valid 8 (innerAD leaf5270Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5270CoverageChecked

private noncomputable def leaf5270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5270InputLogOnePlusV_eq :
    leaf5270InputLogOnePlusV = outerEnclosure 24
      (leaf5270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5270RoundedFacts : LeafRoundedFacts 8
    leaf5270Certificate.logOnePlusV leaf5270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5270InputLogOnePlusV_eq }

private noncomputable def leaf5270Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi296InputQChi innerPair256Input
    leaf5270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5270LowerChecked :
    lowerCheck 24 leaf5270Box leaf5270Inputs = true := by
  rfl'

private theorem leaf5270CoversExact : CoversExact 8
    leaf5270Box leaf5270Certificate leaf5270InnerLog leaf5270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi296RoundedFacts
    innerPair256RoundedFacts leaf5270RoundedFacts (by rfl)

private theorem leaf5270FlatSound : Sound leaf5270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5270CertificateValid
    leaf5270InnerLogValid leaf5270CoversExact leaf5270LowerChecked

private noncomputable def leaf5271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357235968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1164372179/1073741824) }, upper := { exponent := 1, mantissa := (17967/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715958527/68714471936) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5271InnerLog : WideLogData :=
  innerPair332Data

set_option maxRecDepth 1000000 in
private theorem leaf5271LocalValidity :
    LeafFacts leaf5271Box leaf5271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357235968) }) = true
      norm_num [leaf5271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5271CertificateValid :
    WideCertificateValid leaf5271Box leaf5271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi293ValidityFacts
    leaf5271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5271CoverageChecked :
    coverageCheck (innerAD leaf5271Box) leaf5271InnerLog = true := by
  rfl'

private theorem leaf5271InnerLogValid :
    leaf5271InnerLog.Valid 8 (innerAD leaf5271Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint291PositiveFacts.valid leaf5271CoverageChecked

private noncomputable def leaf5271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5271InputLogOnePlusV_eq :
    leaf5271InputLogOnePlusV = outerEnclosure 24
      (leaf5271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5271RoundedFacts : LeafRoundedFacts 8
    leaf5271Certificate.logOnePlusV leaf5271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5271InputLogOnePlusV_eq }

private noncomputable def leaf5271Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi293InputQChi innerPair332Input
    leaf5271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5271LowerChecked :
    lowerCheck 24 leaf5271Box leaf5271Inputs = true := by
  rfl'

private theorem leaf5271CoversExact : CoversExact 8
    leaf5271Box leaf5271Certificate leaf5271InnerLog leaf5271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi293RoundedFacts
    innerPair332RoundedFacts leaf5271RoundedFacts (by rfl)

private theorem leaf5271FlatSound : Sound leaf5271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5271CertificateValid
    leaf5271InnerLogValid leaf5271CoversExact leaf5271LowerChecked

private noncomputable def leaf5272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357206528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1171842825/1073741824) }, upper := { exponent := 1, mantissa := (9041/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715929087/68714413056) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5272InnerLog : WideLogData :=
  innerPair611Data

set_option maxRecDepth 1000000 in
private theorem leaf5272LocalValidity :
    LeafFacts leaf5272Box leaf5272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357206528) }) = true
      norm_num [leaf5272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5272CertificateValid :
    WideCertificateValid leaf5272Box leaf5272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi294ValidityFacts
    leaf5272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5272CoverageChecked :
    coverageCheck (innerAD leaf5272Box) leaf5272InnerLog = true := by
  rfl'

private theorem leaf5272InnerLogValid :
    leaf5272InnerLog.Valid 8 (innerAD leaf5272Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint80PositiveFacts.valid leaf5272CoverageChecked

private noncomputable def leaf5272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5272InputLogOnePlusV_eq :
    leaf5272InputLogOnePlusV = outerEnclosure 24
      (leaf5272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5272RoundedFacts : LeafRoundedFacts 8
    leaf5272Certificate.logOnePlusV leaf5272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5272InputLogOnePlusV_eq }

private noncomputable def leaf5272Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi294InputQChi innerPair611Input
    leaf5272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5272LowerChecked :
    lowerCheck 24 leaf5272Box leaf5272Inputs = true := by
  rfl'

private theorem leaf5272CoversExact : CoversExact 8
    leaf5272Box leaf5272Certificate leaf5272InnerLog leaf5272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi294RoundedFacts
    innerPair611RoundedFacts leaf5272RoundedFacts (by rfl)

private theorem leaf5272FlatSound : Sound leaf5272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5272CertificateValid
    leaf5272InnerLogValid leaf5272CoversExact leaf5272LowerChecked

private noncomputable def leaf5273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357214208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1169876865/1073741824) }, upper := { exponent := 1, mantissa := (4513/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715936767/68714428416) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5273InnerLog : WideLogData :=
  innerPair634Data

set_option maxRecDepth 1000000 in
private theorem leaf5273LocalValidity :
    LeafFacts leaf5273Box leaf5273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357214208) }) = true
      norm_num [leaf5273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5273CertificateValid :
    WideCertificateValid leaf5273Box leaf5273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi293ValidityFacts
    leaf5273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5273CoverageChecked :
    coverageCheck (innerAD leaf5273Box) leaf5273InnerLog = true := by
  rfl'

private theorem leaf5273InnerLogValid :
    leaf5273InnerLog.Valid 8 (innerAD leaf5273Box) :=
  wideLogDataValid_of_cachedCheck endpoint367PositiveFacts
    endpoint346PositiveFacts.valid leaf5273CoverageChecked

private noncomputable def leaf5273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5273InputLogOnePlusV_eq :
    leaf5273InputLogOnePlusV = outerEnclosure 24
      (leaf5273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5273RoundedFacts : LeafRoundedFacts 8
    leaf5273Certificate.logOnePlusV leaf5273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5273InputLogOnePlusV_eq }

private noncomputable def leaf5273Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi293InputQChi innerPair634Input
    leaf5273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5273LowerChecked :
    lowerCheck 24 leaf5273Box leaf5273Inputs = true := by
  rfl'

private theorem leaf5273CoversExact : CoversExact 8
    leaf5273Box leaf5273Certificate leaf5273InnerLog leaf5273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi293RoundedFacts
    innerPair634RoundedFacts leaf5273RoundedFacts (by rfl)

private theorem leaf5273FlatSound : Sound leaf5273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5273CertificateValid
    leaf5273InnerLogValid leaf5273CoversExact leaf5273LowerChecked

private noncomputable def leaf5274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908169216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1177413043/1073741824) }, upper := { exponent := 1, mantissa := (2271/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816558153/9816338432) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5274InnerLog : WideLogData :=
  innerPair259Data

set_option maxRecDepth 1000000 in
private theorem leaf5274LocalValidity :
    LeafFacts leaf5274Box leaf5274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908169216) }) = true
      norm_num [leaf5274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5274CertificateValid :
    WideCertificateValid leaf5274Box leaf5274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi294ValidityFacts
    leaf5274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5274CoverageChecked :
    coverageCheck (innerAD leaf5274Box) leaf5274InnerLog = true := by
  rfl'

private theorem leaf5274InnerLogValid :
    leaf5274InnerLog.Valid 8 (innerAD leaf5274Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint80PositiveFacts.valid leaf5274CoverageChecked

private noncomputable def leaf5274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5274InputLogOnePlusV_eq :
    leaf5274InputLogOnePlusV = outerEnclosure 24
      (leaf5274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5274RoundedFacts : LeafRoundedFacts 8
    leaf5274Certificate.logOnePlusV leaf5274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5274InputLogOnePlusV_eq }

private noncomputable def leaf5274Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi294InputQChi innerPair259Input
    leaf5274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5274LowerChecked :
    lowerCheck 24 leaf5274Box leaf5274Inputs = true := by
  rfl'

private theorem leaf5274CoversExact : CoversExact 8
    leaf5274Box leaf5274Certificate leaf5274InnerLog leaf5274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi294RoundedFacts
    innerPair259RoundedFacts leaf5274RoundedFacts (by rfl)

private theorem leaf5274FlatSound : Sound leaf5274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5274CertificateValid
    leaf5274InnerLogValid leaf5274CoversExact leaf5274LowerChecked

private noncomputable def leaf5275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357177088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1179313471/1073741824) }, upper := { exponent := 1, mantissa := (18197/16384) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715899647/68714354176) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5275InnerLog : WideLogData :=
  innerPair262Data

set_option maxRecDepth 1000000 in
private theorem leaf5275LocalValidity :
    LeafFacts leaf5275Box leaf5275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357177088) }) = true
      norm_num [leaf5275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5275CertificateValid :
    WideCertificateValid leaf5275Box leaf5275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi295ValidityFacts
    leaf5275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5275CoverageChecked :
    coverageCheck (innerAD leaf5275Box) leaf5275InnerLog = true := by
  rfl'

private theorem leaf5275InnerLogValid :
    leaf5275InnerLog.Valid 8 (innerAD leaf5275Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint347PositiveFacts.valid leaf5275CoverageChecked

private noncomputable def leaf5275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5275InputLogOnePlusV_eq :
    leaf5275InputLogOnePlusV = outerEnclosure 24
      (leaf5275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5275RoundedFacts : LeafRoundedFacts 8
    leaf5275Certificate.logOnePlusV leaf5275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5275InputLogOnePlusV_eq }

private noncomputable def leaf5275Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi295InputQChi innerPair262Input
    leaf5275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5275LowerChecked :
    lowerCheck 24 leaf5275Box leaf5275Inputs = true := by
  rfl'

private theorem leaf5275CoversExact : CoversExact 8
    leaf5275Box leaf5275Certificate leaf5275InnerLog leaf5275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi295RoundedFacts
    innerPair262RoundedFacts leaf5275RoundedFacts (by rfl)

private theorem leaf5275FlatSound : Sound leaf5275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5275CertificateValid
    leaf5275InnerLogValid leaf5275CoversExact leaf5275LowerChecked

private noncomputable def leaf5276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357147648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1186784117/1073741824) }, upper := { exponent := 1, mantissa := (2289/2048) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715870207/68714295296) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf5276InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5276LocalValidity :
    LeafFacts leaf5276Box leaf5276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357147648) }) = true
      norm_num [leaf5276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5276CertificateValid :
    WideCertificateValid leaf5276Box leaf5276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi296ValidityFacts
    leaf5276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5276CoverageChecked :
    coverageCheck (innerAD leaf5276Box) leaf5276InnerLog = true := by
  rfl'

private theorem leaf5276InnerLogValid :
    leaf5276InnerLog.Valid 8 (innerAD leaf5276Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5276CoverageChecked

private noncomputable def leaf5276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5276InputLogOnePlusV_eq :
    leaf5276InputLogOnePlusV = outerEnclosure 24
      (leaf5276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5276RoundedFacts : LeafRoundedFacts 8
    leaf5276Certificate.logOnePlusV leaf5276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5276InputLogOnePlusV_eq }

private noncomputable def leaf5276Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi296InputQChi innerPair256Input
    leaf5276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5276LowerChecked :
    lowerCheck 24 leaf5276Box leaf5276Inputs = true := by
  rfl'

private theorem leaf5276CoversExact : CoversExact 8
    leaf5276Box leaf5276Certificate leaf5276InnerLog leaf5276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi296RoundedFacts
    innerPair256RoundedFacts leaf5276RoundedFacts (by rfl)

private theorem leaf5276FlatSound : Sound leaf5276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5276CertificateValid
    leaf5276InnerLogValid leaf5276CoversExact leaf5276LowerChecked

private noncomputable def leaf5277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357154816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1184949221/1073741824) }, upper := { exponent := 1, mantissa := (4571/4096) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715877375/68714309632) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5277InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5277LocalValidity :
    LeafFacts leaf5277Box leaf5277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357154816) }) = true
      norm_num [leaf5277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5277CertificateValid :
    WideCertificateValid leaf5277Box leaf5277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi295ValidityFacts
    leaf5277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5277CoverageChecked :
    coverageCheck (innerAD leaf5277Box) leaf5277InnerLog = true := by
  rfl'

private theorem leaf5277InnerLogValid :
    leaf5277InnerLog.Valid 8 (innerAD leaf5277Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5277CoverageChecked

private noncomputable def leaf5277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5277InputLogOnePlusV_eq :
    leaf5277InputLogOnePlusV = outerEnclosure 24
      (leaf5277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5277RoundedFacts : LeafRoundedFacts 8
    leaf5277Certificate.logOnePlusV leaf5277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5277InputLogOnePlusV_eq }

private noncomputable def leaf5277Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi295InputQChi innerPair256Input
    leaf5277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5277LowerChecked :
    lowerCheck 24 leaf5277Box leaf5277Inputs = true := by
  rfl'

private theorem leaf5277CoversExact : CoversExact 8
    leaf5277Box leaf5277Certificate leaf5277InnerLog leaf5277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi295RoundedFacts
    innerPair256RoundedFacts leaf5277RoundedFacts (by rfl)

private theorem leaf5277FlatSound : Sound leaf5277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5277CertificateValid
    leaf5277InnerLogValid leaf5277CoversExact leaf5277LowerChecked

private noncomputable def leaf5278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2021007360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1192485399/1073741824) }, upper := { exponent := 1, mantissa := (575/512) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042108687/4042014720) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf5278InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5278LocalValidity :
    LeafFacts leaf5278Box leaf5278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2021007360) }) = true
      norm_num [leaf5278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5278CertificateValid :
    WideCertificateValid leaf5278Box leaf5278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi296ValidityFacts
    leaf5278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5278CoverageChecked :
    coverageCheck (innerAD leaf5278Box) leaf5278InnerLog = true := by
  rfl'

private theorem leaf5278InnerLogValid :
    leaf5278InnerLog.Valid 8 (innerAD leaf5278Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5278CoverageChecked

private noncomputable def leaf5278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5278InputLogOnePlusV_eq :
    leaf5278InputLogOnePlusV = outerEnclosure 24
      (leaf5278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5278RoundedFacts : LeafRoundedFacts 8
    leaf5278Certificate.logOnePlusV leaf5278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5278InputLogOnePlusV_eq }

private noncomputable def leaf5278Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi296InputQChi innerPair256Input
    leaf5278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5278LowerChecked :
    lowerCheck 24 leaf5278Box leaf5278Inputs = true := by
  rfl'

private theorem leaf5278CoversExact : CoversExact 8
    leaf5278Box leaf5278Certificate leaf5278InnerLog leaf5278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi296RoundedFacts
    innerPair256RoundedFacts leaf5278RoundedFacts (by rfl)

private theorem leaf5278FlatSound : Sound leaf5278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5278CertificateValid
    leaf5278InnerLogValid leaf5278CoversExact leaf5278LowerChecked

private noncomputable def component106Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node0_sound : Sound component106Node0Box :=
  sound_of_literal_split component106Node0Box leaf5247Box leaf5248Box
    .chi (81/256) (by rfl) (by rfl)
    leaf5247FlatSound leaf5248FlatSound

private noncomputable def component106Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node1_sound : Sound component106Node1Box :=
  sound_of_literal_split component106Node1Box leaf5249Box leaf5250Box
    .chi (81/256) (by rfl) (by rfl)
    leaf5249FlatSound leaf5250FlatSound

private noncomputable def component106Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node2_sound : Sound component106Node2Box :=
  sound_of_literal_split component106Node2Box component106Node0Box component106Node1Box
    .k (113/32) (by rfl) (by rfl)
    component106Node0_sound component106Node1_sound

private noncomputable def component106Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node3_sound : Sound component106Node3Box :=
  sound_of_literal_split component106Node3Box leaf5251Box leaf5252Box
    .chi (83/256) (by rfl) (by rfl)
    leaf5251FlatSound leaf5252FlatSound

private noncomputable def component106Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node4_sound : Sound component106Node4Box :=
  sound_of_literal_split component106Node4Box leaf5253Box leaf5254Box
    .chi (83/256) (by rfl) (by rfl)
    leaf5253FlatSound leaf5254FlatSound

private noncomputable def component106Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node5_sound : Sound component106Node5Box :=
  sound_of_literal_split component106Node5Box component106Node3Box component106Node4Box
    .k (113/32) (by rfl) (by rfl)
    component106Node3_sound component106Node4_sound

private noncomputable def component106Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node6_sound : Sound component106Node6Box :=
  sound_of_literal_split component106Node6Box component106Node2Box component106Node5Box
    .chi (41/128) (by rfl) (by rfl)
    component106Node2_sound component106Node5_sound

private noncomputable def component106Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node7_sound : Sound component106Node7Box :=
  sound_of_literal_split component106Node7Box leaf5255Box leaf5256Box
    .chi (81/256) (by rfl) (by rfl)
    leaf5255FlatSound leaf5256FlatSound

private noncomputable def component106Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node8_sound : Sound component106Node8Box :=
  sound_of_literal_split component106Node8Box leaf5257Box leaf5258Box
    .chi (81/256) (by rfl) (by rfl)
    leaf5257FlatSound leaf5258FlatSound

private noncomputable def component106Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node9_sound : Sound component106Node9Box :=
  sound_of_literal_split component106Node9Box component106Node7Box component106Node8Box
    .k (115/32) (by rfl) (by rfl)
    component106Node7_sound component106Node8_sound

private noncomputable def component106Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node10_sound : Sound component106Node10Box :=
  sound_of_literal_split component106Node10Box leaf5259Box leaf5260Box
    .chi (83/256) (by rfl) (by rfl)
    leaf5259FlatSound leaf5260FlatSound

private noncomputable def component106Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node11_sound : Sound component106Node11Box :=
  sound_of_literal_split component106Node11Box leaf5261Box leaf5262Box
    .chi (83/256) (by rfl) (by rfl)
    leaf5261FlatSound leaf5262FlatSound

private noncomputable def component106Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node12_sound : Sound component106Node12Box :=
  sound_of_literal_split component106Node12Box component106Node10Box component106Node11Box
    .k (115/32) (by rfl) (by rfl)
    component106Node10_sound component106Node11_sound

private noncomputable def component106Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node13_sound : Sound component106Node13Box :=
  sound_of_literal_split component106Node13Box component106Node9Box component106Node12Box
    .chi (41/128) (by rfl) (by rfl)
    component106Node9_sound component106Node12_sound

private noncomputable def component106Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component106Node14_sound : Sound component106Node14Box :=
  sound_of_literal_split component106Node14Box component106Node6Box component106Node13Box
    .k (57/16) (by rfl) (by rfl)
    component106Node6_sound component106Node13_sound

private noncomputable def component106Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node15_sound : Sound component106Node15Box :=
  sound_of_literal_split component106Node15Box leaf5263Box leaf5264Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5263FlatSound leaf5264FlatSound

private noncomputable def component106Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node16_sound : Sound component106Node16Box :=
  sound_of_literal_split component106Node16Box leaf5265Box leaf5266Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5265FlatSound leaf5266FlatSound

private noncomputable def component106Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node17_sound : Sound component106Node17Box :=
  sound_of_literal_split component106Node17Box component106Node15Box component106Node16Box
    .k (113/32) (by rfl) (by rfl)
    component106Node15_sound component106Node16_sound

private noncomputable def component106Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node18_sound : Sound component106Node18Box :=
  sound_of_literal_split component106Node18Box leaf5267Box leaf5268Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5267FlatSound leaf5268FlatSound

private noncomputable def component106Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node19_sound : Sound component106Node19Box :=
  sound_of_literal_split component106Node19Box leaf5269Box leaf5270Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5269FlatSound leaf5270FlatSound

private noncomputable def component106Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node20_sound : Sound component106Node20Box :=
  sound_of_literal_split component106Node20Box component106Node18Box component106Node19Box
    .k (113/32) (by rfl) (by rfl)
    component106Node18_sound component106Node19_sound

private noncomputable def component106Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node21_sound : Sound component106Node21Box :=
  sound_of_literal_split component106Node21Box component106Node17Box component106Node20Box
    .chi (43/128) (by rfl) (by rfl)
    component106Node17_sound component106Node20_sound

private noncomputable def component106Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node22_sound : Sound component106Node22Box :=
  sound_of_literal_split component106Node22Box leaf5271Box leaf5272Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5271FlatSound leaf5272FlatSound

private noncomputable def component106Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node23_sound : Sound component106Node23Box :=
  sound_of_literal_split component106Node23Box leaf5273Box leaf5274Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5273FlatSound leaf5274FlatSound

private noncomputable def component106Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component106Node24_sound : Sound component106Node24Box :=
  sound_of_literal_split component106Node24Box component106Node22Box component106Node23Box
    .k (115/32) (by rfl) (by rfl)
    component106Node22_sound component106Node23_sound

private noncomputable def component106Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node25_sound : Sound component106Node25Box :=
  sound_of_literal_split component106Node25Box leaf5275Box leaf5276Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5275FlatSound leaf5276FlatSound

private noncomputable def component106Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node26_sound : Sound component106Node26Box :=
  sound_of_literal_split component106Node26Box leaf5277Box leaf5278Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5277FlatSound leaf5278FlatSound

private noncomputable def component106Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node27_sound : Sound component106Node27Box :=
  sound_of_literal_split component106Node27Box component106Node25Box component106Node26Box
    .k (115/32) (by rfl) (by rfl)
    component106Node25_sound component106Node26_sound

private noncomputable def component106Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node28_sound : Sound component106Node28Box :=
  sound_of_literal_split component106Node28Box component106Node24Box component106Node27Box
    .chi (43/128) (by rfl) (by rfl)
    component106Node24_sound component106Node27_sound

private noncomputable def component106Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component106Node29_sound : Sound component106Node29Box :=
  sound_of_literal_split component106Node29Box component106Node21Box component106Node28Box
    .k (57/16) (by rfl) (by rfl)
    component106Node21_sound component106Node28_sound

noncomputable def component106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
theorem component106_sound : Sound component106Box :=
  sound_of_literal_split component106Box component106Node14Box component106Node29Box
    .chi (21/64) (by rfl) (by rfl)
    component106Node14_sound component106Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
