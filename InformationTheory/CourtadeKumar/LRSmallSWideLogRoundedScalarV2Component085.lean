import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf4135Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf4135Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357332992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (280976423/268435456) }, upper := { exponent := 1, mantissa := (4397/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716055551/68714665984) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4135InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4135LocalValidity :
    LeafFacts leaf4135Box leaf4135Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4135Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357332992) }) = true
      norm_num [leaf4135Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4135CertificateValid :
    WideCertificateValid leaf4135Box leaf4135Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi66ValidityFacts
    leaf4135LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4135CoverageChecked :
    coverageCheck (innerAD leaf4135Box) leaf4135InnerLog = true := by
  rfl'

private theorem leaf4135InnerLogValid :
    leaf4135InnerLog.Valid 8 (innerAD leaf4135Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4135CoverageChecked

private noncomputable def leaf4135InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4135InputLogOnePlusV_eq :
    leaf4135InputLogOnePlusV = outerEnclosure 24
      (leaf4135Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4135RoundedFacts : LeafRoundedFacts 8
    leaf4135Certificate.logOnePlusV leaf4135InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4135InputLogOnePlusV_eq }

private noncomputable def leaf4135Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi66InputQChi innerPair243Input
    leaf4135InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4135LowerChecked :
    lowerCheck 24 leaf4135Box leaf4135Inputs = true := by
  rfl'

private theorem leaf4135CoversExact : CoversExact 8
    leaf4135Box leaf4135Certificate leaf4135InnerLog leaf4135Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi66RoundedFacts
    innerPair243RoundedFacts leaf4135RoundedFacts (by rfl)

private theorem leaf4135FlatSound : Sound leaf4135Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4135CertificateValid
    leaf4135InnerLogValid leaf4135CoversExact leaf4135LowerChecked

private noncomputable def leaf4136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf4136Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357303296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (282811317/268435456) }, upper := { exponent := 1, mantissa := (2213/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716025855/68714606592) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4136InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4136LocalValidity :
    LeafFacts leaf4136Box leaf4136Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4136Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357303296) }) = true
      norm_num [leaf4136Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4136CertificateValid :
    WideCertificateValid leaf4136Box leaf4136Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi66ValidityFacts
    leaf4136LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4136CoverageChecked :
    coverageCheck (innerAD leaf4136Box) leaf4136InnerLog = true := by
  rfl'

private theorem leaf4136InnerLogValid :
    leaf4136InnerLog.Valid 8 (innerAD leaf4136Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4136CoverageChecked

private noncomputable def leaf4136InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4136InputLogOnePlusV_eq :
    leaf4136InputLogOnePlusV = outerEnclosure 24
      (leaf4136Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4136RoundedFacts : LeafRoundedFacts 8
    leaf4136Certificate.logOnePlusV leaf4136InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4136InputLogOnePlusV_eq }

private noncomputable def leaf4136Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi66InputQChi innerPair243Input
    leaf4136InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4136LowerChecked :
    lowerCheck 24 leaf4136Box leaf4136Inputs = true := by
  rfl'

private theorem leaf4136CoversExact : CoversExact 8
    leaf4136Box leaf4136Certificate leaf4136InnerLog leaf4136Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi66RoundedFacts
    innerPair243RoundedFacts leaf4136RoundedFacts (by rfl)

private theorem leaf4136FlatSound : Sound leaf4136Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4136CertificateValid
    leaf4136InnerLogValid leaf4136CoversExact leaf4136LowerChecked

private noncomputable def leaf4137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf4137Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357250048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (286218981/268435456) }, upper := { exponent := 1, mantissa := (2239/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715972607/68714500096) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4137InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4137LocalValidity :
    LeafFacts leaf4137Box leaf4137Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4137Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357250048) }) = true
      norm_num [leaf4137Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4137CertificateValid :
    WideCertificateValid leaf4137Box leaf4137Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi67ValidityFacts
    leaf4137LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4137CoverageChecked :
    coverageCheck (innerAD leaf4137Box) leaf4137InnerLog = true := by
  rfl'

private theorem leaf4137InnerLogValid :
    leaf4137InnerLog.Valid 8 (innerAD leaf4137Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4137CoverageChecked

private noncomputable def leaf4137InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4137InputLogOnePlusV_eq :
    leaf4137InputLogOnePlusV = outerEnclosure 24
      (leaf4137Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4137RoundedFacts : LeafRoundedFacts 8
    leaf4137Certificate.logOnePlusV leaf4137InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4137InputLogOnePlusV_eq }

private noncomputable def leaf4137Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi67InputQChi innerPair249Input
    leaf4137InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4137LowerChecked :
    lowerCheck 24 leaf4137Box leaf4137Inputs = true := by
  rfl'

private theorem leaf4137CoversExact : CoversExact 8
    leaf4137Box leaf4137Certificate leaf4137InnerLog leaf4137Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi67RoundedFacts
    innerPair249RoundedFacts leaf4137RoundedFacts (by rfl)

private theorem leaf4137FlatSound : Sound leaf4137Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4137CertificateValid
    leaf4137InnerLogValid leaf4137CoversExact leaf4137LowerChecked

private noncomputable def leaf4138Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf4138Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357219328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (288119407/268435456) }, upper := { exponent := 1, mantissa := (1127/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715941887/68714438656) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4138InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4138LocalValidity :
    LeafFacts leaf4138Box leaf4138Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4138Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357219328) }) = true
      norm_num [leaf4138Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4138CertificateValid :
    WideCertificateValid leaf4138Box leaf4138Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi67ValidityFacts
    leaf4138LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4138CoverageChecked :
    coverageCheck (innerAD leaf4138Box) leaf4138InnerLog = true := by
  rfl'

private theorem leaf4138InnerLogValid :
    leaf4138InnerLog.Valid 8 (innerAD leaf4138Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4138CoverageChecked

private noncomputable def leaf4138InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453681/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4138InputLogOnePlusV_eq :
    leaf4138InputLogOnePlusV = outerEnclosure 24
      (leaf4138Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4138RoundedFacts : LeafRoundedFacts 8
    leaf4138Certificate.logOnePlusV leaf4138InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4138InputLogOnePlusV_eq }

private noncomputable def leaf4138Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi67InputQChi innerPair250Input
    leaf4138InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4138LowerChecked :
    lowerCheck 24 leaf4138Box leaf4138Inputs = true := by
  rfl'

private theorem leaf4138CoversExact : CoversExact 8
    leaf4138Box leaf4138Certificate leaf4138InnerLog leaf4138Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi67RoundedFacts
    innerPair250RoundedFacts leaf4138RoundedFacts (by rfl)

private theorem leaf4138FlatSound : Sound leaf4138Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4138CertificateValid
    leaf4138InnerLogValid leaf4138CoversExact leaf4138LowerChecked

private noncomputable def leaf4139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf4139Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357273600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (284646211/268435456) }, upper := { exponent := 1, mantissa := (4455/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715996159/68714547200) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4139InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf4139LocalValidity :
    LeafFacts leaf4139Box leaf4139Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4139Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357273600) }) = true
      norm_num [leaf4139Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4139CertificateValid :
    WideCertificateValid leaf4139Box leaf4139Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi66ValidityFacts
    leaf4139LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4139CoverageChecked :
    coverageCheck (innerAD leaf4139Box) leaf4139InnerLog = true := by
  rfl'

private theorem leaf4139InnerLogValid :
    leaf4139InnerLog.Valid 8 (innerAD leaf4139Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf4139CoverageChecked

private noncomputable def leaf4139InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4139InputLogOnePlusV_eq :
    leaf4139InputLogOnePlusV = outerEnclosure 24
      (leaf4139Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4139RoundedFacts : LeafRoundedFacts 8
    leaf4139Certificate.logOnePlusV leaf4139InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4139InputLogOnePlusV_eq }

private noncomputable def leaf4139Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi66InputQChi innerPair243Input
    leaf4139InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4139LowerChecked :
    lowerCheck 24 leaf4139Box leaf4139Inputs = true := by
  rfl'

private theorem leaf4139CoversExact : CoversExact 8
    leaf4139Box leaf4139Certificate leaf4139InnerLog leaf4139Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi66RoundedFacts
    innerPair243RoundedFacts leaf4139RoundedFacts (by rfl)

private theorem leaf4139FlatSound : Sound leaf4139Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4139CertificateValid
    leaf4139InnerLogValid leaf4139CoversExact leaf4139LowerChecked

private noncomputable def leaf4140Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (7/16), chiHi := (29/64) }

private noncomputable def leaf4140Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357243904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (286481105/268435456) }, upper := { exponent := 1, mantissa := (1121/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi66LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715966463/68714487808) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4140InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4140LocalValidity :
    LeafFacts leaf4140Box leaf4140Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4140Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357243904) }) = true
      norm_num [leaf4140Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4140CertificateValid :
    WideCertificateValid leaf4140Box leaf4140Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi66ValidityFacts
    leaf4140LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4140CoverageChecked :
    coverageCheck (innerAD leaf4140Box) leaf4140InnerLog = true := by
  rfl'

private theorem leaf4140InnerLogValid :
    leaf4140InnerLog.Valid 8 (innerAD leaf4140Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4140CoverageChecked

private noncomputable def leaf4140InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4140InputLogOnePlusV_eq :
    leaf4140InputLogOnePlusV = outerEnclosure 24
      (leaf4140Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4140RoundedFacts : LeafRoundedFacts 8
    leaf4140Certificate.logOnePlusV leaf4140InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4140InputLogOnePlusV_eq }

private noncomputable def leaf4140Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi66InputQChi innerPair250Input
    leaf4140InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4140LowerChecked :
    lowerCheck 24 leaf4140Box leaf4140Inputs = true := by
  rfl'

private theorem leaf4140CoversExact : CoversExact 8
    leaf4140Box leaf4140Certificate leaf4140InnerLog leaf4140Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi66RoundedFacts
    innerPair250RoundedFacts leaf4140RoundedFacts (by rfl)

private theorem leaf4140FlatSound : Sound leaf4140Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4140CertificateValid
    leaf4140InnerLogValid leaf4140CoversExact leaf4140LowerChecked

private noncomputable def leaf4141Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf4141Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357188608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (290019833/268435456) }, upper := { exponent := 1, mantissa := (2269/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715911167/68714377216) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4141InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4141LocalValidity :
    LeafFacts leaf4141Box leaf4141Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4141Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357188608) }) = true
      norm_num [leaf4141Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4141CertificateValid :
    WideCertificateValid leaf4141Box leaf4141Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi67ValidityFacts
    leaf4141LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4141CoverageChecked :
    coverageCheck (innerAD leaf4141Box) leaf4141InnerLog = true := by
  rfl'

private theorem leaf4141InnerLogValid :
    leaf4141InnerLog.Valid 8 (innerAD leaf4141Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4141CoverageChecked

private noncomputable def leaf4141InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4141InputLogOnePlusV_eq :
    leaf4141InputLogOnePlusV = outerEnclosure 24
      (leaf4141Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4141RoundedFacts : LeafRoundedFacts 8
    leaf4141Certificate.logOnePlusV leaf4141InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4141InputLogOnePlusV_eq }

private noncomputable def leaf4141Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi67InputQChi innerPair250Input
    leaf4141InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4141LowerChecked :
    lowerCheck 24 leaf4141Box leaf4141Inputs = true := by
  rfl'

private theorem leaf4141CoversExact : CoversExact 8
    leaf4141Box leaf4141Certificate leaf4141InnerLog leaf4141Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi67RoundedFacts
    innerPair250RoundedFacts leaf4141RoundedFacts (by rfl)

private theorem leaf4141FlatSound : Sound leaf4141Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4141CertificateValid
    leaf4141InnerLogValid leaf4141CoversExact leaf4141LowerChecked

private noncomputable def leaf4142Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (29/64), chiHi := (15/32) }

private noncomputable def leaf4142Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357157888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (291920259/268435456) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi67LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715880447/68714315776) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4142InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4142LocalValidity :
    LeafFacts leaf4142Box leaf4142Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4142Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357157888) }) = true
      norm_num [leaf4142Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4142CertificateValid :
    WideCertificateValid leaf4142Box leaf4142Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi67ValidityFacts
    leaf4142LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4142CoverageChecked :
    coverageCheck (innerAD leaf4142Box) leaf4142InnerLog = true := by
  rfl'

private theorem leaf4142InnerLogValid :
    leaf4142InnerLog.Valid 8 (innerAD leaf4142Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4142CoverageChecked

private noncomputable def leaf4142InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4142InputLogOnePlusV_eq :
    leaf4142InputLogOnePlusV = outerEnclosure 24
      (leaf4142Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4142RoundedFacts : LeafRoundedFacts 8
    leaf4142Certificate.logOnePlusV leaf4142InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4142InputLogOnePlusV_eq }

private noncomputable def leaf4142Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi67InputQChi innerPair250Input
    leaf4142InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4142LowerChecked :
    lowerCheck 24 leaf4142Box leaf4142Inputs = true := by
  rfl'

private theorem leaf4142CoversExact : CoversExact 8
    leaf4142Box leaf4142Certificate leaf4142InnerLog leaf4142Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi67RoundedFacts
    innerPair250RoundedFacts leaf4142RoundedFacts (by rfl)

private theorem leaf4142FlatSound : Sound leaf4142Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4142CertificateValid
    leaf4142InnerLogValid leaf4142CoversExact leaf4142LowerChecked

private noncomputable def leaf4143Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf4143Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357167104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (291461539/268435456) }, upper := { exponent := 1, mantissa := (4559/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715889663/68714334208) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4143InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4143LocalValidity :
    LeafFacts leaf4143Box leaf4143Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4143Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357167104) }) = true
      norm_num [leaf4143Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4143CertificateValid :
    WideCertificateValid leaf4143Box leaf4143Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi68ValidityFacts
    leaf4143LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4143CoverageChecked :
    coverageCheck (innerAD leaf4143Box) leaf4143InnerLog = true := by
  rfl'

private theorem leaf4143InnerLogValid :
    leaf4143InnerLog.Valid 8 (innerAD leaf4143Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4143CoverageChecked

private noncomputable def leaf4143InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4143InputLogOnePlusV_eq :
    leaf4143InputLogOnePlusV = outerEnclosure 24
      (leaf4143Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4143RoundedFacts : LeafRoundedFacts 8
    leaf4143Certificate.logOnePlusV leaf4143InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4143InputLogOnePlusV_eq }

private noncomputable def leaf4143Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi68InputQChi innerPair250Input
    leaf4143InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4143LowerChecked :
    lowerCheck 24 leaf4143Box leaf4143Inputs = true := by
  rfl'

private theorem leaf4143CoversExact : CoversExact 8
    leaf4143Box leaf4143Certificate leaf4143InnerLog leaf4143Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi68RoundedFacts
    innerPair250RoundedFacts leaf4143RoundedFacts (by rfl)

private theorem leaf4143FlatSound : Sound leaf4143Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4143CertificateValid
    leaf4143InnerLogValid leaf4143CoversExact leaf4143LowerChecked

private noncomputable def leaf4144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf4144Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357135360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (293427497/268435456) }, upper := { exponent := 1, mantissa := (2295/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715857919/68714270720) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4144InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4144LocalValidity :
    LeafFacts leaf4144Box leaf4144Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4144Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357135360) }) = true
      norm_num [leaf4144Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4144CertificateValid :
    WideCertificateValid leaf4144Box leaf4144Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi68ValidityFacts
    leaf4144LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4144CoverageChecked :
    coverageCheck (innerAD leaf4144Box) leaf4144InnerLog = true := by
  rfl'

private theorem leaf4144InnerLogValid :
    leaf4144InnerLog.Valid 8 (innerAD leaf4144Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4144CoverageChecked

private noncomputable def leaf4144InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4144InputLogOnePlusV_eq :
    leaf4144InputLogOnePlusV = outerEnclosure 24
      (leaf4144Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4144RoundedFacts : LeafRoundedFacts 8
    leaf4144Certificate.logOnePlusV leaf4144InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4144InputLogOnePlusV_eq }

private noncomputable def leaf4144Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi68InputQChi innerPair250Input
    leaf4144InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4144LowerChecked :
    lowerCheck 24 leaf4144Box leaf4144Inputs = true := by
  rfl'

private theorem leaf4144CoversExact : CoversExact 8
    leaf4144Box leaf4144Certificate leaf4144InnerLog leaf4144Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi68RoundedFacts
    innerPair250RoundedFacts leaf4144RoundedFacts (by rfl)

private theorem leaf4144FlatSound : Sound leaf4144Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4144CertificateValid
    leaf4144InnerLogValid leaf4144CoversExact leaf4144LowerChecked

private noncomputable def leaf4145Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf4145Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908154880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (296704097/268435456) }, upper := { exponent := 1, mantissa := (145/128) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816543817/9816309760) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf4145InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4145LocalValidity :
    LeafFacts leaf4145Box leaf4145Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4145Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908154880) }) = true
      norm_num [leaf4145Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4145CertificateValid :
    WideCertificateValid leaf4145Box leaf4145Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi69ValidityFacts
    leaf4145LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4145CoverageChecked :
    coverageCheck (innerAD leaf4145Box) leaf4145InnerLog = true := by
  rfl'

private theorem leaf4145InnerLogValid :
    leaf4145InnerLog.Valid 8 (innerAD leaf4145Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4145CoverageChecked

private noncomputable def leaf4145InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629481/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4145InputLogOnePlusV_eq :
    leaf4145InputLogOnePlusV = outerEnclosure 24
      (leaf4145Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4145RoundedFacts : LeafRoundedFacts 8
    leaf4145Certificate.logOnePlusV leaf4145InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4145InputLogOnePlusV_eq }

private noncomputable def leaf4145Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi69InputQChi innerPair257Input
    leaf4145InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4145LowerChecked :
    lowerCheck 24 leaf4145Box leaf4145Inputs = true := by
  rfl'

private theorem leaf4145CoversExact : CoversExact 8
    leaf4145Box leaf4145Certificate leaf4145InnerLog leaf4145Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi69RoundedFacts
    innerPair257RoundedFacts leaf4145RoundedFacts (by rfl)

private theorem leaf4145FlatSound : Sound leaf4145Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4145CertificateValid
    leaf4145InnerLogValid leaf4145CoversExact leaf4145LowerChecked

private noncomputable def leaf4146Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf4146Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357051392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (298735587/268435456) }, upper := { exponent := 1, mantissa := (73/64) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715773951/68714102784) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf4146InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4146LocalValidity :
    LeafFacts leaf4146Box leaf4146Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4146Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357051392) }) = true
      norm_num [leaf4146Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4146CertificateValid :
    WideCertificateValid leaf4146Box leaf4146Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi69ValidityFacts
    leaf4146LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4146CoverageChecked :
    coverageCheck (innerAD leaf4146Box) leaf4146InnerLog = true := by
  rfl'

private theorem leaf4146InnerLogValid :
    leaf4146InnerLog.Valid 8 (innerAD leaf4146Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4146CoverageChecked

private noncomputable def leaf4146InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4146InputLogOnePlusV_eq :
    leaf4146InputLogOnePlusV = outerEnclosure 24
      (leaf4146Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4146RoundedFacts : LeafRoundedFacts 8
    leaf4146Certificate.logOnePlusV leaf4146InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4146InputLogOnePlusV_eq }

private noncomputable def leaf4146Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi69InputQChi innerPair257Input
    leaf4146InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4146LowerChecked :
    lowerCheck 24 leaf4146Box leaf4146Inputs = true := by
  rfl'

private theorem leaf4146CoversExact : CoversExact 8
    leaf4146Box leaf4146Certificate leaf4146InnerLog leaf4146Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi69RoundedFacts
    innerPair257RoundedFacts leaf4146RoundedFacts (by rfl)

private theorem leaf4146FlatSound : Sound leaf4146Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4146CertificateValid
    leaf4146InnerLogValid leaf4146CoversExact leaf4146LowerChecked

private noncomputable def leaf4147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf4147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357103616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (295393455/268435456) }, upper := { exponent := 1, mantissa := (4621/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715826175/68714207232) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4147InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4147LocalValidity :
    LeafFacts leaf4147Box leaf4147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357103616) }) = true
      norm_num [leaf4147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4147CertificateValid :
    WideCertificateValid leaf4147Box leaf4147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi68ValidityFacts
    leaf4147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4147CoverageChecked :
    coverageCheck (innerAD leaf4147Box) leaf4147InnerLog = true := by
  rfl'

private theorem leaf4147InnerLogValid :
    leaf4147InnerLog.Valid 8 (innerAD leaf4147Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4147CoverageChecked

private noncomputable def leaf4147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4147InputLogOnePlusV_eq :
    leaf4147InputLogOnePlusV = outerEnclosure 24
      (leaf4147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4147RoundedFacts : LeafRoundedFacts 8
    leaf4147Certificate.logOnePlusV leaf4147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4147InputLogOnePlusV_eq }

private noncomputable def leaf4147Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi68InputQChi innerPair257Input
    leaf4147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4147LowerChecked :
    lowerCheck 24 leaf4147Box leaf4147Inputs = true := by
  rfl'

private theorem leaf4147CoversExact : CoversExact 8
    leaf4147Box leaf4147Certificate leaf4147InnerLog leaf4147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi68RoundedFacts
    innerPair257RoundedFacts leaf4147RoundedFacts (by rfl)

private theorem leaf4147FlatSound : Sound leaf4147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4147CertificateValid
    leaf4147InnerLogValid leaf4147CoversExact leaf4147LowerChecked

private noncomputable def leaf4148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (15/32), chiHi := (31/64) }

private noncomputable def leaf4148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357071872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (297359413/268435456) }, upper := { exponent := 1, mantissa := (1163/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi68LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715794431/68714143744) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4148InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4148LocalValidity :
    LeafFacts leaf4148Box leaf4148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357071872) }) = true
      norm_num [leaf4148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4148CertificateValid :
    WideCertificateValid leaf4148Box leaf4148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi68ValidityFacts
    leaf4148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4148CoverageChecked :
    coverageCheck (innerAD leaf4148Box) leaf4148InnerLog = true := by
  rfl'

private theorem leaf4148InnerLogValid :
    leaf4148InnerLog.Valid 8 (innerAD leaf4148Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4148CoverageChecked

private noncomputable def leaf4148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907371/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4148InputLogOnePlusV_eq :
    leaf4148InputLogOnePlusV = outerEnclosure 24
      (leaf4148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4148RoundedFacts : LeafRoundedFacts 8
    leaf4148Certificate.logOnePlusV leaf4148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4148InputLogOnePlusV_eq }

private noncomputable def leaf4148Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi68InputQChi innerPair257Input
    leaf4148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4148LowerChecked :
    lowerCheck 24 leaf4148Box leaf4148Inputs = true := by
  rfl'

private theorem leaf4148CoversExact : CoversExact 8
    leaf4148Box leaf4148Certificate leaf4148InnerLog leaf4148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi68RoundedFacts
    innerPair257RoundedFacts leaf4148RoundedFacts (by rfl)

private theorem leaf4148FlatSound : Sound leaf4148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4148CertificateValid
    leaf4148InnerLogValid leaf4148CoversExact leaf4148LowerChecked

private noncomputable def leaf4149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf4149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217957/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357018624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (300767077/268435456) }, upper := { exponent := 1, mantissa := (147/128) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715741183/68714037248) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf4149InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4149LocalValidity :
    LeafFacts leaf4149Box leaf4149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357018624) }) = true
      norm_num [leaf4149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4149CertificateValid :
    WideCertificateValid leaf4149Box leaf4149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi69ValidityFacts
    leaf4149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4149CoverageChecked :
    coverageCheck (innerAD leaf4149Box) leaf4149InnerLog = true := by
  rfl'

private theorem leaf4149InnerLogValid :
    leaf4149InnerLog.Valid 8 (innerAD leaf4149Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4149CoverageChecked

private noncomputable def leaf4149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4149InputLogOnePlusV_eq :
    leaf4149InputLogOnePlusV = outerEnclosure 24
      (leaf4149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4149RoundedFacts : LeafRoundedFacts 8
    leaf4149Certificate.logOnePlusV leaf4149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4149InputLogOnePlusV_eq }

private noncomputable def leaf4149Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi69InputQChi innerPair257Input
    leaf4149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4149LowerChecked :
    lowerCheck 24 leaf4149Box leaf4149Inputs = true := by
  rfl'

private theorem leaf4149CoversExact : CoversExact 8
    leaf4149Box leaf4149Certificate leaf4149InnerLog leaf4149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi69RoundedFacts
    innerPair257RoundedFacts leaf4149RoundedFacts (by rfl)

private theorem leaf4149FlatSound : Sound leaf4149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4149CertificateValid
    leaf4149InnerLogValid leaf4149CoversExact leaf4149LowerChecked

private noncomputable def leaf4150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (31/64), chiHi := (1/2) }

private noncomputable def leaf4150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217959/134217728) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2020999168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (302798567/268435456) }, upper := { exponent := 1, mantissa := (37/32) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi69LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042100495/4041998336) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf4150InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4150LocalValidity :
    LeafFacts leaf4150Box leaf4150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2020999168) }) = true
      norm_num [leaf4150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4150CertificateValid :
    WideCertificateValid leaf4150Box leaf4150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi69ValidityFacts
    leaf4150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4150CoverageChecked :
    coverageCheck (innerAD leaf4150Box) leaf4150InnerLog = true := by
  rfl'

private theorem leaf4150InnerLogValid :
    leaf4150InnerLog.Valid 8 (innerAD leaf4150Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4150CoverageChecked

private noncomputable def leaf4150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4150InputLogOnePlusV_eq :
    leaf4150InputLogOnePlusV = outerEnclosure 24
      (leaf4150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4150RoundedFacts : LeafRoundedFacts 8
    leaf4150Certificate.logOnePlusV leaf4150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4150InputLogOnePlusV_eq }

private noncomputable def leaf4150Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi69InputQChi innerPair264Input
    leaf4150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4150LowerChecked :
    lowerCheck 24 leaf4150Box leaf4150Inputs = true := by
  rfl'

private theorem leaf4150CoversExact : CoversExact 8
    leaf4150Box leaf4150Certificate leaf4150InnerLog leaf4150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi69RoundedFacts
    innerPair264RoundedFacts leaf4150RoundedFacts (by rfl)

private theorem leaf4150FlatSound : Sound leaf4150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4150CertificateValid
    leaf4150InnerLogValid leaf4150CoversExact leaf4150LowerChecked

private noncomputable def leaf4151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435739/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357257728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (576664935/536870912) }, upper := { exponent := 1, mantissa := (8941/8192) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715980287/68714515456) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf4151InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf4151LocalValidity :
    LeafFacts leaf4151Box leaf4151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357257728) }) = true
      norm_num [leaf4151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4151CertificateValid :
    WideCertificateValid leaf4151Box leaf4151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi267ValidityFacts
    leaf4151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4151CoverageChecked :
    coverageCheck (innerAD leaf4151Box) leaf4151InnerLog = true := by
  rfl'

private theorem leaf4151InnerLogValid :
    leaf4151InnerLog.Valid 8 (innerAD leaf4151Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf4151CoverageChecked

private noncomputable def leaf4151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4151InputLogOnePlusV_eq :
    leaf4151InputLogOnePlusV = outerEnclosure 24
      (leaf4151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4151RoundedFacts : LeafRoundedFacts 8
    leaf4151Certificate.logOnePlusV leaf4151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4151InputLogOnePlusV_eq }

private noncomputable def leaf4151Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi267InputQChi innerPair249Input
    leaf4151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4151LowerChecked :
    lowerCheck 24 leaf4151Box leaf4151Inputs = true := by
  rfl'

private theorem leaf4151CoversExact : CoversExact 8
    leaf4151Box leaf4151Certificate leaf4151InnerLog leaf4151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi267RoundedFacts
    innerPair249RoundedFacts leaf4151RoundedFacts (by rfl)

private theorem leaf4151FlatSound : Sound leaf4151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4151CertificateValid
    leaf4151InnerLogValid leaf4151CoversExact leaf4151LowerChecked

private noncomputable def leaf4152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357228544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (580334725/536870912) }, upper := { exponent := 1, mantissa := (4499/4096) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715951103/68714457088) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf4152InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4152LocalValidity :
    LeafFacts leaf4152Box leaf4152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357228544) }) = true
      norm_num [leaf4152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4152CertificateValid :
    WideCertificateValid leaf4152Box leaf4152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi267ValidityFacts
    leaf4152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4152CoverageChecked :
    coverageCheck (innerAD leaf4152Box) leaf4152InnerLog = true := by
  rfl'

private theorem leaf4152InnerLogValid :
    leaf4152InnerLog.Valid 8 (innerAD leaf4152Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4152CoverageChecked

private noncomputable def leaf4152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814723/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4152InputLogOnePlusV_eq :
    leaf4152InputLogOnePlusV = outerEnclosure 24
      (leaf4152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4152RoundedFacts : LeafRoundedFacts 8
    leaf4152Certificate.logOnePlusV leaf4152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4152InputLogOnePlusV_eq }

private noncomputable def leaf4152Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi267InputQChi innerPair250Input
    leaf4152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4152LowerChecked :
    lowerCheck 24 leaf4152Box leaf4152Inputs = true := by
  rfl'

private theorem leaf4152CoversExact : CoversExact 8
    leaf4152Box leaf4152Certificate leaf4152InnerLog leaf4152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi267RoundedFacts
    innerPair250RoundedFacts leaf4152RoundedFacts (by rfl)

private theorem leaf4152FlatSound : Sound leaf4152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4152CertificateValid
    leaf4152InnerLogValid leaf4152CoversExact leaf4152LowerChecked

private noncomputable def leaf4153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435741/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357214208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (582169621/536870912) }, upper := { exponent := 1, mantissa := (4513/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715936767/68714428416) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf4153InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4153LocalValidity :
    LeafFacts leaf4153Box leaf4153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357214208) }) = true
      norm_num [leaf4153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4153CertificateValid :
    WideCertificateValid leaf4153Box leaf4153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi268ValidityFacts
    leaf4153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4153CoverageChecked :
    coverageCheck (innerAD leaf4153Box) leaf4153InnerLog = true := by
  rfl'

private theorem leaf4153InnerLogValid :
    leaf4153InnerLog.Valid 8 (innerAD leaf4153Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4153CoverageChecked

private noncomputable def leaf4153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4153InputLogOnePlusV_eq :
    leaf4153InputLogOnePlusV = outerEnclosure 24
      (leaf4153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4153RoundedFacts : LeafRoundedFacts 8
    leaf4153Certificate.logOnePlusV leaf4153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4153InputLogOnePlusV_eq }

private noncomputable def leaf4153Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi268InputQChi innerPair250Input
    leaf4153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4153LowerChecked :
    lowerCheck 24 leaf4153Box leaf4153Inputs = true := by
  rfl'

private theorem leaf4153CoversExact : CoversExact 8
    leaf4153Box leaf4153Certificate leaf4153InnerLog leaf4153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi268RoundedFacts
    innerPair250RoundedFacts leaf4153RoundedFacts (by rfl)

private theorem leaf4153FlatSound : Sound leaf4153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4153CertificateValid
    leaf4153InnerLogValid leaf4153CoversExact leaf4153LowerChecked

private noncomputable def leaf4154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908169216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (585904943/536870912) }, upper := { exponent := 1, mantissa := (2271/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816558153/9816338432) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf4154InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4154LocalValidity :
    LeafFacts leaf4154Box leaf4154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908169216) }) = true
      norm_num [leaf4154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4154CertificateValid :
    WideCertificateValid leaf4154Box leaf4154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi268ValidityFacts
    leaf4154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4154CoverageChecked :
    coverageCheck (innerAD leaf4154Box) leaf4154InnerLog = true := by
  rfl'

private theorem leaf4154InnerLogValid :
    leaf4154InnerLog.Valid 8 (innerAD leaf4154Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4154CoverageChecked

private noncomputable def leaf4154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4154InputLogOnePlusV_eq :
    leaf4154InputLogOnePlusV = outerEnclosure 24
      (leaf4154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4154RoundedFacts : LeafRoundedFacts 8
    leaf4154Certificate.logOnePlusV leaf4154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4154InputLogOnePlusV_eq }

private noncomputable def leaf4154Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi268InputQChi innerPair250Input
    leaf4154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4154LowerChecked :
    lowerCheck 24 leaf4154Box leaf4154Inputs = true := by
  rfl'

private theorem leaf4154CoversExact : CoversExact 8
    leaf4154Box leaf4154Certificate leaf4154InnerLog leaf4154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi268RoundedFacts
    innerPair250RoundedFacts leaf4154RoundedFacts (by rfl)

private theorem leaf4154FlatSound : Sound leaf4154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4154CertificateValid
    leaf4154InnerLogValid leaf4154CoversExact leaf4154LowerChecked

private noncomputable def leaf4155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217931/134217728) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726190080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (293820711/268435456) }, upper := { exponent := 1, mantissa := (4585/4096) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452649301/11452380160) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf4155InnerLog : WideLogData :=
  innerPair260Data

set_option maxRecDepth 1000000 in
private theorem leaf4155LocalValidity :
    LeafFacts leaf4155Box leaf4155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726190080) }) = true
      norm_num [leaf4155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4155CertificateValid :
    WideCertificateValid leaf4155Box leaf4155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi269ValidityFacts
    leaf4155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4155CoverageChecked :
    coverageCheck (innerAD leaf4155Box) leaf4155InnerLog = true := by
  rfl'

private theorem leaf4155InnerLogValid :
    leaf4155InnerLog.Valid 8 (innerAD leaf4155Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint290PositiveFacts.valid leaf4155CoverageChecked

private noncomputable def leaf4155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629475/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4155InputLogOnePlusV_eq :
    leaf4155InputLogOnePlusV = outerEnclosure 24
      (leaf4155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4155RoundedFacts : LeafRoundedFacts 8
    leaf4155Certificate.logOnePlusV leaf4155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4155InputLogOnePlusV_eq }

private noncomputable def leaf4155Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi269InputQChi innerPair260Input
    leaf4155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4155LowerChecked :
    lowerCheck 24 leaf4155Box leaf4155Inputs = true := by
  rfl'

private theorem leaf4155CoversExact : CoversExact 8
    leaf4155Box leaf4155Certificate leaf4155InnerLog leaf4155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi269RoundedFacts
    innerPair260RoundedFacts leaf4155RoundedFacts (by rfl)

private theorem leaf4155FlatSound : Sound leaf4155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4155CertificateValid
    leaf4155InnerLogValid leaf4155CoversExact leaf4155LowerChecked

private noncomputable def leaf4156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217933/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178548224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (296573053/268435456) }, upper := { exponent := 1, mantissa := (1157/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357925887/34357096448) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf4156InnerLog : WideLogData :=
  innerPair556Data

set_option maxRecDepth 1000000 in
private theorem leaf4156LocalValidity :
    LeafFacts leaf4156Box leaf4156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178548224) }) = true
      norm_num [leaf4156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4156CertificateValid :
    WideCertificateValid leaf4156Box leaf4156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi270ValidityFacts
    leaf4156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4156CoverageChecked :
    coverageCheck (innerAD leaf4156Box) leaf4156InnerLog = true := by
  rfl'

private theorem leaf4156InnerLogValid :
    leaf4156InnerLog.Valid 8 (innerAD leaf4156Box) :=
  wideLogDataValid_of_cachedCheck endpoint291PositiveFacts
    endpoint292PositiveFacts.valid leaf4156CoverageChecked

private noncomputable def leaf4156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814743/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4156InputLogOnePlusV_eq :
    leaf4156InputLogOnePlusV = outerEnclosure 24
      (leaf4156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4156RoundedFacts : LeafRoundedFacts 8
    leaf4156Certificate.logOnePlusV leaf4156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4156InputLogOnePlusV_eq }

private noncomputable def leaf4156Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi270InputQChi innerPair556Input
    leaf4156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4156LowerChecked :
    lowerCheck 24 leaf4156Box leaf4156Inputs = true := by
  rfl'

private theorem leaf4156CoversExact : CoversExact 8
    leaf4156Box leaf4156Certificate leaf4156InnerLog leaf4156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi270RoundedFacts
    innerPair556RoundedFacts leaf4156RoundedFacts (by rfl)

private theorem leaf4156FlatSound : Sound leaf4156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4156CertificateValid
    leaf4156InnerLogValid leaf4156CoversExact leaf4156LowerChecked

private noncomputable def leaf4157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435743/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357199360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (584004515/536870912) }, upper := { exponent := 1, mantissa := (9055/8192) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715921919/68714398720) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4157InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf4157LocalValidity :
    LeafFacts leaf4157Box leaf4157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357199360) }) = true
      norm_num [leaf4157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4157CertificateValid :
    WideCertificateValid leaf4157Box leaf4157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi267ValidityFacts
    leaf4157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4157CoverageChecked :
    coverageCheck (innerAD leaf4157Box) leaf4157InnerLog = true := by
  rfl'

private theorem leaf4157InnerLogValid :
    leaf4157InnerLog.Valid 8 (innerAD leaf4157Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf4157CoverageChecked

private noncomputable def leaf4157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4157InputLogOnePlusV_eq :
    leaf4157InputLogOnePlusV = outerEnclosure 24
      (leaf4157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4157RoundedFacts : LeafRoundedFacts 8
    leaf4157Certificate.logOnePlusV leaf4157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4157InputLogOnePlusV_eq }

private noncomputable def leaf4157Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi267InputQChi innerPair250Input
    leaf4157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4157LowerChecked :
    lowerCheck 24 leaf4157Box leaf4157Inputs = true := by
  rfl'

private theorem leaf4157CoversExact : CoversExact 8
    leaf4157Box leaf4157Certificate leaf4157InnerLog leaf4157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi267RoundedFacts
    innerPair250RoundedFacts leaf4157RoundedFacts (by rfl)

private theorem leaf4157FlatSound : Sound leaf4157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4157CertificateValid
    leaf4157InnerLogValid leaf4157CoversExact leaf4157LowerChecked

private noncomputable def leaf4158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (7/16), chiHi := (57/128) }

private noncomputable def leaf4158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908167168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (587674305/536870912) }, upper := { exponent := 1, mantissa := (1139/1024) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi267LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816556105/9816334336) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4158InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4158LocalValidity :
    LeafFacts leaf4158Box leaf4158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908167168) }) = true
      norm_num [leaf4158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4158CertificateValid :
    WideCertificateValid leaf4158Box leaf4158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi267ValidityFacts
    leaf4158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4158CoverageChecked :
    coverageCheck (innerAD leaf4158Box) leaf4158InnerLog = true := by
  rfl'

private theorem leaf4158InnerLogValid :
    leaf4158InnerLog.Valid 8 (innerAD leaf4158Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4158CoverageChecked

private noncomputable def leaf4158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4158InputLogOnePlusV_eq :
    leaf4158InputLogOnePlusV = outerEnclosure 24
      (leaf4158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4158RoundedFacts : LeafRoundedFacts 8
    leaf4158Certificate.logOnePlusV leaf4158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4158InputLogOnePlusV_eq }

private noncomputable def leaf4158Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi267InputQChi innerPair256Input
    leaf4158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4158LowerChecked :
    lowerCheck 24 leaf4158Box leaf4158Inputs = true := by
  rfl'

private theorem leaf4158CoversExact : CoversExact 8
    leaf4158Box leaf4158Certificate leaf4158InnerLog leaf4158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi267RoundedFacts
    innerPair256RoundedFacts leaf4158RoundedFacts (by rfl)

private theorem leaf4158FlatSound : Sound leaf4158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4158CertificateValid
    leaf4158InnerLogValid leaf4158CoversExact leaf4158LowerChecked

private noncomputable def leaf4159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435745/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357154816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (589640265/536870912) }, upper := { exponent := 1, mantissa := (4571/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715877375/68714309632) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4159InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4159LocalValidity :
    LeafFacts leaf4159Box leaf4159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357154816) }) = true
      norm_num [leaf4159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4159CertificateValid :
    WideCertificateValid leaf4159Box leaf4159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi268ValidityFacts
    leaf4159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4159CoverageChecked :
    coverageCheck (innerAD leaf4159Box) leaf4159InnerLog = true := by
  rfl'

private theorem leaf4159InnerLogValid :
    leaf4159InnerLog.Valid 8 (innerAD leaf4159Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4159CoverageChecked

private noncomputable def leaf4159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453683/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4159InputLogOnePlusV_eq :
    leaf4159InputLogOnePlusV = outerEnclosure 24
      (leaf4159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4159RoundedFacts : LeafRoundedFacts 8
    leaf4159Certificate.logOnePlusV leaf4159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4159InputLogOnePlusV_eq }

private noncomputable def leaf4159Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi268InputQChi innerPair256Input
    leaf4159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4159LowerChecked :
    lowerCheck 24 leaf4159Box leaf4159Inputs = true := by
  rfl'

private theorem leaf4159CoversExact : CoversExact 8
    leaf4159Box leaf4159Certificate leaf4159InnerLog leaf4159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi268RoundedFacts
    innerPair256RoundedFacts leaf4159RoundedFacts (by rfl)

private theorem leaf4159FlatSound : Sound leaf4159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4159CertificateValid
    leaf4159InnerLogValid leaf4159CoversExact leaf4159LowerChecked

private noncomputable def leaf4160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (57/128), chiHi := (29/64) }

private noncomputable def leaf4160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (2021101327/2021007360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (593375587/536870912) }, upper := { exponent := 1, mantissa := (575/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi268LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4042108687/4042014720) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4160InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf4160LocalValidity :
    LeafFacts leaf4160Box leaf4160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2021101327/2021007360) }) = true
      norm_num [leaf4160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4160CertificateValid :
    WideCertificateValid leaf4160Box leaf4160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi268ValidityFacts
    leaf4160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4160CoverageChecked :
    coverageCheck (innerAD leaf4160Box) leaf4160InnerLog = true := by
  rfl'

private theorem leaf4160InnerLogValid :
    leaf4160InnerLog.Valid 8 (innerAD leaf4160Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf4160CoverageChecked

private noncomputable def leaf4160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4160InputLogOnePlusV_eq :
    leaf4160InputLogOnePlusV = outerEnclosure 24
      (leaf4160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4160RoundedFacts : LeafRoundedFacts 8
    leaf4160Certificate.logOnePlusV leaf4160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4160InputLogOnePlusV_eq }

private noncomputable def leaf4160Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi268InputQChi innerPair256Input
    leaf4160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4160LowerChecked :
    lowerCheck 24 leaf4160Box leaf4160Inputs = true := by
  rfl'

private theorem leaf4160CoversExact : CoversExact 8
    leaf4160Box leaf4160Certificate leaf4160InnerLog leaf4160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi268RoundedFacts
    innerPair256RoundedFacts leaf4160RoundedFacts (by rfl)

private theorem leaf4160FlatSound : Sound leaf4160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4160CertificateValid
    leaf4160InnerLogValid leaf4160CoversExact leaf4160LowerChecked

private noncomputable def leaf4161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435747/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357110272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (595276015/536870912) }, upper := { exponent := 1, mantissa := (9229/8192) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715832831/68714220544) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf4161InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4161LocalValidity :
    LeafFacts leaf4161Box leaf4161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357110272) }) = true
      norm_num [leaf4161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4161CertificateValid :
    WideCertificateValid leaf4161Box leaf4161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi269ValidityFacts
    leaf4161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4161CoverageChecked :
    coverageCheck (innerAD leaf4161Box) leaf4161InnerLog = true := by
  rfl'

private theorem leaf4161InnerLogValid :
    leaf4161InnerLog.Valid 8 (innerAD leaf4161Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4161CoverageChecked

private noncomputable def leaf4161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4161InputLogOnePlusV_eq :
    leaf4161InputLogOnePlusV = outerEnclosure 24
      (leaf4161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4161RoundedFacts : LeafRoundedFacts 8
    leaf4161Certificate.logOnePlusV leaf4161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4161InputLogOnePlusV_eq }

private noncomputable def leaf4161Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi269InputQChi innerPair257Input
    leaf4161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4161LowerChecked :
    lowerCheck 24 leaf4161Box leaf4161Inputs = true := by
  rfl'

private theorem leaf4161CoversExact : CoversExact 8
    leaf4161Box leaf4161Certificate leaf4161InnerLog leaf4161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi269RoundedFacts
    innerPair257RoundedFacts leaf4161RoundedFacts (by rfl)

private theorem leaf4161FlatSound : Sound leaf4161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4161CertificateValid
    leaf4161InnerLogValid leaf4161CoversExact leaf4161LowerChecked

private noncomputable def leaf4162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (29/64), chiHi := (59/128) }

private noncomputable def leaf4162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435749/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357080064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (599076869/536870912) }, upper := { exponent := 1, mantissa := (1161/1024) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi269LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715802623/68714160128) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf4162InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf4162LocalValidity :
    LeafFacts leaf4162Box leaf4162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357080064) }) = true
      norm_num [leaf4162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4162CertificateValid :
    WideCertificateValid leaf4162Box leaf4162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi269ValidityFacts
    leaf4162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4162CoverageChecked :
    coverageCheck (innerAD leaf4162Box) leaf4162InnerLog = true := by
  rfl'

private theorem leaf4162InnerLogValid :
    leaf4162InnerLog.Valid 8 (innerAD leaf4162Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf4162CoverageChecked

private noncomputable def leaf4162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4162InputLogOnePlusV_eq :
    leaf4162InputLogOnePlusV = outerEnclosure 24
      (leaf4162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4162RoundedFacts : LeafRoundedFacts 8
    leaf4162Certificate.logOnePlusV leaf4162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4162InputLogOnePlusV_eq }

private noncomputable def leaf4162Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi269InputQChi innerPair257Input
    leaf4162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4162LowerChecked :
    lowerCheck 24 leaf4162Box leaf4162Inputs = true := by
  rfl'

private theorem leaf4162CoversExact : CoversExact 8
    leaf4162Box leaf4162Certificate leaf4162InnerLog leaf4162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi269RoundedFacts
    innerPair257RoundedFacts leaf4162RoundedFacts (by rfl)

private theorem leaf4162FlatSound : Sound leaf4162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4162CertificateValid
    leaf4162InnerLogValid leaf4162CoversExact leaf4162LowerChecked

private noncomputable def leaf4163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (59/128), chiHi := (15/32) }

private noncomputable def leaf4163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217935/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178517504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (300439439/268435456) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi270LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357895167/34357035008) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf4163InnerLog : WideLogData :=
  innerPair562Data

set_option maxRecDepth 1000000 in
private theorem leaf4163LocalValidity :
    LeafFacts leaf4163Box leaf4163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178517504) }) = true
      norm_num [leaf4163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4163CertificateValid :
    WideCertificateValid leaf4163Box leaf4163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi270ValidityFacts
    leaf4163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4163CoverageChecked :
    coverageCheck (innerAD leaf4163Box) leaf4163InnerLog = true := by
  rfl'

private theorem leaf4163InnerLogValid :
    leaf4163InnerLog.Valid 8 (innerAD leaf4163Box) :=
  wideLogDataValid_of_cachedCheck endpoint293PositiveFacts
    endpoint294PositiveFacts.valid leaf4163CoverageChecked

private noncomputable def leaf4163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4163InputLogOnePlusV_eq :
    leaf4163InputLogOnePlusV = outerEnclosure 24
      (leaf4163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4163RoundedFacts : LeafRoundedFacts 8
    leaf4163Certificate.logOnePlusV leaf4163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4163InputLogOnePlusV_eq }

private noncomputable def leaf4163Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi270InputQChi innerPair562Input
    leaf4163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4163LowerChecked :
    lowerCheck 24 leaf4163Box leaf4163Inputs = true := by
  rfl'

private theorem leaf4163CoversExact : CoversExact 8
    leaf4163Box leaf4163Certificate leaf4163InnerLog leaf4163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi270RoundedFacts
    innerPair562RoundedFacts leaf4163RoundedFacts (by rfl)

private theorem leaf4163FlatSound : Sound leaf4163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4163CertificateValid
    leaf4163InnerLogValid leaf4163CoversExact leaf4163LowerChecked

private noncomputable def leaf4164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217935/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178526208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (299325395/268435456) }, upper := { exponent := 1, mantissa := (4671/4096) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357903871/34357052416) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf4164InnerLog : WideLogData :=
  innerPair301Data

set_option maxRecDepth 1000000 in
private theorem leaf4164LocalValidity :
    LeafFacts leaf4164Box leaf4164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178526208) }) = true
      norm_num [leaf4164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4164CertificateValid :
    WideCertificateValid leaf4164Box leaf4164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi271ValidityFacts
    leaf4164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4164CoverageChecked :
    coverageCheck (innerAD leaf4164Box) leaf4164InnerLog = true := by
  rfl'

private theorem leaf4164InnerLogValid :
    leaf4164InnerLog.Valid 8 (innerAD leaf4164Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint295PositiveFacts.valid leaf4164CoverageChecked

private noncomputable def leaf4164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629497/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4164InputLogOnePlusV_eq :
    leaf4164InputLogOnePlusV = outerEnclosure 24
      (leaf4164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4164RoundedFacts : LeafRoundedFacts 8
    leaf4164Certificate.logOnePlusV leaf4164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4164InputLogOnePlusV_eq }

private noncomputable def leaf4164Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi271InputQChi innerPair301Input
    leaf4164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4164LowerChecked :
    lowerCheck 24 leaf4164Box leaf4164Inputs = true := by
  rfl'

private theorem leaf4164CoversExact : CoversExact 8
    leaf4164Box leaf4164Certificate leaf4164InnerLog leaf4164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi271RoundedFacts
    innerPair301RoundedFacts leaf4164RoundedFacts (by rfl)

private theorem leaf4164FlatSound : Sound leaf4164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4164CertificateValid
    leaf4164InnerLogValid leaf4164CoversExact leaf4164LowerChecked

private noncomputable def leaf4165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726168064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (302077737/268435456) }, upper := { exponent := 1, mantissa := (2357/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452627285/11452336128) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf4165InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4165LocalValidity :
    LeafFacts leaf4165Box leaf4165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726168064) }) = true
      norm_num [leaf4165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4165CertificateValid :
    WideCertificateValid leaf4165Box leaf4165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi272ValidityFacts
    leaf4165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4165CoverageChecked :
    coverageCheck (innerAD leaf4165Box) leaf4165InnerLog = true := by
  rfl'

private theorem leaf4165InnerLogValid :
    leaf4165InnerLog.Valid 8 (innerAD leaf4165Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4165CoverageChecked

private noncomputable def leaf4165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4165InputLogOnePlusV_eq :
    leaf4165InputLogOnePlusV = outerEnclosure 24
      (leaf4165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4165RoundedFacts : LeafRoundedFacts 8
    leaf4165Certificate.logOnePlusV leaf4165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4165InputLogOnePlusV_eq }

private noncomputable def leaf4165Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi272InputQChi innerPair264Input
    leaf4165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4165LowerChecked :
    lowerCheck 24 leaf4165Box leaf4165Inputs = true := by
  rfl'

private theorem leaf4165CoversExact : CoversExact 8
    leaf4165Box leaf4165Certificate leaf4165InnerLog leaf4165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi272RoundedFacts
    innerPair264RoundedFacts leaf4165RoundedFacts (by rfl)

private theorem leaf4165FlatSound : Sound leaf4165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4165CertificateValid
    leaf4165InnerLogValid leaf4165CoversExact leaf4165LowerChecked

private noncomputable def leaf4166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf4166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178482176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (304830079/268435456) }, upper := { exponent := 1, mantissa := (4757/4096) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357859839/34356964352) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf4166InnerLog : WideLogData :=
  innerPair559Data

set_option maxRecDepth 1000000 in
private theorem leaf4166LocalValidity :
    LeafFacts leaf4166Box leaf4166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178482176) }) = true
      norm_num [leaf4166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4166CertificateValid :
    WideCertificateValid leaf4166Box leaf4166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi273ValidityFacts
    leaf4166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4166CoverageChecked :
    coverageCheck (innerAD leaf4166Box) leaf4166InnerLog = true := by
  rfl'

private theorem leaf4166InnerLogValid :
    leaf4166InnerLog.Valid 8 (innerAD leaf4166Box) :=
  wideLogDataValid_of_cachedCheck endpoint292PositiveFacts
    endpoint296PositiveFacts.valid leaf4166CoverageChecked

private noncomputable def leaf4166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814759/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4166InputLogOnePlusV_eq :
    leaf4166InputLogOnePlusV = outerEnclosure 24
      (leaf4166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4166RoundedFacts : LeafRoundedFacts 8
    leaf4166Certificate.logOnePlusV leaf4166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4166InputLogOnePlusV_eq }

private noncomputable def leaf4166Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi273InputQChi innerPair559Input
    leaf4166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4166LowerChecked :
    lowerCheck 24 leaf4166Box leaf4166Inputs = true := by
  rfl'

private theorem leaf4166CoversExact : CoversExact 8
    leaf4166Box leaf4166Certificate leaf4166InnerLog leaf4166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi273RoundedFacts
    innerPair559RoundedFacts leaf4166RoundedFacts (by rfl)

private theorem leaf4166FlatSound : Sound leaf4166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4166CertificateValid
    leaf4166InnerLogValid leaf4166CoversExact leaf4166LowerChecked

private noncomputable def leaf4167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf4167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178460160) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (307582421/268435456) }, upper := { exponent := 1, mantissa := (75/64) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357837823/34356920320) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf4167InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf4167LocalValidity :
    LeafFacts leaf4167Box leaf4167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178460160) }) = true
      norm_num [leaf4167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4167CertificateValid :
    WideCertificateValid leaf4167Box leaf4167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi274ValidityFacts
    leaf4167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4167CoverageChecked :
    coverageCheck (innerAD leaf4167Box) leaf4167InnerLog = true := by
  rfl'

private theorem leaf4167InnerLogValid :
    leaf4167InnerLog.Valid 8 (innerAD leaf4167Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf4167CoverageChecked

private noncomputable def leaf4167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4167InputLogOnePlusV_eq :
    leaf4167InputLogOnePlusV = outerEnclosure 24
      (leaf4167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4167RoundedFacts : LeafRoundedFacts 8
    leaf4167Certificate.logOnePlusV leaf4167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4167InputLogOnePlusV_eq }

private noncomputable def leaf4167Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi274InputQChi innerPair265Input
    leaf4167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4167LowerChecked :
    lowerCheck 24 leaf4167Box leaf4167Inputs = true := by
  rfl'

private theorem leaf4167CoversExact : CoversExact 8
    leaf4167Box leaf4167Certificate leaf4167InnerLog leaf4167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi274RoundedFacts
    innerPair265RoundedFacts leaf4167RoundedFacts (by rfl)

private theorem leaf4167FlatSound : Sound leaf4167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4167CertificateValid
    leaf4167InnerLogValid leaf4167CoversExact leaf4167LowerChecked

private noncomputable def leaf4168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (15/32), chiHi := (61/128) }

private noncomputable def leaf4168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217937/134217728) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726164992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (303257313/268435456) }, upper := { exponent := 1, mantissa := (1183/1024) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi271LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452624213/11452329984) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf4168InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf4168LocalValidity :
    LeafFacts leaf4168Box leaf4168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726164992) }) = true
      norm_num [leaf4168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4168CertificateValid :
    WideCertificateValid leaf4168Box leaf4168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi271ValidityFacts
    leaf4168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4168CoverageChecked :
    coverageCheck (innerAD leaf4168Box) leaf4168InnerLog = true := by
  rfl'

private theorem leaf4168InnerLogValid :
    leaf4168InnerLog.Valid 8 (innerAD leaf4168Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf4168CoverageChecked

private noncomputable def leaf4168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453689/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4168InputLogOnePlusV_eq :
    leaf4168InputLogOnePlusV = outerEnclosure 24
      (leaf4168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4168RoundedFacts : LeafRoundedFacts 8
    leaf4168Certificate.logOnePlusV leaf4168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4168InputLogOnePlusV_eq }

private noncomputable def leaf4168Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi271InputQChi innerPair264Input
    leaf4168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4168LowerChecked :
    lowerCheck 24 leaf4168Box leaf4168Inputs = true := by
  rfl'

private theorem leaf4168CoversExact : CoversExact 8
    leaf4168Box leaf4168Certificate leaf4168InnerLog leaf4168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi271RoundedFacts
    innerPair264RoundedFacts leaf4168RoundedFacts (by rfl)

private theorem leaf4168FlatSound : Sound leaf4168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4168CertificateValid
    leaf4168InnerLogValid leaf4168CoversExact leaf4168LowerChecked

private noncomputable def leaf4169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (61/128), chiHi := (31/64) }

private noncomputable def leaf4169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217939/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178472448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (306075187/268435456) }, upper := { exponent := 1, mantissa := (597/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi272LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357850111/34356944896) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf4169InnerLog : WideLogData :=
  innerPair560Data

set_option maxRecDepth 1000000 in
private theorem leaf4169LocalValidity :
    LeafFacts leaf4169Box leaf4169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178472448) }) = true
      norm_num [leaf4169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4169CertificateValid :
    WideCertificateValid leaf4169Box leaf4169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi272ValidityFacts
    leaf4169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4169CoverageChecked :
    coverageCheck (innerAD leaf4169Box) leaf4169InnerLog = true := by
  rfl'

private theorem leaf4169InnerLogValid :
    leaf4169InnerLog.Valid 8 (innerAD leaf4169Box) :=
  wideLogDataValid_of_cachedCheck endpoint292PositiveFacts
    endpoint297PositiveFacts.valid leaf4169CoverageChecked

private noncomputable def leaf4169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4169InputLogOnePlusV_eq :
    leaf4169InputLogOnePlusV = outerEnclosure 24
      (leaf4169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4169RoundedFacts : LeafRoundedFacts 8
    leaf4169Certificate.logOnePlusV leaf4169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4169InputLogOnePlusV_eq }

private noncomputable def leaf4169Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi272InputQChi innerPair560Input
    leaf4169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4169LowerChecked :
    lowerCheck 24 leaf4169Box leaf4169Inputs = true := by
  rfl'

private theorem leaf4169CoversExact : CoversExact 8
    leaf4169Box leaf4169Certificate leaf4169InnerLog leaf4169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi272RoundedFacts
    innerPair560RoundedFacts leaf4169RoundedFacts (by rfl)

private theorem leaf4169FlatSound : Sound leaf4169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4169CertificateValid
    leaf4169InnerLogValid leaf4169CoversExact leaf4169LowerChecked

private noncomputable def leaf4170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (31/64), chiHi := (63/128) }

private noncomputable def leaf4170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178449920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (308893061/268435456) }, upper := { exponent := 1, mantissa := (1205/1024) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi273LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357827583/34356899840) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf4170InnerLog : WideLogData :=
  innerPair573Data

set_option maxRecDepth 1000000 in
private theorem leaf4170LocalValidity :
    LeafFacts leaf4170Box leaf4170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178449920) }) = true
      norm_num [leaf4170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4170CertificateValid :
    WideCertificateValid leaf4170Box leaf4170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi273ValidityFacts
    leaf4170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4170CoverageChecked :
    coverageCheck (innerAD leaf4170Box) leaf4170InnerLog = true := by
  rfl'

private theorem leaf4170InnerLogValid :
    leaf4170InnerLog.Valid 8 (innerAD leaf4170Box) :=
  wideLogDataValid_of_cachedCheck endpoint298PositiveFacts
    endpoint299PositiveFacts.valid leaf4170CoverageChecked

private noncomputable def leaf4170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4170InputLogOnePlusV_eq :
    leaf4170InputLogOnePlusV = outerEnclosure 24
      (leaf4170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4170RoundedFacts : LeafRoundedFacts 8
    leaf4170Certificate.logOnePlusV leaf4170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4170InputLogOnePlusV_eq }

private noncomputable def leaf4170Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi273InputQChi innerPair573Input
    leaf4170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4170LowerChecked :
    lowerCheck 24 leaf4170Box leaf4170Inputs = true := by
  rfl'

private theorem leaf4170CoversExact : CoversExact 8
    leaf4170Box leaf4170Certificate leaf4170InnerLog leaf4170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi273RoundedFacts
    innerPair573RoundedFacts leaf4170RoundedFacts (by rfl)

private theorem leaf4170FlatSound : Sound leaf4170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4170CertificateValid
    leaf4170InnerLogValid leaf4170CoversExact leaf4170LowerChecked

private noncomputable def leaf4171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (63/128), chiHi := (1/2) }

private noncomputable def leaf4171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (818065603/818020352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (311710935/268435456) }, upper := { exponent := 1, mantissa := (19/16) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi274LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1636085955/1636040704) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf4171InnerLog : WideLogData :=
  innerPair272Data

set_option maxRecDepth 1000000 in
private theorem leaf4171LocalValidity :
    LeafFacts leaf4171Box leaf4171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (818065603/818020352) }) = true
      norm_num [leaf4171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4171CertificateValid :
    WideCertificateValid leaf4171Box leaf4171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi274ValidityFacts
    leaf4171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4171CoverageChecked :
    coverageCheck (innerAD leaf4171Box) leaf4171InnerLog = true := by
  rfl'

private theorem leaf4171InnerLogValid :
    leaf4171InnerLog.Valid 8 (innerAD leaf4171Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint77PositiveFacts.valid leaf4171CoverageChecked

private noncomputable def leaf4171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629545/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4171InputLogOnePlusV_eq :
    leaf4171InputLogOnePlusV = outerEnclosure 24
      (leaf4171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4171RoundedFacts : LeafRoundedFacts 8
    leaf4171Certificate.logOnePlusV leaf4171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4171InputLogOnePlusV_eq }

private noncomputable def leaf4171Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi274InputQChi innerPair272Input
    leaf4171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4171LowerChecked :
    lowerCheck 24 leaf4171Box leaf4171Inputs = true := by
  rfl'

private theorem leaf4171CoversExact : CoversExact 8
    leaf4171Box leaf4171Certificate leaf4171InnerLog leaf4171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi274RoundedFacts
    innerPair272RoundedFacts leaf4171RoundedFacts (by rfl)

private theorem leaf4171FlatSound : Sound leaf4171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4171CertificateValid
    leaf4171InnerLogValid leaf4171CoversExact leaf4171LowerChecked

private noncomputable def component85Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node0_sound : Sound component85Node0Box :=
  sound_of_literal_split component85Node0Box leaf4135Box leaf4136Box
    .k (81/32) (by rfl) (by rfl)
    leaf4135FlatSound leaf4136FlatSound

private noncomputable def component85Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node1_sound : Sound component85Node1Box :=
  sound_of_literal_split component85Node1Box leaf4137Box leaf4138Box
    .k (81/32) (by rfl) (by rfl)
    leaf4137FlatSound leaf4138FlatSound

private noncomputable def component85Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node2_sound : Sound component85Node2Box :=
  sound_of_literal_split component85Node2Box component85Node0Box component85Node1Box
    .chi (29/64) (by rfl) (by rfl)
    component85Node0_sound component85Node1_sound

private noncomputable def component85Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node3_sound : Sound component85Node3Box :=
  sound_of_literal_split component85Node3Box leaf4139Box leaf4140Box
    .k (83/32) (by rfl) (by rfl)
    leaf4139FlatSound leaf4140FlatSound

private noncomputable def component85Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node4_sound : Sound component85Node4Box :=
  sound_of_literal_split component85Node4Box leaf4141Box leaf4142Box
    .k (83/32) (by rfl) (by rfl)
    leaf4141FlatSound leaf4142FlatSound

private noncomputable def component85Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node5_sound : Sound component85Node5Box :=
  sound_of_literal_split component85Node5Box component85Node3Box component85Node4Box
    .chi (29/64) (by rfl) (by rfl)
    component85Node3_sound component85Node4_sound

private noncomputable def component85Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node6_sound : Sound component85Node6Box :=
  sound_of_literal_split component85Node6Box component85Node2Box component85Node5Box
    .k (41/16) (by rfl) (by rfl)
    component85Node2_sound component85Node5_sound

private noncomputable def component85Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node7_sound : Sound component85Node7Box :=
  sound_of_literal_split component85Node7Box leaf4143Box leaf4144Box
    .k (81/32) (by rfl) (by rfl)
    leaf4143FlatSound leaf4144FlatSound

private noncomputable def component85Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node8_sound : Sound component85Node8Box :=
  sound_of_literal_split component85Node8Box leaf4145Box leaf4146Box
    .k (81/32) (by rfl) (by rfl)
    leaf4145FlatSound leaf4146FlatSound

private noncomputable def component85Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node9_sound : Sound component85Node9Box :=
  sound_of_literal_split component85Node9Box component85Node7Box component85Node8Box
    .chi (31/64) (by rfl) (by rfl)
    component85Node7_sound component85Node8_sound

private noncomputable def component85Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node10_sound : Sound component85Node10Box :=
  sound_of_literal_split component85Node10Box leaf4147Box leaf4148Box
    .k (83/32) (by rfl) (by rfl)
    leaf4147FlatSound leaf4148FlatSound

private noncomputable def component85Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node11_sound : Sound component85Node11Box :=
  sound_of_literal_split component85Node11Box leaf4149Box leaf4150Box
    .k (83/32) (by rfl) (by rfl)
    leaf4149FlatSound leaf4150FlatSound

private noncomputable def component85Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node12_sound : Sound component85Node12Box :=
  sound_of_literal_split component85Node12Box component85Node10Box component85Node11Box
    .chi (31/64) (by rfl) (by rfl)
    component85Node10_sound component85Node11_sound

private noncomputable def component85Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node13_sound : Sound component85Node13Box :=
  sound_of_literal_split component85Node13Box component85Node9Box component85Node12Box
    .k (41/16) (by rfl) (by rfl)
    component85Node9_sound component85Node12_sound

private noncomputable def component85Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node14_sound : Sound component85Node14Box :=
  sound_of_literal_split component85Node14Box component85Node6Box component85Node13Box
    .chi (15/32) (by rfl) (by rfl)
    component85Node6_sound component85Node13_sound

private noncomputable def component85Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component85Node15_sound : Sound component85Node15Box :=
  sound_of_literal_split component85Node15Box leaf4151Box leaf4152Box
    .k (85/32) (by rfl) (by rfl)
    leaf4151FlatSound leaf4152FlatSound

private noncomputable def component85Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node16_sound : Sound component85Node16Box :=
  sound_of_literal_split component85Node16Box leaf4153Box leaf4154Box
    .k (85/32) (by rfl) (by rfl)
    leaf4153FlatSound leaf4154FlatSound

private noncomputable def component85Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node17_sound : Sound component85Node17Box :=
  sound_of_literal_split component85Node17Box component85Node15Box component85Node16Box
    .chi (57/128) (by rfl) (by rfl)
    component85Node15_sound component85Node16_sound

private noncomputable def component85Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node18_sound : Sound component85Node18Box :=
  sound_of_literal_split component85Node18Box leaf4155Box leaf4156Box
    .chi (59/128) (by rfl) (by rfl)
    leaf4155FlatSound leaf4156FlatSound

private noncomputable def component85Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node19_sound : Sound component85Node19Box :=
  sound_of_literal_split component85Node19Box component85Node17Box component85Node18Box
    .chi (29/64) (by rfl) (by rfl)
    component85Node17_sound component85Node18_sound

private noncomputable def component85Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/16), chiHi := (57/128) }

set_option maxRecDepth 1000000 in
private theorem component85Node20_sound : Sound component85Node20Box :=
  sound_of_literal_split component85Node20Box leaf4157Box leaf4158Box
    .k (87/32) (by rfl) (by rfl)
    leaf4157FlatSound leaf4158FlatSound

private noncomputable def component85Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (57/128), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node21_sound : Sound component85Node21Box :=
  sound_of_literal_split component85Node21Box leaf4159Box leaf4160Box
    .k (87/32) (by rfl) (by rfl)
    leaf4159FlatSound leaf4160FlatSound

private noncomputable def component85Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/16), chiHi := (29/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node22_sound : Sound component85Node22Box :=
  sound_of_literal_split component85Node22Box component85Node20Box component85Node21Box
    .chi (57/128) (by rfl) (by rfl)
    component85Node20_sound component85Node21_sound

private noncomputable def component85Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (29/64), chiHi := (59/128) }

set_option maxRecDepth 1000000 in
private theorem component85Node23_sound : Sound component85Node23Box :=
  sound_of_literal_split component85Node23Box leaf4161Box leaf4162Box
    .k (87/32) (by rfl) (by rfl)
    leaf4161FlatSound leaf4162FlatSound

private noncomputable def component85Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (29/64), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node24_sound : Sound component85Node24Box :=
  sound_of_literal_split component85Node24Box component85Node23Box leaf4163Box
    .chi (59/128) (by rfl) (by rfl)
    component85Node23_sound leaf4163FlatSound

private noncomputable def component85Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node25_sound : Sound component85Node25Box :=
  sound_of_literal_split component85Node25Box component85Node22Box component85Node24Box
    .chi (29/64) (by rfl) (by rfl)
    component85Node22_sound component85Node24_sound

private noncomputable def component85Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (7/16), chiHi := (15/32) }

set_option maxRecDepth 1000000 in
private theorem component85Node26_sound : Sound component85Node26Box :=
  sound_of_literal_split component85Node26Box component85Node19Box component85Node25Box
    .k (43/16) (by rfl) (by rfl)
    component85Node19_sound component85Node25_sound

private noncomputable def component85Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node27_sound : Sound component85Node27Box :=
  sound_of_literal_split component85Node27Box leaf4164Box leaf4165Box
    .chi (61/128) (by rfl) (by rfl)
    leaf4164FlatSound leaf4165FlatSound

private noncomputable def component85Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node28_sound : Sound component85Node28Box :=
  sound_of_literal_split component85Node28Box leaf4166Box leaf4167Box
    .chi (63/128) (by rfl) (by rfl)
    leaf4166FlatSound leaf4167FlatSound

private noncomputable def component85Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node29_sound : Sound component85Node29Box :=
  sound_of_literal_split component85Node29Box component85Node27Box component85Node28Box
    .chi (31/64) (by rfl) (by rfl)
    component85Node27_sound component85Node28_sound

private noncomputable def component85Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (15/32), chiHi := (31/64) }

set_option maxRecDepth 1000000 in
private theorem component85Node30_sound : Sound component85Node30Box :=
  sound_of_literal_split component85Node30Box leaf4168Box leaf4169Box
    .chi (61/128) (by rfl) (by rfl)
    leaf4168FlatSound leaf4169FlatSound

private noncomputable def component85Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (31/64), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node31_sound : Sound component85Node31Box :=
  sound_of_literal_split component85Node31Box leaf4170Box leaf4171Box
    .chi (63/128) (by rfl) (by rfl)
    leaf4170FlatSound leaf4171FlatSound

private noncomputable def component85Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node32_sound : Sound component85Node32Box :=
  sound_of_literal_split component85Node32Box component85Node30Box component85Node31Box
    .chi (31/64) (by rfl) (by rfl)
    component85Node30_sound component85Node31_sound

private noncomputable def component85Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (15/32), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node33_sound : Sound component85Node33Box :=
  sound_of_literal_split component85Node33Box component85Node29Box component85Node32Box
    .k (43/16) (by rfl) (by rfl)
    component85Node29_sound component85Node32_sound

private noncomputable def component85Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component85Node34_sound : Sound component85Node34Box :=
  sound_of_literal_split component85Node34Box component85Node26Box component85Node33Box
    .chi (15/32) (by rfl) (by rfl)
    component85Node26_sound component85Node33_sound

noncomputable def component85Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component85_sound : Sound component85Box :=
  sound_of_literal_split component85Box component85Node14Box component85Node34Box
    .k (21/8) (by rfl) (by rfl)
    component85Node14_sound component85Node34_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
