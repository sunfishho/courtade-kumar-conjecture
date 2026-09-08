import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf5279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871307/536870912) }, vSqrt := { lower := (8191/8192), upper := (2021101327/2021018368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1144974711/1073741824) }, upper := { exponent := 1, mantissa := (17669/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4042119695/4042036736) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5279InnerLog : WideLogData :=
  innerPair635Data

set_option maxRecDepth 1000000 in
private theorem leaf5279LocalValidity :
    LeafFacts leaf5279Box leaf5279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2021101327/2021018368) }) = true
      norm_num [leaf5279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5279CertificateValid :
    WideCertificateValid leaf5279Box leaf5279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi289ValidityFacts
    leaf5279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5279CoverageChecked :
    coverageCheck (innerAD leaf5279Box) leaf5279InnerLog = true := by
  rfl'

private theorem leaf5279InnerLogValid :
    leaf5279InnerLog.Valid 8 (innerAD leaf5279Box) :=
  wideLogDataValid_of_cachedCheck endpoint368PositiveFacts
    endpoint369PositiveFacts.valid leaf5279CoverageChecked

private noncomputable def leaf5279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5279InputLogOnePlusV_eq :
    leaf5279InputLogOnePlusV = outerEnclosure 24
      (leaf5279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5279RoundedFacts : LeafRoundedFacts 8
    leaf5279Certificate.logOnePlusV leaf5279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5279InputLogOnePlusV_eq }

private noncomputable def leaf5279Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi289InputQChi innerPair635Input
    leaf5279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5279LowerChecked :
    lowerCheck 24 leaf5279Box leaf5279Inputs = true := by
  rfl'

private theorem leaf5279CoversExact : CoversExact 8
    leaf5279Box leaf5279Certificate leaf5279InnerLog leaf5279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi289RoundedFacts
    innerPair635RoundedFacts leaf5279RoundedFacts (by rfl)

private theorem leaf5279FlatSound : Sound leaf5279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5279CertificateValid
    leaf5279InnerLogValid leaf5279CoversExact leaf5279LowerChecked

private noncomputable def leaf5280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871309/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357282304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1152576421/1073741824) }, upper := { exponent := 1, mantissa := (8893/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68716004863/68714564608) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5280InnerLog : WideLogData :=
  innerPair554Data

set_option maxRecDepth 1000000 in
private theorem leaf5280LocalValidity :
    LeafFacts leaf5280Box leaf5280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357282304) }) = true
      norm_num [leaf5280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5280CertificateValid :
    WideCertificateValid leaf5280Box leaf5280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi290ValidityFacts
    leaf5280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5280CoverageChecked :
    coverageCheck (innerAD leaf5280Box) leaf5280InnerLog = true := by
  rfl'

private theorem leaf5280InnerLogValid :
    leaf5280InnerLog.Valid 8 (innerAD leaf5280Box) :=
  wideLogDataValid_of_cachedCheck endpoint289PositiveFacts
    endpoint337PositiveFacts.valid leaf5280CoverageChecked

private noncomputable def leaf5280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5280InputLogOnePlusV_eq :
    leaf5280InputLogOnePlusV = outerEnclosure 24
      (leaf5280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5280RoundedFacts : LeafRoundedFacts 8
    leaf5280Certificate.logOnePlusV leaf5280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5280InputLogOnePlusV_eq }

private noncomputable def leaf5280Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi290InputQChi innerPair554Input
    leaf5280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5280LowerChecked :
    lowerCheck 24 leaf5280Box leaf5280Inputs = true := by
  rfl'

private theorem leaf5280CoversExact : CoversExact 8
    leaf5280Box leaf5280Certificate leaf5280InnerLog leaf5280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi290RoundedFacts
    innerPair554RoundedFacts leaf5280RoundedFacts (by rfl)

private theorem leaf5280FlatSound : Sound leaf5280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5280CertificateValid
    leaf5280InnerLogValid leaf5280CoversExact leaf5280LowerChecked

private noncomputable def leaf5281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816371968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2300467467/2147483648) }, upper := { exponent := 1, mantissa := (35419/32768) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633145161/19632743936) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf5281InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5281LocalValidity :
    LeafFacts leaf5281Box leaf5281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816371968) }) = true
      norm_num [leaf5281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5281CertificateValid :
    WideCertificateValid leaf5281Box leaf5281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi289ValidityFacts
    leaf5281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5281CoverageChecked :
    coverageCheck (innerAD leaf5281Box) leaf5281InnerLog = true := by
  rfl'

private theorem leaf5281InnerLogValid :
    leaf5281InnerLog.Valid 8 (innerAD leaf5281Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5281CoverageChecked

private noncomputable def leaf5281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf5281InputLogOnePlusV_eq :
    leaf5281InputLogOnePlusV = outerEnclosure 24
      (leaf5281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5281RoundedFacts : LeafRoundedFacts 8
    leaf5281Certificate.logOnePlusV leaf5281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5281InputLogOnePlusV_eq }

private noncomputable def leaf5281Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi289InputQChi innerPair249Input
    leaf5281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5281LowerChecked :
    lowerCheck 24 leaf5281Box leaf5281Inputs = true := by
  rfl'

private theorem leaf5281CoversExact : CoversExact 8
    leaf5281Box leaf5281Certificate leaf5281InnerLog leaf5281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi289RoundedFacts
    innerPair249RoundedFacts leaf5281RoundedFacts (by rfl)

private theorem leaf5281FlatSound : Sound leaf5281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5281CertificateValid
    leaf5281InnerLogValid leaf5281CoversExact leaf5281LowerChecked

private noncomputable def leaf5282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714583040) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2305710025/2147483648) }, upper := { exponent := 1, mantissa := (8875/8192) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431995391/137429166080) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf5282InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5282LocalValidity :
    LeafFacts leaf5282Box leaf5282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714583040) }) = true
      norm_num [leaf5282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5282CertificateValid :
    WideCertificateValid leaf5282Box leaf5282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi289ValidityFacts
    leaf5282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5282CoverageChecked :
    coverageCheck (innerAD leaf5282Box) leaf5282InnerLog = true := by
  rfl'

private theorem leaf5282InnerLogValid :
    leaf5282InnerLog.Valid 8 (innerAD leaf5282Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5282CoverageChecked

private noncomputable def leaf5282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5282InputLogOnePlusV_eq :
    leaf5282InputLogOnePlusV = outerEnclosure 24
      (leaf5282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5282RoundedFacts : LeafRoundedFacts 8
    leaf5282Certificate.logOnePlusV leaf5282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5282InputLogOnePlusV_eq }

private noncomputable def leaf5282Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi289InputQChi innerPair249Input
    leaf5282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5282LowerChecked :
    lowerCheck 24 leaf5282Box leaf5282Inputs = true := by
  rfl'

private theorem leaf5282CoversExact : CoversExact 8
    leaf5282Box leaf5282Certificate leaf5282InnerLog leaf5282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi289RoundedFacts
    innerPair249RoundedFacts leaf5282RoundedFacts (by rfl)

private theorem leaf5282FlatSound : Sound leaf5282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5282CertificateValid
    leaf5282InnerLogValid leaf5282CoversExact leaf5282LowerChecked

private noncomputable def leaf5283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (8191/8192), upper := (1108345889/1108298752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1157884511/1073741824) }, upper := { exponent := 1, mantissa := (4467/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2216644641/2216597504) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5283InnerLog : WideLogData :=
  innerPair333Data

set_option maxRecDepth 1000000 in
private theorem leaf5283LocalValidity :
    LeafFacts leaf5283Box leaf5283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1108345889/1108298752) }) = true
      norm_num [leaf5283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5283CertificateValid :
    WideCertificateValid leaf5283Box leaf5283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi290ValidityFacts
    leaf5283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5283CoverageChecked :
    coverageCheck (innerAD leaf5283Box) leaf5283InnerLog = true := by
  rfl'

private theorem leaf5283InnerLogValid :
    leaf5283InnerLog.Valid 8 (innerAD leaf5283Box) :=
  wideLogDataValid_of_cachedCheck endpoint88PositiveFacts
    endpoint370PositiveFacts.valid leaf5283CoverageChecked

private noncomputable def leaf5283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5283InputLogOnePlusV_eq :
    leaf5283InputLogOnePlusV = outerEnclosure 24
      (leaf5283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5283RoundedFacts : LeafRoundedFacts 8
    leaf5283Certificate.logOnePlusV leaf5283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5283InputLogOnePlusV_eq }

private noncomputable def leaf5283Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi290InputQChi innerPair333Input
    leaf5283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5283LowerChecked :
    lowerCheck 24 leaf5283Box leaf5283Inputs = true := by
  rfl'

private theorem leaf5283CoversExact : CoversExact 8
    leaf5283Box leaf5283Certificate leaf5283InnerLog leaf5283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi290RoundedFacts
    innerPair333RoundedFacts leaf5283RoundedFacts (by rfl)

private theorem leaf5283FlatSound : Sound leaf5283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5283CertificateValid
    leaf5283InnerLogValid leaf5283CoversExact leaf5283LowerChecked

private noncomputable def leaf5284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871311/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357252352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1160178131/1073741824) }, upper := { exponent := 1, mantissa := (17903/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715974911/68714504704) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5284InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5284LocalValidity :
    LeafFacts leaf5284Box leaf5284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357252352) }) = true
      norm_num [leaf5284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5284CertificateValid :
    WideCertificateValid leaf5284Box leaf5284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi291ValidityFacts
    leaf5284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5284CoverageChecked :
    coverageCheck (innerAD leaf5284Box) leaf5284InnerLog = true := by
  rfl'

private theorem leaf5284InnerLogValid :
    leaf5284InnerLog.Valid 8 (innerAD leaf5284Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5284CoverageChecked

private noncomputable def leaf5284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf5284InputLogOnePlusV_eq :
    leaf5284InputLogOnePlusV = outerEnclosure 24
      (leaf5284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5284RoundedFacts : LeafRoundedFacts 8
    leaf5284Certificate.logOnePlusV leaf5284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5284InputLogOnePlusV_eq }

private noncomputable def leaf5284Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi291InputQChi innerPair249Input
    leaf5284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5284LowerChecked :
    lowerCheck 24 leaf5284Box leaf5284Inputs = true := by
  rfl'

private theorem leaf5284CoversExact : CoversExact 8
    leaf5284Box leaf5284Certificate leaf5284InnerLog leaf5284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi291RoundedFacts
    innerPair249RoundedFacts leaf5284RoundedFacts (by rfl)

private theorem leaf5284FlatSound : Sound leaf5284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5284CertificateValid
    leaf5284InnerLogValid leaf5284CoversExact leaf5284LowerChecked

private noncomputable def leaf5285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357222400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1167779841/1073741824) }, upper := { exponent := 1, mantissa := (4505/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715944959/68714444800) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5285InnerLog : WideLogData :=
  innerPair612Data

set_option maxRecDepth 1000000 in
private theorem leaf5285LocalValidity :
    LeafFacts leaf5285Box leaf5285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357222400) }) = true
      norm_num [leaf5285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5285CertificateValid :
    WideCertificateValid leaf5285Box leaf5285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi292ValidityFacts
    leaf5285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5285CoverageChecked :
    coverageCheck (innerAD leaf5285Box) leaf5285InnerLog = true := by
  rfl'

private theorem leaf5285InnerLogValid :
    leaf5285InnerLog.Valid 8 (innerAD leaf5285Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint291PositiveFacts.valid leaf5285CoverageChecked

private noncomputable def leaf5285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5285InputLogOnePlusV_eq :
    leaf5285InputLogOnePlusV = outerEnclosure 24
      (leaf5285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5285RoundedFacts : LeafRoundedFacts 8
    leaf5285Certificate.logOnePlusV leaf5285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5285InputLogOnePlusV_eq }

private noncomputable def leaf5285Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi292InputQChi innerPair612Input
    leaf5285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5285LowerChecked :
    lowerCheck 24 leaf5285Box leaf5285Inputs = true := by
  rfl'

private theorem leaf5285CoversExact : CoversExact 8
    leaf5285Box leaf5285Certificate leaf5285InnerLog leaf5285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi292RoundedFacts
    innerPair612RoundedFacts leaf5285RoundedFacts (by rfl)

private theorem leaf5285FlatSound : Sound leaf5285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5285CertificateValid
    leaf5285InnerLogValid leaf5285CoversExact leaf5285LowerChecked

private noncomputable def leaf5286Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5286Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871313/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908175872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1165551753/1073741824) }, upper := { exponent := 1, mantissa := (8993/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816564809/9816351744) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5286InnerLog : WideLogData :=
  innerPair636Data

set_option maxRecDepth 1000000 in
private theorem leaf5286LocalValidity :
    LeafFacts leaf5286Box leaf5286Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5286Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908175872) }) = true
      norm_num [leaf5286Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5286CertificateValid :
    WideCertificateValid leaf5286Box leaf5286Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi291ValidityFacts
    leaf5286LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5286CoverageChecked :
    coverageCheck (innerAD leaf5286Box) leaf5286InnerLog = true := by
  rfl'

private theorem leaf5286InnerLogValid :
    leaf5286InnerLog.Valid 8 (innerAD leaf5286Box) :=
  wideLogDataValid_of_cachedCheck endpoint371PositiveFacts
    endpoint372PositiveFacts.valid leaf5286CoverageChecked

private noncomputable def leaf5286InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5286InputLogOnePlusV_eq :
    leaf5286InputLogOnePlusV = outerEnclosure 24
      (leaf5286Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5286RoundedFacts : LeafRoundedFacts 8
    leaf5286Certificate.logOnePlusV leaf5286InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5286InputLogOnePlusV_eq }

private noncomputable def leaf5286Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi291InputQChi innerPair636Input
    leaf5286InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5286LowerChecked :
    lowerCheck 24 leaf5286Box leaf5286Inputs = true := by
  rfl'

private theorem leaf5286CoversExact : CoversExact 8
    leaf5286Box leaf5286Certificate leaf5286InnerLog leaf5286Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi291RoundedFacts
    innerPair636RoundedFacts leaf5286RoundedFacts (by rfl)

private theorem leaf5286FlatSound : Sound leaf5286Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5286CertificateValid
    leaf5286InnerLogValid leaf5286CoversExact leaf5286LowerChecked

private noncomputable def leaf5287Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5287Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357200896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1173218995/1073741824) }, upper := { exponent := 1, mantissa := (2263/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715923455/68714401792) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5287InnerLog : WideLogData :=
  innerPair638Data

set_option maxRecDepth 1000000 in
private theorem leaf5287LocalValidity :
    LeafFacts leaf5287Box leaf5287Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5287Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357200896) }) = true
      norm_num [leaf5287Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5287CertificateValid :
    WideCertificateValid leaf5287Box leaf5287Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi292ValidityFacts
    leaf5287LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5287CoverageChecked :
    coverageCheck (innerAD leaf5287Box) leaf5287InnerLog = true := by
  rfl'

private theorem leaf5287InnerLogValid :
    leaf5287InnerLog.Valid 8 (innerAD leaf5287Box) :=
  wideLogDataValid_of_cachedCheck endpoint373PositiveFacts
    endpoint374PositiveFacts.valid leaf5287CoverageChecked

private noncomputable def leaf5287InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5287InputLogOnePlusV_eq :
    leaf5287InputLogOnePlusV = outerEnclosure 24
      (leaf5287Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5287RoundedFacts : LeafRoundedFacts 8
    leaf5287Certificate.logOnePlusV leaf5287InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5287InputLogOnePlusV_eq }

private noncomputable def leaf5287Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi292InputQChi innerPair638Input
    leaf5287InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5287LowerChecked :
    lowerCheck 24 leaf5287Box leaf5287Inputs = true := by
  rfl'

private theorem leaf5287CoversExact : CoversExact 8
    leaf5287Box leaf5287Certificate leaf5287InnerLog leaf5287Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi292RoundedFacts
    innerPair638RoundedFacts leaf5287RoundedFacts (by rfl)

private theorem leaf5287FlatSound : Sound leaf5287Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5287CertificateValid
    leaf5287InnerLogValid leaf5287CoversExact leaf5287LowerChecked

private noncomputable def leaf5288Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5288Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2216690721/2216598784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2310952583/2147483648) }, upper := { exponent := 1, mantissa := (35581/32768) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4433289505/4433197568) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf5288InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5288LocalValidity :
    LeafFacts leaf5288Box leaf5288Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5288Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2216690721/2216598784) }) = true
      norm_num [leaf5288Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5288CertificateValid :
    WideCertificateValid leaf5288Box leaf5288Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi289ValidityFacts
    leaf5288LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5288CoverageChecked :
    coverageCheck (innerAD leaf5288Box) leaf5288InnerLog = true := by
  rfl'

private theorem leaf5288InnerLogValid :
    leaf5288InnerLog.Valid 8 (innerAD leaf5288Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5288CoverageChecked

private noncomputable def leaf5288InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5288InputLogOnePlusV_eq :
    leaf5288InputLogOnePlusV = outerEnclosure 24
      (leaf5288Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5288RoundedFacts : LeafRoundedFacts 8
    leaf5288Certificate.logOnePlusV leaf5288InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5288InputLogOnePlusV_eq }

private noncomputable def leaf5288Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi289InputQChi innerPair249Input
    leaf5288InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5288LowerChecked :
    lowerCheck 24 leaf5288Box leaf5288Inputs = true := by
  rfl'

private theorem leaf5288CoversExact : CoversExact 8
    leaf5288Box leaf5288Certificate leaf5288InnerLog leaf5288Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi289RoundedFacts
    innerPair249RoundedFacts leaf5288RoundedFacts (by rfl)

private theorem leaf5288FlatSound : Sound leaf5288Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5288CertificateValid
    leaf5288InnerLogValid leaf5288CoversExact leaf5288LowerChecked

private noncomputable def leaf5289Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5289Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714541568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2316195141/2147483648) }, upper := { exponent := 1, mantissa := (17831/16384) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431953919/137429083136) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf5289InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5289LocalValidity :
    LeafFacts leaf5289Box leaf5289Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5289Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714541568) }) = true
      norm_num [leaf5289Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5289CertificateValid :
    WideCertificateValid leaf5289Box leaf5289Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi289ValidityFacts
    leaf5289LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5289CoverageChecked :
    coverageCheck (innerAD leaf5289Box) leaf5289InnerLog = true := by
  rfl'

private theorem leaf5289InnerLogValid :
    leaf5289InnerLog.Valid 8 (innerAD leaf5289Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5289CoverageChecked

private noncomputable def leaf5289InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5289InputLogOnePlusV_eq :
    leaf5289InputLogOnePlusV = outerEnclosure 24
      (leaf5289Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5289RoundedFacts : LeafRoundedFacts 8
    leaf5289Certificate.logOnePlusV leaf5289InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5289InputLogOnePlusV_eq }

private noncomputable def leaf5289Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi289InputQChi innerPair249Input
    leaf5289InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5289LowerChecked :
    lowerCheck 24 leaf5289Box leaf5289Inputs = true := by
  rfl'

private theorem leaf5289CoversExact : CoversExact 8
    leaf5289Box leaf5289Certificate leaf5289InnerLog leaf5289Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi289RoundedFacts
    innerPair249RoundedFacts leaf5289RoundedFacts (by rfl)

private theorem leaf5289FlatSound : Sound leaf5289Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5289CertificateValid
    leaf5289InnerLogValid leaf5289CoversExact leaf5289LowerChecked

private noncomputable def leaf5290Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5290Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816357376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2326418133/2147483648) }, upper := { exponent := 1, mantissa := (17909/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633130569/19632714752) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf5290InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5290LocalValidity :
    LeafFacts leaf5290Box leaf5290Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5290Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816357376) }) = true
      norm_num [leaf5290Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5290CertificateValid :
    WideCertificateValid leaf5290Box leaf5290Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi290ValidityFacts
    leaf5290LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5290CoverageChecked :
    coverageCheck (innerAD leaf5290Box) leaf5290InnerLog = true := by
  rfl'

private theorem leaf5290InnerLogValid :
    leaf5290InnerLog.Valid 8 (innerAD leaf5290Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5290CoverageChecked

private noncomputable def leaf5290InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5290InputLogOnePlusV_eq :
    leaf5290InputLogOnePlusV = outerEnclosure 24
      (leaf5290Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5290RoundedFacts : LeafRoundedFacts 8
    leaf5290Certificate.logOnePlusV leaf5290InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5290InputLogOnePlusV_eq }

private noncomputable def leaf5290Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi290InputQChi innerPair249Input
    leaf5290InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5290LowerChecked :
    lowerCheck 24 leaf5290Box leaf5290Inputs = true := by
  rfl'

private theorem leaf5290CoversExact : CoversExact 8
    leaf5290Box leaf5290Certificate leaf5290InnerLog leaf5290Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi290RoundedFacts
    innerPair249RoundedFacts leaf5290RoundedFacts (by rfl)

private theorem leaf5290FlatSound : Sound leaf5290Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5290CertificateValid
    leaf5290InnerLogValid leaf5290CoversExact leaf5290LowerChecked

private noncomputable def leaf5291Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5291Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904826880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2331726223/2147483648) }, upper := { exponent := 1, mantissa := (8975/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810630997/45809653760) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf5291InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5291LocalValidity :
    LeafFacts leaf5291Box leaf5291Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5291Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904826880) }) = true
      norm_num [leaf5291Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5291CertificateValid :
    WideCertificateValid leaf5291Box leaf5291Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi290ValidityFacts
    leaf5291LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5291CoverageChecked :
    coverageCheck (innerAD leaf5291Box) leaf5291InnerLog = true := by
  rfl'

private theorem leaf5291InnerLogValid :
    leaf5291InnerLog.Valid 8 (innerAD leaf5291Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5291CoverageChecked

private noncomputable def leaf5291InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5291InputLogOnePlusV_eq :
    leaf5291InputLogOnePlusV = outerEnclosure 24
      (leaf5291Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5291RoundedFacts : LeafRoundedFacts 8
    leaf5291Certificate.logOnePlusV leaf5291InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5291InputLogOnePlusV_eq }

private noncomputable def leaf5291Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi290InputQChi innerPair250Input
    leaf5291InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5291LowerChecked :
    lowerCheck 24 leaf5291Box leaf5291Inputs = true := by
  rfl'

private theorem leaf5291CoversExact : CoversExact 8
    leaf5291Box leaf5291Certificate leaf5291InnerLog leaf5291Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi290RoundedFacts
    innerPair250RoundedFacts leaf5291RoundedFacts (by rfl)

private theorem leaf5291FlatSound : Sound leaf5291Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5291CertificateValid
    leaf5291InnerLogValid leaf5291CoversExact leaf5291LowerChecked

private noncomputable def leaf5292Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5292Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714520832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2321437699/2147483648) }, upper := { exponent := 1, mantissa := (35743/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431933183/137429041664) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf5292InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5292LocalValidity :
    LeafFacts leaf5292Box leaf5292Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5292Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714520832) }) = true
      norm_num [leaf5292Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5292CertificateValid :
    WideCertificateValid leaf5292Box leaf5292Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi289ValidityFacts
    leaf5292LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5292CoverageChecked :
    coverageCheck (innerAD leaf5292Box) leaf5292InnerLog = true := by
  rfl'

private theorem leaf5292InnerLogValid :
    leaf5292InnerLog.Valid 8 (innerAD leaf5292Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5292CoverageChecked

private noncomputable def leaf5292InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5292InputLogOnePlusV_eq :
    leaf5292InputLogOnePlusV = outerEnclosure 24
      (leaf5292Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5292RoundedFacts : LeafRoundedFacts 8
    leaf5292Certificate.logOnePlusV leaf5292InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5292InputLogOnePlusV_eq }

private noncomputable def leaf5292Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi289InputQChi innerPair249Input
    leaf5292InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5292LowerChecked :
    lowerCheck 24 leaf5292Box leaf5292Inputs = true := by
  rfl'

private theorem leaf5292CoversExact : CoversExact 8
    leaf5292Box leaf5292Certificate leaf5292InnerLog leaf5292Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi289RoundedFacts
    innerPair249RoundedFacts leaf5292RoundedFacts (by rfl)

private theorem leaf5292FlatSound : Sound leaf5292Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5292CertificateValid
    leaf5292InnerLogValid leaf5292CoversExact leaf5292LowerChecked

private noncomputable def leaf5293Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (5/16), chiHi := (81/256) }

private noncomputable def leaf5293Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714500096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2326680257/2147483648) }, upper := { exponent := 1, mantissa := (2239/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi289LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431912447/137429000192) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf5293InnerLog : WideLogData :=
  innerPair249Data

set_option maxRecDepth 1000000 in
private theorem leaf5293LocalValidity :
    LeafFacts leaf5293Box leaf5293Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5293Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714500096) }) = true
      norm_num [leaf5293Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5293CertificateValid :
    WideCertificateValid leaf5293Box leaf5293Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi289ValidityFacts
    leaf5293LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5293CoverageChecked :
    coverageCheck (innerAD leaf5293Box) leaf5293InnerLog = true := by
  rfl'

private theorem leaf5293InnerLogValid :
    leaf5293InnerLog.Valid 8 (innerAD leaf5293Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint74PositiveFacts.valid leaf5293CoverageChecked

private noncomputable def leaf5293InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5293InputLogOnePlusV_eq :
    leaf5293InputLogOnePlusV = outerEnclosure 24
      (leaf5293Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5293RoundedFacts : LeafRoundedFacts 8
    leaf5293Certificate.logOnePlusV leaf5293InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5293InputLogOnePlusV_eq }

private noncomputable def leaf5293Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi289InputQChi innerPair249Input
    leaf5293InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5293LowerChecked :
    lowerCheck 24 leaf5293Box leaf5293Inputs = true := by
  rfl'

private theorem leaf5293CoversExact : CoversExact 8
    leaf5293Box leaf5293Certificate leaf5293InnerLog leaf5293Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi289RoundedFacts
    innerPair249RoundedFacts leaf5293RoundedFacts (by rfl)

private theorem leaf5293FlatSound : Sound leaf5293Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5293CertificateValid
    leaf5293InnerLogValid leaf5293CoversExact leaf5293LowerChecked

private noncomputable def leaf5294Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5294Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742465/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714459648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2337034313/2147483648) }, upper := { exponent := 1, mantissa := (17991/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431871999/137428919296) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf5294InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5294LocalValidity :
    LeafFacts leaf5294Box leaf5294Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5294Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714459648) }) = true
      norm_num [leaf5294Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5294CertificateValid :
    WideCertificateValid leaf5294Box leaf5294Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi290ValidityFacts
    leaf5294LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5294CoverageChecked :
    coverageCheck (innerAD leaf5294Box) leaf5294InnerLog = true := by
  rfl'

private theorem leaf5294InnerLogValid :
    leaf5294InnerLog.Valid 8 (innerAD leaf5294Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5294CoverageChecked

private noncomputable def leaf5294InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5294InputLogOnePlusV_eq :
    leaf5294InputLogOnePlusV = outerEnclosure 24
      (leaf5294Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5294RoundedFacts : LeafRoundedFacts 8
    leaf5294Certificate.logOnePlusV leaf5294InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5294InputLogOnePlusV_eq }

private noncomputable def leaf5294Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi290InputQChi innerPair250Input
    leaf5294InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5294LowerChecked :
    lowerCheck 24 leaf5294Box leaf5294Inputs = true := by
  rfl'

private theorem leaf5294CoversExact : CoversExact 8
    leaf5294Box leaf5294Certificate leaf5294InnerLog leaf5294Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi290RoundedFacts
    innerPair250RoundedFacts leaf5294RoundedFacts (by rfl)

private theorem leaf5294FlatSound : Sound leaf5294Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5294CertificateValid
    leaf5294InnerLogValid leaf5294CoversExact leaf5294LowerChecked

private noncomputable def leaf5295Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (81/256), chiHi := (41/128) }

private noncomputable def leaf5295Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714438656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2342342403/2147483648) }, upper := { exponent := 1, mantissa := (1127/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi290LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431851007/137428877312) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf5295InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf5295LocalValidity :
    LeafFacts leaf5295Box leaf5295Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5295Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714438656) }) = true
      norm_num [leaf5295Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5295CertificateValid :
    WideCertificateValid leaf5295Box leaf5295Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi290ValidityFacts
    leaf5295LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5295CoverageChecked :
    coverageCheck (innerAD leaf5295Box) leaf5295InnerLog = true := by
  rfl'

private theorem leaf5295InnerLogValid :
    leaf5295InnerLog.Valid 8 (innerAD leaf5295Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf5295CoverageChecked

private noncomputable def leaf5295InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5295InputLogOnePlusV_eq :
    leaf5295InputLogOnePlusV = outerEnclosure 24
      (leaf5295Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5295RoundedFacts : LeafRoundedFacts 8
    leaf5295Certificate.logOnePlusV leaf5295InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5295InputLogOnePlusV_eq }

private noncomputable def leaf5295Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi290InputQChi innerPair250Input
    leaf5295InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5295LowerChecked :
    lowerCheck 24 leaf5295Box leaf5295Inputs = true := by
  rfl'

private theorem leaf5295CoversExact : CoversExact 8
    leaf5295Box leaf5295Certificate leaf5295InnerLog leaf5295Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi290RoundedFacts
    innerPair250RoundedFacts leaf5295RoundedFacts (by rfl)

private theorem leaf5295FlatSound : Sound leaf5295Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5295CertificateValid
    leaf5295InnerLogValid leaf5295CoversExact leaf5295LowerChecked

private noncomputable def leaf5296Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5296Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357209856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1170925375/1073741824) }, upper := { exponent := 1, mantissa := (18069/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715932415/68714419712) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5296InnerLog : WideLogData :=
  innerPair639Data

set_option maxRecDepth 1000000 in
private theorem leaf5296LocalValidity :
    LeafFacts leaf5296Box leaf5296Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5296Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357209856) }) = true
      norm_num [leaf5296Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5296CertificateValid :
    WideCertificateValid leaf5296Box leaf5296Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi291ValidityFacts
    leaf5296LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5296CoverageChecked :
    coverageCheck (innerAD leaf5296Box) leaf5296InnerLog = true := by
  rfl'

private theorem leaf5296InnerLogValid :
    leaf5296InnerLog.Valid 8 (innerAD leaf5296Box) :=
  wideLogDataValid_of_cachedCheck endpoint375PositiveFacts
    endpoint376PositiveFacts.valid leaf5296CoverageChecked

private noncomputable def leaf5296InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5296InputLogOnePlusV_eq :
    leaf5296InputLogOnePlusV = outerEnclosure 24
      (leaf5296Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5296RoundedFacts : LeafRoundedFacts 8
    leaf5296Certificate.logOnePlusV leaf5296InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5296InputLogOnePlusV_eq }

private noncomputable def leaf5296Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi291InputQChi innerPair639Input
    leaf5296InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5296LowerChecked :
    lowerCheck 24 leaf5296Box leaf5296Inputs = true := by
  rfl'

private theorem leaf5296CoversExact : CoversExact 8
    leaf5296Box leaf5296Certificate leaf5296InnerLog leaf5296Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi291RoundedFacts
    innerPair639RoundedFacts leaf5296RoundedFacts (by rfl)

private theorem leaf5296FlatSound : Sound leaf5296Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5296CertificateValid
    leaf5296InnerLogValid leaf5296CoversExact leaf5296LowerChecked

private noncomputable def leaf5297Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5297Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357179392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1178658149/1073741824) }, upper := { exponent := 1, mantissa := (4547/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715901951/68714358784) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5297InnerLog : WideLogData :=
  innerPair640Data

set_option maxRecDepth 1000000 in
private theorem leaf5297LocalValidity :
    LeafFacts leaf5297Box leaf5297Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5297Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357179392) }) = true
      norm_num [leaf5297Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5297CertificateValid :
    WideCertificateValid leaf5297Box leaf5297Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi292ValidityFacts
    leaf5297LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5297CoverageChecked :
    coverageCheck (innerAD leaf5297Box) leaf5297InnerLog = true := by
  rfl'

private theorem leaf5297InnerLogValid :
    leaf5297InnerLog.Valid 8 (innerAD leaf5297Box) :=
  wideLogDataValid_of_cachedCheck endpoint377PositiveFacts
    endpoint378PositiveFacts.valid leaf5297CoverageChecked

private noncomputable def leaf5297InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814729/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5297InputLogOnePlusV_eq :
    leaf5297InputLogOnePlusV = outerEnclosure 24
      (leaf5297Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5297RoundedFacts : LeafRoundedFacts 8
    leaf5297Certificate.logOnePlusV leaf5297InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5297InputLogOnePlusV_eq }

private noncomputable def leaf5297Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi292InputQChi innerPair640Input
    leaf5297InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5297LowerChecked :
    lowerCheck 24 leaf5297Box leaf5297Inputs = true := by
  rfl'

private theorem leaf5297CoversExact : CoversExact 8
    leaf5297Box leaf5297Certificate leaf5297InnerLog leaf5297Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi292RoundedFacts
    innerPair640RoundedFacts leaf5297RoundedFacts (by rfl)

private theorem leaf5297FlatSound : Sound leaf5297Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5297CertificateValid
    leaf5297InnerLogValid leaf5297CoversExact leaf5297LowerChecked

private noncomputable def leaf5298Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5298Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742467/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22905804117/22904799488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2352630927/2147483648) }, upper := { exponent := 1, mantissa := (36221/32768) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45810603605/45809598976) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf5298InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5298LocalValidity :
    LeafFacts leaf5298Box leaf5298Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5298Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22905804117/22904799488) }) = true
      norm_num [leaf5298Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5298CertificateValid :
    WideCertificateValid leaf5298Box leaf5298Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi291ValidityFacts
    leaf5298LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5298CoverageChecked :
    coverageCheck (innerAD leaf5298Box) leaf5298InnerLog = true := by
  rfl'

private theorem leaf5298InnerLogValid :
    leaf5298InnerLog.Valid 8 (innerAD leaf5298Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5298CoverageChecked

private noncomputable def leaf5298InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5298InputLogOnePlusV_eq :
    leaf5298InputLogOnePlusV = outerEnclosure 24
      (leaf5298Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5298RoundedFacts : LeafRoundedFacts 8
    leaf5298Certificate.logOnePlusV leaf5298InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5298InputLogOnePlusV_eq }

private noncomputable def leaf5298Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5298InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5298LowerChecked :
    lowerCheck 24 leaf5298Box leaf5298Inputs = true := by
  rfl'

private theorem leaf5298CoversExact : CoversExact 8
    leaf5298Box leaf5298Certificate leaf5298InnerLog leaf5298Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5298RoundedFacts (by rfl)

private theorem leaf5298FlatSound : Sound leaf5298Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5298CertificateValid
    leaf5298InnerLogValid leaf5298CoversExact leaf5298LowerChecked

private noncomputable def leaf5299Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (41/128), chiHi := (83/256) }

private noncomputable def leaf5299Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742469/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68714377216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (2358004549/2147483648) }, upper := { exponent := 1, mantissa := (2269/2048) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi291LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137431789567/137428754432) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf5299InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5299LocalValidity :
    LeafFacts leaf5299Box leaf5299Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5299Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68714377216) }) = true
      norm_num [leaf5299Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5299CertificateValid :
    WideCertificateValid leaf5299Box leaf5299Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi291ValidityFacts
    leaf5299LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5299CoverageChecked :
    coverageCheck (innerAD leaf5299Box) leaf5299InnerLog = true := by
  rfl'

private theorem leaf5299InnerLogValid :
    leaf5299InnerLog.Valid 8 (innerAD leaf5299Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5299CoverageChecked

private noncomputable def leaf5299InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5299InputLogOnePlusV_eq :
    leaf5299InputLogOnePlusV = outerEnclosure 24
      (leaf5299Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5299RoundedFacts : LeafRoundedFacts 8
    leaf5299Certificate.logOnePlusV leaf5299InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5299InputLogOnePlusV_eq }

private noncomputable def leaf5299Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi291InputQChi innerPair256Input
    leaf5299InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5299LowerChecked :
    lowerCheck 24 leaf5299Box leaf5299Inputs = true := by
  rfl'

private theorem leaf5299CoversExact : CoversExact 8
    leaf5299Box leaf5299Certificate leaf5299InnerLog leaf5299Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi291RoundedFacts
    innerPair256RoundedFacts leaf5299RoundedFacts (by rfl)

private theorem leaf5299FlatSound : Sound leaf5299Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5299CertificateValid
    leaf5299InnerLogValid leaf5299CoversExact leaf5299LowerChecked

private noncomputable def leaf5300Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (83/256), chiHi := (21/64) }

private noncomputable def leaf5300Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357157888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1184097303/1073741824) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi292LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715880447/68714315776) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5300InnerLog : WideLogData :=
  innerPair558Data

set_option maxRecDepth 1000000 in
private theorem leaf5300LocalValidity :
    LeafFacts leaf5300Box leaf5300Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5300Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357157888) }) = true
      norm_num [leaf5300Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5300CertificateValid :
    WideCertificateValid leaf5300Box leaf5300Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi292ValidityFacts
    leaf5300LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5300CoverageChecked :
    coverageCheck (innerAD leaf5300Box) leaf5300InnerLog = true := by
  rfl'

private theorem leaf5300InnerLogValid :
    leaf5300InnerLog.Valid 8 (innerAD leaf5300Box) :=
  wideLogDataValid_of_cachedCheck endpoint291PositiveFacts
    endpoint348PositiveFacts.valid leaf5300CoverageChecked

private noncomputable def leaf5300InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5300InputLogOnePlusV_eq :
    leaf5300InputLogOnePlusV = outerEnclosure 24
      (leaf5300Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5300RoundedFacts : LeafRoundedFacts 8
    leaf5300Certificate.logOnePlusV leaf5300InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5300InputLogOnePlusV_eq }

private noncomputable def leaf5300Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi292InputQChi innerPair558Input
    leaf5300InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5300LowerChecked :
    lowerCheck 24 leaf5300Box leaf5300Inputs = true := by
  rfl'

private theorem leaf5300CoversExact : CoversExact 8
    leaf5300Box leaf5300Certificate leaf5300InnerLog leaf5300Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi292RoundedFacts
    innerPair558RoundedFacts leaf5300RoundedFacts (by rfl)

private theorem leaf5300FlatSound : Sound leaf5300Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5300CertificateValid
    leaf5300InnerLogValid leaf5300CoversExact leaf5300LowerChecked

private noncomputable def leaf5301Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5301Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871315/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357192448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1175381551/1073741824) }, upper := { exponent := 1, mantissa := (18137/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715915007/68714384896) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5301InnerLog : WideLogData :=
  innerPair259Data

set_option maxRecDepth 1000000 in
private theorem leaf5301LocalValidity :
    LeafFacts leaf5301Box leaf5301Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5301Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357192448) }) = true
      norm_num [leaf5301Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5301CertificateValid :
    WideCertificateValid leaf5301Box leaf5301Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi293ValidityFacts
    leaf5301LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5301CoverageChecked :
    coverageCheck (innerAD leaf5301Box) leaf5301InnerLog = true := by
  rfl'

private theorem leaf5301InnerLogValid :
    leaf5301InnerLog.Valid 8 (innerAD leaf5301Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint80PositiveFacts.valid leaf5301CoverageChecked

private noncomputable def leaf5301InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5301InputLogOnePlusV_eq :
    leaf5301InputLogOnePlusV = outerEnclosure 24
      (leaf5301Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5301RoundedFacts : LeafRoundedFacts 8
    leaf5301Certificate.logOnePlusV leaf5301InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5301InputLogOnePlusV_eq }

private noncomputable def leaf5301Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi293InputQChi innerPair259Input
    leaf5301InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5301LowerChecked :
    lowerCheck 24 leaf5301Box leaf5301Inputs = true := by
  rfl'

private theorem leaf5301CoversExact : CoversExact 8
    leaf5301Box leaf5301Certificate leaf5301InnerLog leaf5301Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi293RoundedFacts
    innerPair259RoundedFacts leaf5301RoundedFacts (by rfl)

private theorem leaf5301FlatSound : Sound leaf5301Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5301CertificateValid
    leaf5301InnerLogValid leaf5301CoversExact leaf5301LowerChecked

private noncomputable def leaf5302Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5302Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357162496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1182983261/1073741824) }, upper := { exponent := 1, mantissa := (9127/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715885055/68714324992) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5302InnerLog : WideLogData :=
  innerPair557Data

set_option maxRecDepth 1000000 in
private theorem leaf5302LocalValidity :
    LeafFacts leaf5302Box leaf5302Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5302Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357162496) }) = true
      norm_num [leaf5302Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5302CertificateValid :
    WideCertificateValid leaf5302Box leaf5302Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi294ValidityFacts
    leaf5302LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5302CoverageChecked :
    coverageCheck (innerAD leaf5302Box) leaf5302InnerLog = true := by
  rfl'

private theorem leaf5302InnerLogValid :
    leaf5302InnerLog.Valid 8 (innerAD leaf5302Box) :=
  wideLogDataValid_of_cachedCheck endpoint291PositiveFacts
    endpoint347PositiveFacts.valid leaf5302CoverageChecked

private noncomputable def leaf5302InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814731/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5302InputLogOnePlusV_eq :
    leaf5302InputLogOnePlusV = outerEnclosure 24
      (leaf5302Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5302RoundedFacts : LeafRoundedFacts 8
    leaf5302Certificate.logOnePlusV leaf5302InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5302InputLogOnePlusV_eq }

private noncomputable def leaf5302Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi294InputQChi innerPair557Input
    leaf5302InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5302LowerChecked :
    lowerCheck 24 leaf5302Box leaf5302Inputs = true := by
  rfl'

private theorem leaf5302CoversExact : CoversExact 8
    leaf5302Box leaf5302Certificate leaf5302InnerLog leaf5302Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi294RoundedFacts
    innerPair557RoundedFacts leaf5302RoundedFacts (by rfl)

private theorem leaf5302FlatSound : Sound leaf5302Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5302CertificateValid
    leaf5302InnerLogValid leaf5302CoversExact leaf5302LowerChecked

private noncomputable def leaf5303Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5303Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871317/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357170688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1180886237/1073741824) }, upper := { exponent := 1, mantissa := (9111/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715893247/68714341376) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5303InnerLog : WideLogData :=
  innerPair637Data

set_option maxRecDepth 1000000 in
private theorem leaf5303LocalValidity :
    LeafFacts leaf5303Box leaf5303Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5303Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357170688) }) = true
      norm_num [leaf5303Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5303CertificateValid :
    WideCertificateValid leaf5303Box leaf5303Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi293ValidityFacts
    leaf5303LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5303CoverageChecked :
    coverageCheck (innerAD leaf5303Box) leaf5303InnerLog = true := by
  rfl'

private theorem leaf5303InnerLogValid :
    leaf5303InnerLog.Valid 8 (innerAD leaf5303Box) :=
  wideLogDataValid_of_cachedCheck endpoint372PositiveFacts
    endpoint379PositiveFacts.valid leaf5303CoverageChecked

private noncomputable def leaf5303InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5303InputLogOnePlusV_eq :
    leaf5303InputLogOnePlusV = outerEnclosure 24
      (leaf5303Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5303RoundedFacts : LeafRoundedFacts 8
    leaf5303Certificate.logOnePlusV leaf5303InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5303InputLogOnePlusV_eq }

private noncomputable def leaf5303Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi293InputQChi innerPair637Input
    leaf5303InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5303LowerChecked :
    lowerCheck 24 leaf5303Box leaf5303Inputs = true := by
  rfl'

private theorem leaf5303CoversExact : CoversExact 8
    leaf5303Box leaf5303Certificate leaf5303InnerLog leaf5303Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi293RoundedFacts
    innerPair637RoundedFacts leaf5303RoundedFacts (by rfl)

private theorem leaf5303FlatSound : Sound leaf5303Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5303CertificateValid
    leaf5303InnerLogValid leaf5303CoversExact leaf5303LowerChecked

private noncomputable def leaf5304Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5304Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357140480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1188553479/1073741824) }, upper := { exponent := 1, mantissa := (4585/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715863039/68714280960) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5304InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5304LocalValidity :
    LeafFacts leaf5304Box leaf5304Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5304Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357140480) }) = true
      norm_num [leaf5304Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5304CertificateValid :
    WideCertificateValid leaf5304Box leaf5304Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi294ValidityFacts
    leaf5304LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5304CoverageChecked :
    coverageCheck (innerAD leaf5304Box) leaf5304InnerLog = true := by
  rfl'

private theorem leaf5304InnerLogValid :
    leaf5304InnerLog.Valid 8 (innerAD leaf5304Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5304CoverageChecked

private noncomputable def leaf5304InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629467/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5304InputLogOnePlusV_eq :
    leaf5304InputLogOnePlusV = outerEnclosure 24
      (leaf5304Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5304RoundedFacts : LeafRoundedFacts 8
    leaf5304Certificate.logOnePlusV leaf5304InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5304InputLogOnePlusV_eq }

private noncomputable def leaf5304Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi294InputQChi innerPair256Input
    leaf5304InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5304LowerChecked :
    lowerCheck 24 leaf5304Box leaf5304Inputs = true := by
  rfl'

private theorem leaf5304CoversExact : CoversExact 8
    leaf5304Box leaf5304Certificate leaf5304InnerLog leaf5304Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi294RoundedFacts
    innerPair256RoundedFacts leaf5304RoundedFacts (by rfl)

private theorem leaf5304FlatSound : Sound leaf5304Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5304CertificateValid
    leaf5304InnerLogValid leaf5304CoversExact leaf5304LowerChecked

private noncomputable def leaf5305Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5305Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908161792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1190584971/1073741824) }, upper := { exponent := 1, mantissa := (18371/16384) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816550729/9816323584) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5305InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5305LocalValidity :
    LeafFacts leaf5305Box leaf5305Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5305Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908161792) }) = true
      norm_num [leaf5305Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5305CertificateValid :
    WideCertificateValid leaf5305Box leaf5305Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi295ValidityFacts
    leaf5305LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5305CoverageChecked :
    coverageCheck (innerAD leaf5305Box) leaf5305InnerLog = true := by
  rfl'

private theorem leaf5305InnerLogValid :
    leaf5305InnerLog.Valid 8 (innerAD leaf5305Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5305CoverageChecked

private noncomputable def leaf5305InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5305InputLogOnePlusV_eq :
    leaf5305InputLogOnePlusV = outerEnclosure 24
      (leaf5305Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5305RoundedFacts : LeafRoundedFacts 8
    leaf5305Certificate.logOnePlusV leaf5305InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5305InputLogOnePlusV_eq }

private noncomputable def leaf5305Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi295InputQChi innerPair256Input
    leaf5305InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5305LowerChecked :
    lowerCheck 24 leaf5305Box leaf5305Inputs = true := by
  rfl'

private theorem leaf5305CoversExact : CoversExact 8
    leaf5305Box leaf5305Certificate leaf5305InnerLog leaf5305Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi295RoundedFacts
    innerPair256RoundedFacts leaf5305RoundedFacts (by rfl)

private theorem leaf5305FlatSound : Sound leaf5305Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5305CertificateValid
    leaf5305InnerLogValid leaf5305CoversExact leaf5305LowerChecked

private noncomputable def leaf5306Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5306Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (1108345889/1108293632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1198186681/1073741824) }, upper := { exponent := 1, mantissa := (2311/2048) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2216639521/2216587264) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf5306InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5306LocalValidity :
    LeafFacts leaf5306Box leaf5306Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5306Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1108345889/1108293632) }) = true
      norm_num [leaf5306Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5306CertificateValid :
    WideCertificateValid leaf5306Box leaf5306Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi296ValidityFacts
    leaf5306LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5306CoverageChecked :
    coverageCheck (innerAD leaf5306Box) leaf5306InnerLog = true := by
  rfl'

private theorem leaf5306InnerLogValid :
    leaf5306InnerLog.Valid 8 (innerAD leaf5306Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5306CoverageChecked

private noncomputable def leaf5306InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf5306InputLogOnePlusV_eq :
    leaf5306InputLogOnePlusV = outerEnclosure 24
      (leaf5306Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5306RoundedFacts : LeafRoundedFacts 8
    leaf5306Certificate.logOnePlusV leaf5306InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5306InputLogOnePlusV_eq }

private noncomputable def leaf5306Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi296InputQChi innerPair300Input
    leaf5306InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5306LowerChecked :
    lowerCheck 24 leaf5306Box leaf5306Inputs = true := by
  rfl'

private theorem leaf5306CoversExact : CoversExact 8
    leaf5306Box leaf5306Certificate leaf5306InnerLog leaf5306Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi296RoundedFacts
    innerPair300RoundedFacts leaf5306RoundedFacts (by rfl)

private theorem leaf5306FlatSound : Sound leaf5306Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5306CertificateValid
    leaf5306InnerLogValid leaf5306CoversExact leaf5306LowerChecked

private noncomputable def leaf5307Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5307Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357110272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1196220721/1073741824) }, upper := { exponent := 1, mantissa := (9229/8192) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715832831/68714220544) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5307InnerLog : WideLogData :=
  innerPair300Data

set_option maxRecDepth 1000000 in
private theorem leaf5307LocalValidity :
    LeafFacts leaf5307Box leaf5307Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5307Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357110272) }) = true
      norm_num [leaf5307Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5307CertificateValid :
    WideCertificateValid leaf5307Box leaf5307Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi295ValidityFacts
    leaf5307LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5307CoverageChecked :
    coverageCheck (innerAD leaf5307Box) leaf5307InnerLog = true := by
  rfl'

private theorem leaf5307InnerLogValid :
    leaf5307InnerLog.Valid 8 (innerAD leaf5307Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint292PositiveFacts.valid leaf5307CoverageChecked

private noncomputable def leaf5307InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814737/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5307InputLogOnePlusV_eq :
    leaf5307InputLogOnePlusV = outerEnclosure 24
      (leaf5307Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5307RoundedFacts : LeafRoundedFacts 8
    leaf5307Certificate.logOnePlusV leaf5307InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5307InputLogOnePlusV_eq }

private noncomputable def leaf5307Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi295InputQChi innerPair300Input
    leaf5307InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5307LowerChecked :
    lowerCheck 24 leaf5307Box leaf5307Inputs = true := by
  rfl'

private theorem leaf5307CoversExact : CoversExact 8
    leaf5307Box leaf5307Certificate leaf5307InnerLog leaf5307Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi295RoundedFacts
    innerPair300RoundedFacts leaf5307RoundedFacts (by rfl)

private theorem leaf5307FlatSound : Sound leaf5307Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5307CertificateValid
    leaf5307InnerLogValid leaf5307CoversExact leaf5307LowerChecked

private noncomputable def leaf5308Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5308Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357080064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1203887963/1073741824) }, upper := { exponent := 1, mantissa := (1161/1024) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715802623/68714160128) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf5308InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf5308LocalValidity :
    LeafFacts leaf5308Box leaf5308Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5308Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357080064) }) = true
      norm_num [leaf5308Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5308CertificateValid :
    WideCertificateValid leaf5308Box leaf5308Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi296ValidityFacts
    leaf5308LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5308CoverageChecked :
    coverageCheck (innerAD leaf5308Box) leaf5308InnerLog = true := by
  rfl'

private theorem leaf5308InnerLogValid :
    leaf5308InnerLog.Valid 8 (innerAD leaf5308Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf5308CoverageChecked

private noncomputable def leaf5308InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814741/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5308InputLogOnePlusV_eq :
    leaf5308InputLogOnePlusV = outerEnclosure 24
      (leaf5308Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5308RoundedFacts : LeafRoundedFacts 8
    leaf5308Certificate.logOnePlusV leaf5308InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5308InputLogOnePlusV_eq }

private noncomputable def leaf5308Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi296InputQChi innerPair622Input
    leaf5308InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5308LowerChecked :
    lowerCheck 24 leaf5308Box leaf5308Inputs = true := by
  rfl'

private theorem leaf5308CoversExact : CoversExact 8
    leaf5308Box leaf5308Certificate leaf5308InnerLog leaf5308Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi296RoundedFacts
    innerPair622RoundedFacts leaf5308RoundedFacts (by rfl)

private theorem leaf5308FlatSound : Sound leaf5308Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5308CertificateValid
    leaf5308InnerLogValid leaf5308CoversExact leaf5308LowerChecked

private noncomputable def leaf5309Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5309Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871319/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357148928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1186390923/1073741824) }, upper := { exponent := 1, mantissa := (18307/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715871487/68714297856) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5309InnerLog : WideLogData :=
  innerPair620Data

set_option maxRecDepth 1000000 in
private theorem leaf5309LocalValidity :
    LeafFacts leaf5309Box leaf5309Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5309Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357148928) }) = true
      norm_num [leaf5309Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5309CertificateValid :
    WideCertificateValid leaf5309Box leaf5309Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi293ValidityFacts
    leaf5309LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5309CoverageChecked :
    coverageCheck (innerAD leaf5309Box) leaf5309InnerLog = true := by
  rfl'

private theorem leaf5309InnerLogValid :
    leaf5309InnerLog.Valid 8 (innerAD leaf5309Box) :=
  wideLogDataValid_of_cachedCheck endpoint346PositiveFacts
    endpoint293PositiveFacts.valid leaf5309CoverageChecked

private noncomputable def leaf5309InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629465/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5309InputLogOnePlusV_eq :
    leaf5309InputLogOnePlusV = outerEnclosure 24
      (leaf5309Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5309RoundedFacts : LeafRoundedFacts 8
    leaf5309Certificate.logOnePlusV leaf5309InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5309InputLogOnePlusV_eq }

private noncomputable def leaf5309Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi293InputQChi innerPair620Input
    leaf5309InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5309LowerChecked :
    lowerCheck 24 leaf5309Box leaf5309Inputs = true := by
  rfl'

private theorem leaf5309CoversExact : CoversExact 8
    leaf5309Box leaf5309Certificate leaf5309InnerLog leaf5309Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi293RoundedFacts
    innerPair620RoundedFacts leaf5309RoundedFacts (by rfl)

private theorem leaf5309FlatSound : Sound leaf5309Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5309CertificateValid
    leaf5309InnerLogValid leaf5309CoversExact leaf5309LowerChecked

private noncomputable def leaf5310Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5310Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (1108345889/1108294144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1194123697/1073741824) }, upper := { exponent := 1, mantissa := (9213/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2216640033/2216588288) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5310InnerLog : WideLogData :=
  innerPair256Data

set_option maxRecDepth 1000000 in
private theorem leaf5310LocalValidity :
    LeafFacts leaf5310Box leaf5310Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5310Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1108345889/1108294144) }) = true
      norm_num [leaf5310Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5310CertificateValid :
    WideCertificateValid leaf5310Box leaf5310Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi294ValidityFacts
    leaf5310LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5310CoverageChecked :
    coverageCheck (innerAD leaf5310Box) leaf5310InnerLog = true := by
  rfl'

private theorem leaf5310InnerLogValid :
    leaf5310InnerLog.Valid 8 (innerAD leaf5310Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint75PositiveFacts.valid leaf5310CoverageChecked

private noncomputable def leaf5310InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf5310InputLogOnePlusV_eq :
    leaf5310InputLogOnePlusV = outerEnclosure 24
      (leaf5310Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5310RoundedFacts : LeafRoundedFacts 8
    leaf5310Certificate.logOnePlusV leaf5310InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5310InputLogOnePlusV_eq }

private noncomputable def leaf5310Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi294InputQChi innerPair256Input
    leaf5310InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5310LowerChecked :
    lowerCheck 24 leaf5310Box leaf5310Inputs = true := by
  rfl'

private theorem leaf5310CoversExact : CoversExact 8
    leaf5310Box leaf5310Certificate leaf5310InnerLog leaf5310Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi294RoundedFacts
    innerPair256RoundedFacts leaf5310RoundedFacts (by rfl)

private theorem leaf5310FlatSound : Sound leaf5310Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5310CertificateValid
    leaf5310InnerLogValid leaf5310CoversExact leaf5310LowerChecked

private noncomputable def leaf5311Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (21/64), chiHi := (85/256) }

private noncomputable def leaf5311Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871321/536870912) }, vSqrt := { lower := (8191/8192), upper := (4908388937/4908161024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1191895609/1073741824) }, upper := { exponent := 1, mantissa := (2299/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi293LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9816549961/9816322048) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5311InnerLog : WideLogData :=
  innerPair303Data

set_option maxRecDepth 1000000 in
private theorem leaf5311LocalValidity :
    LeafFacts leaf5311Box leaf5311Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5311Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4908388937/4908161024) }) = true
      norm_num [leaf5311Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5311CertificateValid :
    WideCertificateValid leaf5311Box leaf5311Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi293ValidityFacts
    leaf5311LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5311CoverageChecked :
    coverageCheck (innerAD leaf5311Box) leaf5311InnerLog = true := by
  rfl'

private theorem leaf5311InnerLogValid :
    leaf5311InnerLog.Valid 8 (innerAD leaf5311Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint380PositiveFacts.valid leaf5311CoverageChecked

private noncomputable def leaf5311InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5311InputLogOnePlusV_eq :
    leaf5311InputLogOnePlusV = outerEnclosure 24
      (leaf5311Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5311RoundedFacts : LeafRoundedFacts 8
    leaf5311Certificate.logOnePlusV leaf5311InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5311InputLogOnePlusV_eq }

private noncomputable def leaf5311Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi293InputQChi innerPair303Input
    leaf5311InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5311LowerChecked :
    lowerCheck 24 leaf5311Box leaf5311Inputs = true := by
  rfl'

private theorem leaf5311CoversExact : CoversExact 8
    leaf5311Box leaf5311Certificate leaf5311InnerLog leaf5311Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi293RoundedFacts
    innerPair303RoundedFacts leaf5311RoundedFacts (by rfl)

private theorem leaf5311FlatSound : Sound leaf5311Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5311CertificateValid
    leaf5311InnerLogValid leaf5311CoversExact leaf5311LowerChecked

private noncomputable def leaf5312Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (85/256), chiHi := (43/128) }

private noncomputable def leaf5312Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357096448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1199693915/1073741824) }, upper := { exponent := 1, mantissa := (1157/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi294LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715819007/68714192896) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5312InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5312LocalValidity :
    LeafFacts leaf5312Box leaf5312Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5312Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357096448) }) = true
      norm_num [leaf5312Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5312CertificateValid :
    WideCertificateValid leaf5312Box leaf5312Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi294ValidityFacts
    leaf5312LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5312CoverageChecked :
    coverageCheck (innerAD leaf5312Box) leaf5312InnerLog = true := by
  rfl'

private theorem leaf5312InnerLogValid :
    leaf5312InnerLog.Valid 8 (innerAD leaf5312Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5312CoverageChecked

private noncomputable def leaf5312InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814739/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf5312InputLogOnePlusV_eq :
    leaf5312InputLogOnePlusV = outerEnclosure 24
      (leaf5312Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5312RoundedFacts : LeafRoundedFacts 8
    leaf5312Certificate.logOnePlusV leaf5312InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5312InputLogOnePlusV_eq }

private noncomputable def leaf5312Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi294InputQChi innerPair621Input
    leaf5312InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5312LowerChecked :
    lowerCheck 24 leaf5312Box leaf5312Inputs = true := by
  rfl'

private theorem leaf5312CoversExact : CoversExact 8
    leaf5312Box leaf5312Certificate leaf5312InnerLog leaf5312Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi294RoundedFacts
    innerPair621RoundedFacts leaf5312RoundedFacts (by rfl)

private theorem leaf5312FlatSound : Sound leaf5312Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5312CertificateValid
    leaf5312InnerLogValid leaf5312CoversExact leaf5312LowerChecked

private noncomputable def leaf5313Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5313Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871323/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357088000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1201856471/1073741824) }, upper := { exponent := 1, mantissa := (18545/16384) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715810559/68714176000) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5313InnerLog : WideLogData :=
  innerPair621Data

set_option maxRecDepth 1000000 in
private theorem leaf5313LocalValidity :
    LeafFacts leaf5313Box leaf5313Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5313Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357088000) }) = true
      norm_num [leaf5313Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5313CertificateValid :
    WideCertificateValid leaf5313Box leaf5313Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi295ValidityFacts
    leaf5313LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5313CoverageChecked :
    coverageCheck (innerAD leaf5313Box) leaf5313InnerLog = true := by
  rfl'

private theorem leaf5313InnerLogValid :
    leaf5313InnerLog.Valid 8 (innerAD leaf5313Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint292PositiveFacts.valid leaf5313CoverageChecked

private noncomputable def leaf5313InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453685/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf5313InputLogOnePlusV_eq :
    leaf5313InputLogOnePlusV = outerEnclosure 24
      (leaf5313Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5313RoundedFacts : LeafRoundedFacts 8
    leaf5313Certificate.logOnePlusV leaf5313InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5313InputLogOnePlusV_eq }

private noncomputable def leaf5313Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi295InputQChi innerPair621Input
    leaf5313InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5313LowerChecked :
    lowerCheck 24 leaf5313Box leaf5313Inputs = true := by
  rfl'

private theorem leaf5313CoversExact : CoversExact 8
    leaf5313Box leaf5313Certificate leaf5313InnerLog leaf5313Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi295RoundedFacts
    innerPair621RoundedFacts leaf5313RoundedFacts (by rfl)

private theorem leaf5313FlatSound : Sound leaf5313Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5313CertificateValid
    leaf5313InnerLogValid leaf5313CoversExact leaf5313LowerChecked

private noncomputable def leaf5314Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5314Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357057536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1209589245/1073741824) }, upper := { exponent := 1, mantissa := (2333/2048) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715780095/68714115072) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf5314InnerLog : WideLogData :=
  innerPair269Data

set_option maxRecDepth 1000000 in
private theorem leaf5314LocalValidity :
    LeafFacts leaf5314Box leaf5314Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5314Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357057536) }) = true
      norm_num [leaf5314Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5314CertificateValid :
    WideCertificateValid leaf5314Box leaf5314Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi296ValidityFacts
    leaf5314LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5314CoverageChecked :
    coverageCheck (innerAD leaf5314Box) leaf5314InnerLog = true := by
  rfl'

private theorem leaf5314InnerLogValid :
    leaf5314InnerLog.Valid 8 (innerAD leaf5314Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint295PositiveFacts.valid leaf5314CoverageChecked

private noncomputable def leaf5314InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5314InputLogOnePlusV_eq :
    leaf5314InputLogOnePlusV = outerEnclosure 24
      (leaf5314Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5314RoundedFacts : LeafRoundedFacts 8
    leaf5314Certificate.logOnePlusV leaf5314InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5314InputLogOnePlusV_eq }

private noncomputable def leaf5314Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi296InputQChi innerPair269Input
    leaf5314InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5314LowerChecked :
    lowerCheck 24 leaf5314Box leaf5314Inputs = true := by
  rfl'

private theorem leaf5314CoversExact : CoversExact 8
    leaf5314Box leaf5314Certificate leaf5314InnerLog leaf5314Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi296RoundedFacts
    innerPair269RoundedFacts leaf5314RoundedFacts (by rfl)

private theorem leaf5314FlatSound : Sound leaf5314Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5314CertificateValid
    leaf5314InnerLogValid leaf5314CoversExact leaf5314LowerChecked

private noncomputable def leaf5315Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (43/128), chiHi := (87/256) }

private noncomputable def leaf5315Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871325/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357065728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1207492221/1073741824) }, upper := { exponent := 1, mantissa := (2329/2048) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi295LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715788287/68714131456) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5315InnerLog : WideLogData :=
  innerPair622Data

set_option maxRecDepth 1000000 in
private theorem leaf5315LocalValidity :
    LeafFacts leaf5315Box leaf5315Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5315Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357065728) }) = true
      norm_num [leaf5315Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5315CertificateValid :
    WideCertificateValid leaf5315Box leaf5315Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi295ValidityFacts
    leaf5315LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5315CoverageChecked :
    coverageCheck (innerAD leaf5315Box) leaf5315InnerLog = true := by
  rfl'

private theorem leaf5315InnerLogValid :
    leaf5315InnerLog.Valid 8 (innerAD leaf5315Box) :=
  wideLogDataValid_of_cachedCheck endpoint347PositiveFacts
    endpoint295PositiveFacts.valid leaf5315CoverageChecked

private noncomputable def leaf5315InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5315InputLogOnePlusV_eq :
    leaf5315InputLogOnePlusV = outerEnclosure 24
      (leaf5315Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5315RoundedFacts : LeafRoundedFacts 8
    leaf5315Certificate.logOnePlusV leaf5315InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5315InputLogOnePlusV_eq }

private noncomputable def leaf5315Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi295InputQChi innerPair622Input
    leaf5315InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5315LowerChecked :
    lowerCheck 24 leaf5315Box leaf5315Inputs = true := by
  rfl'

private theorem leaf5315CoversExact : CoversExact 8
    leaf5315Box leaf5315Certificate leaf5315InnerLog leaf5315Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi295RoundedFacts
    innerPair622RoundedFacts leaf5315RoundedFacts (by rfl)

private theorem leaf5315FlatSound : Sound leaf5315Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5315CertificateValid
    leaf5315InnerLogValid leaf5315CoversExact leaf5315LowerChecked

private noncomputable def leaf5316Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (87/256), chiHi := (11/32) }

private noncomputable def leaf5316Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (536871327/536870912) }, vSqrt := { lower := (8191/8192), upper := (34358722559/34357035008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (1215290527/1073741824) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi296LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68715757567/68714070016) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf5316InnerLog : WideLogData :=
  innerPair271Data

set_option maxRecDepth 1000000 in
private theorem leaf5316LocalValidity :
    LeafFacts leaf5316Box leaf5316Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf5316Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34358722559/34357035008) }) = true
      norm_num [leaf5316Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf5316CertificateValid :
    WideCertificateValid leaf5316Box leaf5316Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi296ValidityFacts
    leaf5316LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf5316CoverageChecked :
    coverageCheck (innerAD leaf5316Box) leaf5316InnerLog = true := by
  rfl'

private theorem leaf5316InnerLogValid :
    leaf5316InnerLog.Valid 8 (innerAD leaf5316Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint298PositiveFacts.valid leaf5316CoverageChecked

private noncomputable def leaf5316InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf5316InputLogOnePlusV_eq :
    leaf5316InputLogOnePlusV = outerEnclosure 24
      (leaf5316Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf5316RoundedFacts : LeafRoundedFacts 8
    leaf5316Certificate.logOnePlusV leaf5316InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf5316InputLogOnePlusV_eq }

private noncomputable def leaf5316Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi296InputQChi innerPair271Input
    leaf5316InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf5316LowerChecked :
    lowerCheck 24 leaf5316Box leaf5316Inputs = true := by
  rfl'

private theorem leaf5316CoversExact : CoversExact 8
    leaf5316Box leaf5316Certificate leaf5316InnerLog leaf5316Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi296RoundedFacts
    innerPair271RoundedFacts leaf5316RoundedFacts (by rfl)

private theorem leaf5316FlatSound : Sound leaf5316Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf5316CertificateValid
    leaf5316InnerLogValid leaf5316CoversExact leaf5316LowerChecked

private noncomputable def component107Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node0_sound : Sound component107Node0Box :=
  sound_of_literal_split component107Node0Box leaf5279Box leaf5280Box
    .chi (81/256) (by rfl) (by rfl)
    leaf5279FlatSound leaf5280FlatSound

private noncomputable def component107Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component107Node1_sound : Sound component107Node1Box :=
  sound_of_literal_split component107Node1Box leaf5281Box leaf5282Box
    .k (235/64) (by rfl) (by rfl)
    leaf5281FlatSound leaf5282FlatSound

private noncomputable def component107Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node2_sound : Sound component107Node2Box :=
  sound_of_literal_split component107Node2Box component107Node1Box leaf5283Box
    .chi (81/256) (by rfl) (by rfl)
    component107Node1_sound leaf5283FlatSound

private noncomputable def component107Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node3_sound : Sound component107Node3Box :=
  sound_of_literal_split component107Node3Box component107Node0Box component107Node2Box
    .k (117/32) (by rfl) (by rfl)
    component107Node0_sound component107Node2_sound

private noncomputable def component107Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node4_sound : Sound component107Node4Box :=
  sound_of_literal_split component107Node4Box leaf5284Box leaf5285Box
    .chi (83/256) (by rfl) (by rfl)
    leaf5284FlatSound leaf5285FlatSound

private noncomputable def component107Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node5_sound : Sound component107Node5Box :=
  sound_of_literal_split component107Node5Box leaf5286Box leaf5287Box
    .chi (83/256) (by rfl) (by rfl)
    leaf5286FlatSound leaf5287FlatSound

private noncomputable def component107Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node6_sound : Sound component107Node6Box :=
  sound_of_literal_split component107Node6Box component107Node4Box component107Node5Box
    .k (117/32) (by rfl) (by rfl)
    component107Node4_sound component107Node5_sound

private noncomputable def component107Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node7_sound : Sound component107Node7Box :=
  sound_of_literal_split component107Node7Box component107Node3Box component107Node6Box
    .chi (41/128) (by rfl) (by rfl)
    component107Node3_sound component107Node6_sound

private noncomputable def component107Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component107Node8_sound : Sound component107Node8Box :=
  sound_of_literal_split component107Node8Box leaf5288Box leaf5289Box
    .k (237/64) (by rfl) (by rfl)
    leaf5288FlatSound leaf5289FlatSound

private noncomputable def component107Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node9_sound : Sound component107Node9Box :=
  sound_of_literal_split component107Node9Box leaf5290Box leaf5291Box
    .k (237/64) (by rfl) (by rfl)
    leaf5290FlatSound leaf5291FlatSound

private noncomputable def component107Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node10_sound : Sound component107Node10Box :=
  sound_of_literal_split component107Node10Box component107Node8Box component107Node9Box
    .chi (81/256) (by rfl) (by rfl)
    component107Node8_sound component107Node9_sound

private noncomputable def component107Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (5/16), chiHi := (81/256) }

set_option maxRecDepth 1000000 in
private theorem component107Node11_sound : Sound component107Node11Box :=
  sound_of_literal_split component107Node11Box leaf5292Box leaf5293Box
    .k (239/64) (by rfl) (by rfl)
    leaf5292FlatSound leaf5293FlatSound

private noncomputable def component107Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (81/256), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node12_sound : Sound component107Node12Box :=
  sound_of_literal_split component107Node12Box leaf5294Box leaf5295Box
    .k (239/64) (by rfl) (by rfl)
    leaf5294FlatSound leaf5295FlatSound

private noncomputable def component107Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node13_sound : Sound component107Node13Box :=
  sound_of_literal_split component107Node13Box component107Node11Box component107Node12Box
    .chi (81/256) (by rfl) (by rfl)
    component107Node11_sound component107Node12_sound

private noncomputable def component107Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/16), chiHi := (41/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node14_sound : Sound component107Node14Box :=
  sound_of_literal_split component107Node14Box component107Node10Box component107Node13Box
    .k (119/32) (by rfl) (by rfl)
    component107Node10_sound component107Node13_sound

private noncomputable def component107Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node15_sound : Sound component107Node15Box :=
  sound_of_literal_split component107Node15Box leaf5296Box leaf5297Box
    .chi (83/256) (by rfl) (by rfl)
    leaf5296FlatSound leaf5297FlatSound

private noncomputable def component107Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (41/128), chiHi := (83/256) }

set_option maxRecDepth 1000000 in
private theorem component107Node16_sound : Sound component107Node16Box :=
  sound_of_literal_split component107Node16Box leaf5298Box leaf5299Box
    .k (239/64) (by rfl) (by rfl)
    leaf5298FlatSound leaf5299FlatSound

private noncomputable def component107Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node17_sound : Sound component107Node17Box :=
  sound_of_literal_split component107Node17Box component107Node16Box leaf5300Box
    .chi (83/256) (by rfl) (by rfl)
    component107Node16_sound leaf5300FlatSound

private noncomputable def component107Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (41/128), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node18_sound : Sound component107Node18Box :=
  sound_of_literal_split component107Node18Box component107Node15Box component107Node17Box
    .k (119/32) (by rfl) (by rfl)
    component107Node15_sound component107Node17_sound

private noncomputable def component107Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node19_sound : Sound component107Node19Box :=
  sound_of_literal_split component107Node19Box component107Node14Box component107Node18Box
    .chi (41/128) (by rfl) (by rfl)
    component107Node14_sound component107Node18_sound

private noncomputable def component107Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component107Node20_sound : Sound component107Node20Box :=
  sound_of_literal_split component107Node20Box component107Node7Box component107Node19Box
    .k (59/16) (by rfl) (by rfl)
    component107Node7_sound component107Node19_sound

private noncomputable def component107Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node21_sound : Sound component107Node21Box :=
  sound_of_literal_split component107Node21Box leaf5301Box leaf5302Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5301FlatSound leaf5302FlatSound

private noncomputable def component107Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node22_sound : Sound component107Node22Box :=
  sound_of_literal_split component107Node22Box leaf5303Box leaf5304Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5303FlatSound leaf5304FlatSound

private noncomputable def component107Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node23_sound : Sound component107Node23Box :=
  sound_of_literal_split component107Node23Box component107Node21Box component107Node22Box
    .k (117/32) (by rfl) (by rfl)
    component107Node21_sound component107Node22_sound

private noncomputable def component107Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node24_sound : Sound component107Node24Box :=
  sound_of_literal_split component107Node24Box leaf5305Box leaf5306Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5305FlatSound leaf5306FlatSound

private noncomputable def component107Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node25_sound : Sound component107Node25Box :=
  sound_of_literal_split component107Node25Box leaf5307Box leaf5308Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5307FlatSound leaf5308FlatSound

private noncomputable def component107Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node26_sound : Sound component107Node26Box :=
  sound_of_literal_split component107Node26Box component107Node24Box component107Node25Box
    .k (117/32) (by rfl) (by rfl)
    component107Node24_sound component107Node25_sound

private noncomputable def component107Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node27_sound : Sound component107Node27Box :=
  sound_of_literal_split component107Node27Box component107Node23Box component107Node26Box
    .chi (43/128) (by rfl) (by rfl)
    component107Node23_sound component107Node26_sound

private noncomputable def component107Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node28_sound : Sound component107Node28Box :=
  sound_of_literal_split component107Node28Box leaf5309Box leaf5310Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5309FlatSound leaf5310FlatSound

private noncomputable def component107Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node29_sound : Sound component107Node29Box :=
  sound_of_literal_split component107Node29Box leaf5311Box leaf5312Box
    .chi (85/256) (by rfl) (by rfl)
    leaf5311FlatSound leaf5312FlatSound

private noncomputable def component107Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (21/64), chiHi := (43/128) }

set_option maxRecDepth 1000000 in
private theorem component107Node30_sound : Sound component107Node30Box :=
  sound_of_literal_split component107Node30Box component107Node28Box component107Node29Box
    .k (119/32) (by rfl) (by rfl)
    component107Node28_sound component107Node29_sound

private noncomputable def component107Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node31_sound : Sound component107Node31Box :=
  sound_of_literal_split component107Node31Box leaf5313Box leaf5314Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5313FlatSound leaf5314FlatSound

private noncomputable def component107Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node32_sound : Sound component107Node32Box :=
  sound_of_literal_split component107Node32Box leaf5315Box leaf5316Box
    .chi (87/256) (by rfl) (by rfl)
    leaf5315FlatSound leaf5316FlatSound

private noncomputable def component107Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (43/128), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node33_sound : Sound component107Node33Box :=
  sound_of_literal_split component107Node33Box component107Node31Box component107Node32Box
    .k (119/32) (by rfl) (by rfl)
    component107Node31_sound component107Node32_sound

private noncomputable def component107Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node34_sound : Sound component107Node34Box :=
  sound_of_literal_split component107Node34Box component107Node30Box component107Node33Box
    .chi (43/128) (by rfl) (by rfl)
    component107Node30_sound component107Node33_sound

private noncomputable def component107Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component107Node35_sound : Sound component107Node35Box :=
  sound_of_literal_split component107Node35Box component107Node27Box component107Node34Box
    .k (59/16) (by rfl) (by rfl)
    component107Node27_sound component107Node34_sound

noncomputable def component107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
theorem component107_sound : Sound component107Box :=
  sound_of_literal_split component107Box component107Node20Box component107Node35Box
    .chi (21/64) (by rfl) (by rfl)
    component107Node20_sound component107Node35_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
