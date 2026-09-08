import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf3561Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3561Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431176704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2048824599/1073741824) }, upper := { exponent := 0, mantissa := (31573/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868098559/274862353408) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3561InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3561LocalValidity :
    LeafFacts leaf3561Box leaf3561Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3561Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431176704) }) = true
      norm_num [leaf3561Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3561CertificateValid :
    WideCertificateValid leaf3561Box leaf3561Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi191ValidityFacts
    leaf3561LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3561CoverageChecked :
    coverageCheck (innerAD leaf3561Box) leaf3561InnerLog = true := by
  rfl'

private theorem leaf3561InnerLogValid :
    leaf3561InnerLog.Valid 8 (innerAD leaf3561Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3561CoverageChecked

private noncomputable def leaf3561InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3561InputLogOnePlusV_eq :
    leaf3561InputLogOnePlusV = outerEnclosure 24
      (leaf3561Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3561RoundedFacts : LeafRoundedFacts 8
    leaf3561Certificate.logOnePlusV leaf3561InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3561InputLogOnePlusV_eq }

private noncomputable def leaf3561Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi191InputQChi innerPair100Input
    leaf3561InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3561LowerChecked :
    lowerCheck 24 leaf3561Box leaf3561Inputs = true := by
  rfl'

private theorem leaf3561CoversExact : CoversExact 8
    leaf3561Box leaf3561Certificate leaf3561InnerLog leaf3561Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi191RoundedFacts
    innerPair100RoundedFacts leaf3561RoundedFacts (by rfl)

private theorem leaf3561FlatSound : Sound leaf3561Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3561CertificateValid
    leaf3561InnerLogValid leaf3561CoversExact leaf3561LowerChecked

private noncomputable def leaf3562Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3562Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810381824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2052756517/1073741824) }, upper := { exponent := 0, mantissa := (15817/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622689109/91620763648) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3562InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3562LocalValidity :
    LeafFacts leaf3562Box leaf3562Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3562Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810381824) }) = true
      norm_num [leaf3562Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3562CertificateValid :
    WideCertificateValid leaf3562Box leaf3562Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi191ValidityFacts
    leaf3562LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3562CoverageChecked :
    coverageCheck (innerAD leaf3562Box) leaf3562InnerLog = true := by
  rfl'

private theorem leaf3562InnerLogValid :
    leaf3562InnerLog.Valid 8 (innerAD leaf3562Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3562CoverageChecked

private noncomputable def leaf3562InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3562InputLogOnePlusV_eq :
    leaf3562InputLogOnePlusV = outerEnclosure 24
      (leaf3562Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3562RoundedFacts : LeafRoundedFacts 8
    leaf3562Certificate.logOnePlusV leaf3562InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3562InputLogOnePlusV_eq }

private noncomputable def leaf3562Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi191InputQChi innerPair100Input
    leaf3562InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3562LowerChecked :
    lowerCheck 24 leaf3562Box leaf3562Inputs = true := by
  rfl'

private theorem leaf3562CoversExact : CoversExact 8
    leaf3562Box leaf3562Certificate leaf3562InnerLog leaf3562Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi191RoundedFacts
    innerPair100RoundedFacts leaf3562RoundedFacts (by rfl)

private theorem leaf3562FlatSound : Sound leaf3562Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3562CertificateValid
    leaf3562InnerLogValid leaf3562CoversExact leaf3562LowerChecked

private noncomputable def leaf3563Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3563Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196070912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2065076533/1073741824) }, upper := { exponent := 0, mantissa := (15911/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392278397/6392141824) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3563InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3563LocalValidity :
    LeafFacts leaf3563Box leaf3563Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3563Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196070912) }) = true
      norm_num [leaf3563Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3563CertificateValid :
    WideCertificateValid leaf3563Box leaf3563Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi192ValidityFacts
    leaf3563LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3563CoverageChecked :
    coverageCheck (innerAD leaf3563Box) leaf3563InnerLog = true := by
  rfl'

private theorem leaf3563InnerLogValid :
    leaf3563InnerLog.Valid 8 (innerAD leaf3563Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3563CoverageChecked

private noncomputable def leaf3563InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3563InputLogOnePlusV_eq :
    leaf3563InputLogOnePlusV = outerEnclosure 24
      (leaf3563Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3563RoundedFacts : LeafRoundedFacts 8
    leaf3563Certificate.logOnePlusV leaf3563InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3563InputLogOnePlusV_eq }

private noncomputable def leaf3563Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi192InputQChi innerPair304Input
    leaf3563InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3563LowerChecked :
    lowerCheck 24 leaf3563Box leaf3563Inputs = true := by
  rfl'

private theorem leaf3563CoversExact : CoversExact 8
    leaf3563Box leaf3563Certificate leaf3563InnerLog leaf3563Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi192RoundedFacts
    innerPair304RoundedFacts leaf3563RoundedFacts (by rfl)

private theorem leaf3563FlatSound : Sound leaf3563Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3563CertificateValid
    leaf3563InnerLogValid leaf3563CoversExact leaf3563LowerChecked

private noncomputable def leaf3564Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3564Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431017472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2069073983/1073741824) }, upper := { exponent := 0, mantissa := (7971/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867939327/274862034944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3564InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3564LocalValidity :
    LeafFacts leaf3564Box leaf3564Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3564Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431017472) }) = true
      norm_num [leaf3564Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3564CertificateValid :
    WideCertificateValid leaf3564Box leaf3564Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi192ValidityFacts
    leaf3564LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3564CoverageChecked :
    coverageCheck (innerAD leaf3564Box) leaf3564InnerLog = true := by
  rfl'

private theorem leaf3564InnerLogValid :
    leaf3564InnerLog.Valid 8 (innerAD leaf3564Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3564CoverageChecked

private noncomputable def leaf3564InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3564InputLogOnePlusV_eq :
    leaf3564InputLogOnePlusV = outerEnclosure 24
      (leaf3564Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3564RoundedFacts : LeafRoundedFacts 8
    leaf3564Certificate.logOnePlusV leaf3564InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3564InputLogOnePlusV_eq }

private noncomputable def leaf3564Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi192InputQChi innerPair304Input
    leaf3564InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3564LowerChecked :
    lowerCheck 24 leaf3564Box leaf3564Inputs = true := by
  rfl'

private theorem leaf3564CoversExact : CoversExact 8
    leaf3564Box leaf3564Certificate leaf3564InnerLog leaf3564Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi192RoundedFacts
    innerPair304RoundedFacts leaf3564RoundedFacts (by rfl)

private theorem leaf3564FlatSound : Sound leaf3564Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3564CertificateValid
    leaf3564InnerLogValid leaf3564CoversExact leaf3564LowerChecked

private noncomputable def leaf3565Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3565Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486222848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2056688435/1073741824) }, upper := { exponent := 0, mantissa := (31695/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973607219/54972445696) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3565InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3565LocalValidity :
    LeafFacts leaf3565Box leaf3565Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3565Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486222848) }) = true
      norm_num [leaf3565Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3565CertificateValid :
    WideCertificateValid leaf3565Box leaf3565Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi191ValidityFacts
    leaf3565LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3565CoverageChecked :
    coverageCheck (innerAD leaf3565Box) leaf3565InnerLog = true := by
  rfl'

private theorem leaf3565InnerLogValid :
    leaf3565InnerLog.Valid 8 (innerAD leaf3565Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3565CoverageChecked

private noncomputable def leaf3565InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3565InputLogOnePlusV_eq :
    leaf3565InputLogOnePlusV = outerEnclosure 24
      (leaf3565Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3565RoundedFacts : LeafRoundedFacts 8
    leaf3565Certificate.logOnePlusV leaf3565InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3565InputLogOnePlusV_eq }

private noncomputable def leaf3565Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi191InputQChi innerPair100Input
    leaf3565InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3565LowerChecked :
    lowerCheck 24 leaf3565Box leaf3565Inputs = true := by
  rfl'

private theorem leaf3565CoversExact : CoversExact 8
    leaf3565Box leaf3565Certificate leaf3565InnerLog leaf3565Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi191RoundedFacts
    innerPair100RoundedFacts leaf3565RoundedFacts (by rfl)

private theorem leaf3565FlatSound : Sound leaf3565Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3565CertificateValid
    leaf3565InnerLogValid leaf3565CoversExact leaf3565LowerChecked

private noncomputable def leaf3566Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3566Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431083008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2060620353/1073741824) }, upper := { exponent := 0, mantissa := (7939/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868004863/274862166016) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3566InnerLog : WideLogData :=
  innerPair519Data

set_option maxRecDepth 1000000 in
private theorem leaf3566LocalValidity :
    LeafFacts leaf3566Box leaf3566Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3566Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431083008) }) = true
      norm_num [leaf3566Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3566CertificateValid :
    WideCertificateValid leaf3566Box leaf3566Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi191ValidityFacts
    leaf3566LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3566CoverageChecked :
    coverageCheck (innerAD leaf3566Box) leaf3566InnerLog = true := by
  rfl'

private theorem leaf3566InnerLogValid :
    leaf3566InnerLog.Valid 8 (innerAD leaf3566Box) :=
  wideLogDataValid_of_cachedCheck endpoint249PositiveFacts
    endpoint250PositiveFacts.valid leaf3566CoverageChecked

private noncomputable def leaf3566InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3566InputLogOnePlusV_eq :
    leaf3566InputLogOnePlusV = outerEnclosure 24
      (leaf3566Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3566RoundedFacts : LeafRoundedFacts 8
    leaf3566Certificate.logOnePlusV leaf3566InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3566InputLogOnePlusV_eq }

private noncomputable def leaf3566Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi191InputQChi innerPair519Input
    leaf3566InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3566LowerChecked :
    lowerCheck 24 leaf3566Box leaf3566Inputs = true := by
  rfl'

private theorem leaf3566CoversExact : CoversExact 8
    leaf3566Box leaf3566Certificate leaf3566InnerLog leaf3566Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi191RoundedFacts
    innerPair519RoundedFacts leaf3566RoundedFacts (by rfl)

private theorem leaf3566FlatSound : Sound leaf3566Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3566CertificateValid
    leaf3566InnerLogValid leaf3566CoversExact leaf3566LowerChecked

private noncomputable def leaf3567Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3567Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810328576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2073071433/1073741824) }, upper := { exponent := 0, mantissa := (15973/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622635861/91620657152) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3567InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3567LocalValidity :
    LeafFacts leaf3567Box leaf3567Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3567Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810328576) }) = true
      norm_num [leaf3567Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3567CertificateValid :
    WideCertificateValid leaf3567Box leaf3567Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi192ValidityFacts
    leaf3567LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3567CoverageChecked :
    coverageCheck (innerAD leaf3567Box) leaf3567InnerLog = true := by
  rfl'

private theorem leaf3567InnerLogValid :
    leaf3567InnerLog.Valid 8 (innerAD leaf3567Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3567CoverageChecked

private noncomputable def leaf3567InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3567InputLogOnePlusV_eq :
    leaf3567InputLogOnePlusV = outerEnclosure 24
      (leaf3567Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3567RoundedFacts : LeafRoundedFacts 8
    leaf3567Certificate.logOnePlusV leaf3567InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3567InputLogOnePlusV_eq }

private noncomputable def leaf3567Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi192InputQChi innerPair304Input
    leaf3567InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3567LowerChecked :
    lowerCheck 24 leaf3567Box leaf3567Inputs = true := by
  rfl'

private theorem leaf3567CoversExact : CoversExact 8
    leaf3567Box leaf3567Certificate leaf3567InnerLog leaf3567Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi192RoundedFacts
    innerPair304RoundedFacts leaf3567RoundedFacts (by rfl)

private theorem leaf3567FlatSound : Sound leaf3567Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3567CertificateValid
    leaf3567InnerLogValid leaf3567CoversExact leaf3567LowerChecked

private noncomputable def leaf3568Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3568Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430953984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2077068883/1073741824) }, upper := { exponent := 0, mantissa := (4001/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867875839/274861907968) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3568InnerLog : WideLogData :=
  innerPair529Data

set_option maxRecDepth 1000000 in
private theorem leaf3568LocalValidity :
    LeafFacts leaf3568Box leaf3568Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3568Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430953984) }) = true
      norm_num [leaf3568Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3568CertificateValid :
    WideCertificateValid leaf3568Box leaf3568Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi192ValidityFacts
    leaf3568LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3568CoverageChecked :
    coverageCheck (innerAD leaf3568Box) leaf3568InnerLog = true := by
  rfl'

private theorem leaf3568InnerLogValid :
    leaf3568InnerLog.Valid 8 (innerAD leaf3568Box) :=
  wideLogDataValid_of_cachedCheck endpoint265PositiveFacts
    endpoint266PositiveFacts.valid leaf3568CoverageChecked

private noncomputable def leaf3568InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3568InputLogOnePlusV_eq :
    leaf3568InputLogOnePlusV = outerEnclosure 24
      (leaf3568Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3568RoundedFacts : LeafRoundedFacts 8
    leaf3568Certificate.logOnePlusV leaf3568InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3568InputLogOnePlusV_eq }

private noncomputable def leaf3568Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi192InputQChi innerPair529Input
    leaf3568InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3568LowerChecked :
    lowerCheck 24 leaf3568Box leaf3568Inputs = true := by
  rfl'

private theorem leaf3568CoversExact : CoversExact 8
    leaf3568Box leaf3568Certificate leaf3568InnerLog leaf3568Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi192RoundedFacts
    innerPair529RoundedFacts leaf3568RoundedFacts (by rfl)

private theorem leaf3568FlatSound : Sound leaf3568Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3568CertificateValid
    leaf3568InnerLogValid leaf3568CoversExact leaf3568LowerChecked

private noncomputable def leaf3569Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3569Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430921728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2081328467/1073741824) }, upper := { exponent := 0, mantissa := (32071/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867843583/274861843456) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3569InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf3569LocalValidity :
    LeafFacts leaf3569Box leaf3569Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3569Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430921728) }) = true
      norm_num [leaf3569Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3569CertificateValid :
    WideCertificateValid leaf3569Box leaf3569Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi189ValidityFacts
    leaf3569LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3569CoverageChecked :
    coverageCheck (innerAD leaf3569Box) leaf3569InnerLog = true := by
  rfl'

private theorem leaf3569InnerLogValid :
    leaf3569InnerLog.Valid 8 (innerAD leaf3569Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf3569CoverageChecked

private noncomputable def leaf3569InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3569InputLogOnePlusV_eq :
    leaf3569InputLogOnePlusV = outerEnclosure 24
      (leaf3569Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3569RoundedFacts : LeafRoundedFacts 8
    leaf3569Certificate.logOnePlusV leaf3569InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3569InputLogOnePlusV_eq }

private noncomputable def leaf3569Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi189InputQChi innerPair113Input
    leaf3569InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3569LowerChecked :
    lowerCheck 24 leaf3569Box leaf3569Inputs = true := by
  rfl'

private theorem leaf3569CoversExact : CoversExact 8
    leaf3569Box leaf3569Certificate leaf3569InnerLog leaf3569Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi189RoundedFacts
    innerPair113RoundedFacts leaf3569RoundedFacts (by rfl)

private theorem leaf3569FlatSound : Sound leaf3569Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3569CertificateValid
    leaf3569InnerLogValid leaf3569CoversExact leaf3569LowerChecked

private noncomputable def leaf3570Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3570Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430889472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2085391449/1073741824) }, upper := { exponent := 0, mantissa := (16067/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867811327/274861778944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3570InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf3570LocalValidity :
    LeafFacts leaf3570Box leaf3570Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3570Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430889472) }) = true
      norm_num [leaf3570Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3570CertificateValid :
    WideCertificateValid leaf3570Box leaf3570Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi189ValidityFacts
    leaf3570LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3570CoverageChecked :
    coverageCheck (innerAD leaf3570Box) leaf3570InnerLog = true := by
  rfl'

private theorem leaf3570InnerLogValid :
    leaf3570InnerLog.Valid 8 (innerAD leaf3570Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf3570CoverageChecked

private noncomputable def leaf3570InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3570InputLogOnePlusV_eq :
    leaf3570InputLogOnePlusV = outerEnclosure 24
      (leaf3570Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3570RoundedFacts : LeafRoundedFacts 8
    leaf3570Certificate.logOnePlusV leaf3570InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3570InputLogOnePlusV_eq }

private noncomputable def leaf3570Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi189InputQChi innerPair113Input
    leaf3570InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3570LowerChecked :
    lowerCheck 24 leaf3570Box leaf3570Inputs = true := by
  rfl'

private theorem leaf3570CoversExact : CoversExact 8
    leaf3570Box leaf3570Certificate leaf3570InnerLog leaf3570Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi189RoundedFacts
    innerPair113RoundedFacts leaf3570RoundedFacts (by rfl)

private theorem leaf3570FlatSound : Sound leaf3570Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3570CertificateValid
    leaf3570InnerLogValid leaf3570CoversExact leaf3570LowerChecked

private noncomputable def leaf3571Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3571Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486158848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2097580401/1073741824) }, upper := { exponent := 0, mantissa := (505/256) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973543219/54972317696) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3571InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf3571LocalValidity :
    LeafFacts leaf3571Box leaf3571Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3571Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486158848) }) = true
      norm_num [leaf3571Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3571CertificateValid :
    WideCertificateValid leaf3571Box leaf3571Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi190ValidityFacts
    leaf3571LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3571CoverageChecked :
    coverageCheck (innerAD leaf3571Box) leaf3571InnerLog = true := by
  rfl'

private theorem leaf3571InnerLogValid :
    leaf3571InnerLog.Valid 8 (innerAD leaf3571Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf3571CoverageChecked

private noncomputable def leaf3571InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3571InputLogOnePlusV_eq :
    leaf3571InputLogOnePlusV = outerEnclosure 24
      (leaf3571Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3571RoundedFacts : LeafRoundedFacts 8
    leaf3571Certificate.logOnePlusV leaf3571InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3571InputLogOnePlusV_eq }

private noncomputable def leaf3571Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi190InputQChi innerPair238Input
    leaf3571InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3571LowerChecked :
    lowerCheck 24 leaf3571Box leaf3571Inputs = true := by
  rfl'

private theorem leaf3571CoversExact : CoversExact 8
    leaf3571Box leaf3571Certificate leaf3571InnerLog leaf3571Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi190RoundedFacts
    innerPair238RoundedFacts leaf3571RoundedFacts (by rfl)

private theorem leaf3571FlatSound : Sound leaf3571Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3571CertificateValid
    leaf3571InnerLogValid leaf3571CoversExact leaf3571LowerChecked

private noncomputable def leaf3572Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3572Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270084608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2101708915/1073741824) }, upper := { exponent := 0, mantissa := (253/128) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540853703/30540169216) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3572InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf3572LocalValidity :
    LeafFacts leaf3572Box leaf3572Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3572Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270084608) }) = true
      norm_num [leaf3572Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3572CertificateValid :
    WideCertificateValid leaf3572Box leaf3572Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi190ValidityFacts
    leaf3572LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3572CoverageChecked :
    coverageCheck (innerAD leaf3572Box) leaf3572InnerLog = true := by
  rfl'

private theorem leaf3572InnerLogValid :
    leaf3572InnerLog.Valid 8 (innerAD leaf3572Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf3572CoverageChecked

private noncomputable def leaf3572InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3572InputLogOnePlusV_eq :
    leaf3572InputLogOnePlusV = outerEnclosure 24
      (leaf3572Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3572RoundedFacts : LeafRoundedFacts 8
    leaf3572Certificate.logOnePlusV leaf3572InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3572InputLogOnePlusV_eq }

private noncomputable def leaf3572Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi190InputQChi innerPair238Input
    leaf3572InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3572LowerChecked :
    lowerCheck 24 leaf3572Box leaf3572Inputs = true := by
  rfl'

private theorem leaf3572CoversExact : CoversExact 8
    leaf3572Box leaf3572Certificate leaf3572InnerLog leaf3572Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi190RoundedFacts
    innerPair238RoundedFacts leaf3572RoundedFacts (by rfl)

private theorem leaf3572FlatSound : Sound leaf3572Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3572CertificateValid
    leaf3572InnerLogValid leaf3572CoversExact leaf3572LowerChecked

private noncomputable def leaf3573Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3573Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430857216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2089454431/1073741824) }, upper := { exponent := 0, mantissa := (32197/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867779071/274861714432) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3573InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf3573LocalValidity :
    LeafFacts leaf3573Box leaf3573Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3573Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430857216) }) = true
      norm_num [leaf3573Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3573CertificateValid :
    WideCertificateValid leaf3573Box leaf3573Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi189ValidityFacts
    leaf3573LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3573CoverageChecked :
    coverageCheck (innerAD leaf3573Box) leaf3573InnerLog = true := by
  rfl'

private theorem leaf3573InnerLogValid :
    leaf3573InnerLog.Valid 8 (innerAD leaf3573Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf3573CoverageChecked

private noncomputable def leaf3573InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3573InputLogOnePlusV_eq :
    leaf3573InputLogOnePlusV = outerEnclosure 24
      (leaf3573Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3573RoundedFacts : LeafRoundedFacts 8
    leaf3573Certificate.logOnePlusV leaf3573InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3573InputLogOnePlusV_eq }

private noncomputable def leaf3573Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi189InputQChi innerPair113Input
    leaf3573InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3573LowerChecked :
    lowerCheck 24 leaf3573Box leaf3573Inputs = true := by
  rfl'

private theorem leaf3573CoversExact : CoversExact 8
    leaf3573Box leaf3573Certificate leaf3573InnerLog leaf3573Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi189RoundedFacts
    innerPair113RoundedFacts leaf3573RoundedFacts (by rfl)

private theorem leaf3573FlatSound : Sound leaf3573Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3573CertificateValid
    leaf3573InnerLogValid leaf3573CoversExact leaf3573LowerChecked

private noncomputable def leaf3574Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3574Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486164992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2093517413/1073741824) }, upper := { exponent := 0, mantissa := (8065/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973549363/54972329984) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3574InnerLog : WideLogData :=
  innerPair535Data

set_option maxRecDepth 1000000 in
private theorem leaf3574LocalValidity :
    LeafFacts leaf3574Box leaf3574Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3574Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486164992) }) = true
      norm_num [leaf3574Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3574CertificateValid :
    WideCertificateValid leaf3574Box leaf3574Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi189ValidityFacts
    leaf3574LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3574CoverageChecked :
    coverageCheck (innerAD leaf3574Box) leaf3574InnerLog = true := by
  rfl'

private theorem leaf3574InnerLogValid :
    leaf3574InnerLog.Valid 8 (innerAD leaf3574Box) :=
  wideLogDataValid_of_cachedCheck endpoint268PositiveFacts
    endpoint269PositiveFacts.valid leaf3574CoverageChecked

private noncomputable def leaf3574InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3574InputLogOnePlusV_eq :
    leaf3574InputLogOnePlusV = outerEnclosure 24
      (leaf3574Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3574RoundedFacts : LeafRoundedFacts 8
    leaf3574Certificate.logOnePlusV leaf3574InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3574InputLogOnePlusV_eq }

private noncomputable def leaf3574Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi189InputQChi innerPair535Input
    leaf3574InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3574LowerChecked :
    lowerCheck 24 leaf3574Box leaf3574Inputs = true := by
  rfl'

private theorem leaf3574CoversExact : CoversExact 8
    leaf3574Box leaf3574Certificate leaf3574InnerLog leaf3574Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi189RoundedFacts
    innerPair535RoundedFacts leaf3574RoundedFacts (by rfl)

private theorem leaf3574FlatSound : Sound leaf3574Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3574CertificateValid
    leaf3574InnerLogValid leaf3574CoversExact leaf3574LowerChecked

private noncomputable def leaf3575Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3575Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084160512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2105837429/1073741824) }, upper := { exponent := 0, mantissa := (507/256) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168685327/16168321024) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3575InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf3575LocalValidity :
    LeafFacts leaf3575Box leaf3575Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3575Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084160512) }) = true
      norm_num [leaf3575Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3575CertificateValid :
    WideCertificateValid leaf3575Box leaf3575Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi190ValidityFacts
    leaf3575LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3575CoverageChecked :
    coverageCheck (innerAD leaf3575Box) leaf3575InnerLog = true := by
  rfl'

private theorem leaf3575InnerLogValid :
    leaf3575InnerLog.Valid 8 (innerAD leaf3575Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf3575CoverageChecked

private noncomputable def leaf3575InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3575InputLogOnePlusV_eq :
    leaf3575InputLogOnePlusV = outerEnclosure 24
      (leaf3575Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3575RoundedFacts : LeafRoundedFacts 8
    leaf3575Certificate.logOnePlusV leaf3575InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3575InputLogOnePlusV_eq }

private noncomputable def leaf3575Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi190InputQChi innerPair238Input
    leaf3575InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3575LowerChecked :
    lowerCheck 24 leaf3575Box leaf3575Inputs = true := by
  rfl'

private theorem leaf3575CoversExact : CoversExact 8
    leaf3575Box leaf3575Certificate leaf3575InnerLog leaf3575Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi190RoundedFacts
    innerPair238RoundedFacts leaf3575RoundedFacts (by rfl)

private theorem leaf3575FlatSound : Sound leaf3575Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3575CertificateValid
    leaf3575InnerLogValid leaf3575CoversExact leaf3575LowerChecked

private noncomputable def leaf3576Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3576Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430695936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2109965943/1073741824) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867617791/274861391872) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3576InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf3576LocalValidity :
    LeafFacts leaf3576Box leaf3576Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3576Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430695936) }) = true
      norm_num [leaf3576Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3576CertificateValid :
    WideCertificateValid leaf3576Box leaf3576Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi190ValidityFacts
    leaf3576LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3576CoverageChecked :
    coverageCheck (innerAD leaf3576Box) leaf3576InnerLog = true := by
  rfl'

private theorem leaf3576InnerLogValid :
    leaf3576InnerLog.Valid 8 (innerAD leaf3576Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf3576CoverageChecked

private noncomputable def leaf3576InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3576InputLogOnePlusV_eq :
    leaf3576InputLogOnePlusV = outerEnclosure 24
      (leaf3576Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3576RoundedFacts : LeafRoundedFacts 8
    leaf3576Certificate.logOnePlusV leaf3576InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3576InputLogOnePlusV_eq }

private noncomputable def leaf3576Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi190InputQChi innerPair238Input
    leaf3576InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3576LowerChecked :
    lowerCheck 24 leaf3576Box leaf3576Inputs = true := by
  rfl'

private theorem leaf3576CoversExact : CoversExact 8
    leaf3576Box leaf3576Certificate leaf3576InnerLog leaf3576Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi190RoundedFacts
    innerPair238RoundedFacts leaf3576RoundedFacts (by rfl)

private theorem leaf3576FlatSound : Sound leaf3576Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3576CertificateValid
    leaf3576InnerLogValid leaf3576CoversExact leaf3576LowerChecked

private noncomputable def leaf3577Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3577Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270116864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2064552271/1073741824) }, upper := { exponent := 0, mantissa := (31817/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540885959/30540233728) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3577InnerLog : WideLogData :=
  innerPair309Data

set_option maxRecDepth 1000000 in
private theorem leaf3577LocalValidity :
    LeafFacts leaf3577Box leaf3577Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3577Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270116864) }) = true
      norm_num [leaf3577Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3577CertificateValid :
    WideCertificateValid leaf3577Box leaf3577Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi191ValidityFacts
    leaf3577LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3577CoverageChecked :
    coverageCheck (innerAD leaf3577Box) leaf3577InnerLog = true := by
  rfl'

private theorem leaf3577InnerLogValid :
    leaf3577InnerLog.Valid 8 (innerAD leaf3577Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint270PositiveFacts.valid leaf3577CoverageChecked

private noncomputable def leaf3577InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3577InputLogOnePlusV_eq :
    leaf3577InputLogOnePlusV = outerEnclosure 24
      (leaf3577Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3577RoundedFacts : LeafRoundedFacts 8
    leaf3577Certificate.logOnePlusV leaf3577InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3577InputLogOnePlusV_eq }

private noncomputable def leaf3577Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi191InputQChi innerPair309Input
    leaf3577InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3577LowerChecked :
    lowerCheck 24 leaf3577Box leaf3577Inputs = true := by
  rfl'

private theorem leaf3577CoversExact : CoversExact 8
    leaf3577Box leaf3577Certificate leaf3577InnerLog leaf3577Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi191RoundedFacts
    innerPair309RoundedFacts leaf3577RoundedFacts (by rfl)

private theorem leaf3577FlatSound : Sound leaf3577Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3577CertificateValid
    leaf3577InnerLogValid leaf3577CoversExact leaf3577LowerChecked

private noncomputable def leaf3578Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3578Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431020544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2068484189/1073741824) }, upper := { exponent := 0, mantissa := (15939/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867942399/274862041088) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3578InnerLog : WideLogData :=
  innerPair518Data

set_option maxRecDepth 1000000 in
private theorem leaf3578LocalValidity :
    LeafFacts leaf3578Box leaf3578Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3578Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431020544) }) = true
      norm_num [leaf3578Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3578CertificateValid :
    WideCertificateValid leaf3578Box leaf3578Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi191ValidityFacts
    leaf3578LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3578CoverageChecked :
    coverageCheck (innerAD leaf3578Box) leaf3578InnerLog = true := by
  rfl'

private theorem leaf3578InnerLogValid :
    leaf3578InnerLog.Valid 8 (innerAD leaf3578Box) :=
  wideLogDataValid_of_cachedCheck endpoint248PositiveFacts
    endpoint271PositiveFacts.valid leaf3578CoverageChecked

private noncomputable def leaf3578InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3578InputLogOnePlusV_eq :
    leaf3578InputLogOnePlusV = outerEnclosure 24
      (leaf3578Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3578RoundedFacts : LeafRoundedFacts 8
    leaf3578Certificate.logOnePlusV leaf3578InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3578InputLogOnePlusV_eq }

private noncomputable def leaf3578Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi191InputQChi innerPair518Input
    leaf3578InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3578LowerChecked :
    lowerCheck 24 leaf3578Box leaf3578Inputs = true := by
  rfl'

private theorem leaf3578CoversExact : CoversExact 8
    leaf3578Box leaf3578Certificate leaf3578InnerLog leaf3578Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi191RoundedFacts
    innerPair518RoundedFacts leaf3578RoundedFacts (by rfl)

private theorem leaf3578FlatSound : Sound leaf3578Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3578CertificateValid
    leaf3578InnerLogValid leaf3578CoversExact leaf3578LowerChecked

private noncomputable def leaf3579Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3579Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742453/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486184448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2081066333/1073741824) }, upper := { exponent := 0, mantissa := (16035/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973568819/54972368896) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3579InnerLog : WideLogData :=
  innerPair112Data

set_option maxRecDepth 1000000 in
private theorem leaf3579LocalValidity :
    LeafFacts leaf3579Box leaf3579Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3579Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486184448) }) = true
      norm_num [leaf3579Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3579CertificateValid :
    WideCertificateValid leaf3579Box leaf3579Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi192ValidityFacts
    leaf3579LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3579CoverageChecked :
    coverageCheck (innerAD leaf3579Box) leaf3579InnerLog = true := by
  rfl'

private theorem leaf3579InnerLogValid :
    leaf3579InnerLog.Valid 8 (innerAD leaf3579Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint83PositiveFacts.valid leaf3579CoverageChecked

private noncomputable def leaf3579InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3579InputLogOnePlusV_eq :
    leaf3579InputLogOnePlusV = outerEnclosure 24
      (leaf3579Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3579RoundedFacts : LeafRoundedFacts 8
    leaf3579Certificate.logOnePlusV leaf3579InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3579InputLogOnePlusV_eq }

private noncomputable def leaf3579Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi192InputQChi innerPair112Input
    leaf3579InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3579LowerChecked :
    lowerCheck 24 leaf3579Box leaf3579Inputs = true := by
  rfl'

private theorem leaf3579CoversExact : CoversExact 8
    leaf3579Box leaf3579Certificate leaf3579InnerLog leaf3579Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi192RoundedFacts
    innerPair112RoundedFacts leaf3579RoundedFacts (by rfl)

private theorem leaf3579FlatSound : Sound leaf3579Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3579CertificateValid
    leaf3579InnerLogValid leaf3579CoversExact leaf3579LowerChecked

private noncomputable def leaf3580Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3580Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270098944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2085063783/1073741824) }, upper := { exponent := 0, mantissa := (8033/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540868039/30540197888) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3580InnerLog : WideLogData :=
  innerPair520Data

set_option maxRecDepth 1000000 in
private theorem leaf3580LocalValidity :
    LeafFacts leaf3580Box leaf3580Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3580Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270098944) }) = true
      norm_num [leaf3580Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3580CertificateValid :
    WideCertificateValid leaf3580Box leaf3580Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi192ValidityFacts
    leaf3580LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3580CoverageChecked :
    coverageCheck (innerAD leaf3580Box) leaf3580InnerLog = true := by
  rfl'

private theorem leaf3580InnerLogValid :
    leaf3580InnerLog.Valid 8 (innerAD leaf3580Box) :=
  wideLogDataValid_of_cachedCheck endpoint250PositiveFacts
    endpoint272PositiveFacts.valid leaf3580CoverageChecked

private noncomputable def leaf3580InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3580InputLogOnePlusV_eq :
    leaf3580InputLogOnePlusV = outerEnclosure 24
      (leaf3580Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3580RoundedFacts : LeafRoundedFacts 8
    leaf3580Certificate.logOnePlusV leaf3580InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3580InputLogOnePlusV_eq }

private noncomputable def leaf3580Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi192InputQChi innerPair520Input
    leaf3580InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3580LowerChecked :
    lowerCheck 24 leaf3580Box leaf3580Inputs = true := by
  rfl'

private theorem leaf3580CoversExact : CoversExact 8
    leaf3580Box leaf3580Certificate leaf3580InnerLog leaf3580Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi192RoundedFacts
    innerPair520RoundedFacts leaf3580RoundedFacts (by rfl)

private theorem leaf3580FlatSound : Sound leaf3580Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3580CertificateValid
    leaf3580InnerLogValid leaf3580CoversExact leaf3580LowerChecked

private noncomputable def leaf3581Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (15/64), chiHi := (121/512) }

private noncomputable def leaf3581Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484399/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431054592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4144865491/2147483648) }, upper := { exponent := 0, mantissa := (63623/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi237LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867976447/274862109184) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3581InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3581LocalValidity :
    LeafFacts leaf3581Box leaf3581Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3581Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431054592) }) = true
      norm_num [leaf3581Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3581CertificateValid :
    WideCertificateValid leaf3581Box leaf3581Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi237ValidityFacts
    leaf3581LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3581CoverageChecked :
    coverageCheck (innerAD leaf3581Box) leaf3581InnerLog = true := by
  rfl'

private theorem leaf3581InnerLogValid :
    leaf3581InnerLog.Valid 8 (innerAD leaf3581Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3581CoverageChecked

private noncomputable def leaf3581InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3581InputLogOnePlusV_eq :
    leaf3581InputLogOnePlusV = outerEnclosure 24
      (leaf3581Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3581RoundedFacts : LeafRoundedFacts 8
    leaf3581Certificate.logOnePlusV leaf3581InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3581InputLogOnePlusV_eq }

private noncomputable def leaf3581Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi237InputQChi innerPair304Input
    leaf3581InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3581LowerChecked :
    lowerCheck 24 leaf3581Box leaf3581Inputs = true := by
  rfl'

private theorem leaf3581CoversExact : CoversExact 8
    leaf3581Box leaf3581Certificate leaf3581InnerLog leaf3581Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi237RoundedFacts
    innerPair304RoundedFacts leaf3581RoundedFacts (by rfl)

private theorem leaf3581FlatSound : Sound leaf3581Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3581CertificateValid
    leaf3581InnerLogValid leaf3581CoversExact leaf3581LowerChecked

private noncomputable def leaf3582Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (121/512), chiHi := (61/256) }

private noncomputable def leaf3582Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484401/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430989312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4161510617/2147483648) }, upper := { exponent := 0, mantissa := (31939/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi238LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867911167/274861978624) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3582InnerLog : WideLogData :=
  innerPair109Data

set_option maxRecDepth 1000000 in
private theorem leaf3582LocalValidity :
    LeafFacts leaf3582Box leaf3582Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3582Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430989312) }) = true
      norm_num [leaf3582Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3582CertificateValid :
    WideCertificateValid leaf3582Box leaf3582Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi238ValidityFacts
    leaf3582LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3582CoverageChecked :
    coverageCheck (innerAD leaf3582Box) leaf3582InnerLog = true := by
  rfl'

private theorem leaf3582InnerLogValid :
    leaf3582InnerLog.Valid 8 (innerAD leaf3582Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint71PositiveFacts.valid leaf3582CoverageChecked

private noncomputable def leaf3582InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629443/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3582InputLogOnePlusV_eq :
    leaf3582InputLogOnePlusV = outerEnclosure 24
      (leaf3582Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3582RoundedFacts : LeafRoundedFacts 8
    leaf3582Certificate.logOnePlusV leaf3582InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3582InputLogOnePlusV_eq }

private noncomputable def leaf3582Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi238InputQChi innerPair109Input
    leaf3582InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3582LowerChecked :
    lowerCheck 24 leaf3582Box leaf3582Inputs = true := by
  rfl'

private theorem leaf3582CoversExact : CoversExact 8
    leaf3582Box leaf3582Certificate leaf3582InnerLog leaf3582Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi238RoundedFacts
    innerPair109RoundedFacts leaf3582RoundedFacts (by rfl)

private theorem leaf3582FlatSound : Sound leaf3582Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3582CertificateValid
    leaf3582InnerLogValid leaf3582CoversExact leaf3582LowerChecked

private noncomputable def leaf3583Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (15/64), chiHi := (121/512) }

private noncomputable def leaf3583Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484401/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431023616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4152729329/2147483648) }, upper := { exponent := 0, mantissa := (249/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi237LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274867945471/274862047232) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3583InnerLog : WideLogData :=
  innerPair304Data

set_option maxRecDepth 1000000 in
private theorem leaf3583LocalValidity :
    LeafFacts leaf3583Box leaf3583Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3583Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431023616) }) = true
      norm_num [leaf3583Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3583CertificateValid :
    WideCertificateValid leaf3583Box leaf3583Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi237ValidityFacts
    leaf3583LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3583CoverageChecked :
    coverageCheck (innerAD leaf3583Box) leaf3583InnerLog = true := by
  rfl'

private theorem leaf3583InnerLogValid :
    leaf3583InnerLog.Valid 8 (innerAD leaf3583Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint71PositiveFacts.valid leaf3583CoverageChecked

private noncomputable def leaf3583InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3583InputLogOnePlusV_eq :
    leaf3583InputLogOnePlusV = outerEnclosure 24
      (leaf3583Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3583RoundedFacts : LeafRoundedFacts 8
    leaf3583Certificate.logOnePlusV leaf3583InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3583InputLogOnePlusV_eq }

private noncomputable def leaf3583Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi237InputQChi innerPair304Input
    leaf3583InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3583LowerChecked :
    lowerCheck 24 leaf3583Box leaf3583Inputs = true := by
  rfl'

private theorem leaf3583CoversExact : CoversExact 8
    leaf3583Box leaf3583Certificate leaf3583InnerLog leaf3583Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi237RoundedFacts
    innerPair304RoundedFacts leaf3583RoundedFacts (by rfl)

private theorem leaf3583FlatSound : Sound leaf3583Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3583CertificateValid
    leaf3583InnerLogValid leaf3583CoversExact leaf3583LowerChecked

private noncomputable def leaf3584Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (121/512), chiHi := (61/256) }

private noncomputable def leaf3584Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484403/2147483648) }, vSqrt := { lower := (65527/65536), upper := (9162461457/9162063872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4169439987/2147483648) }, upper := { exponent := 0, mantissa := (125/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi238LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (18324525329/18324127744) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3584InnerLog : WideLogData :=
  innerPair109Data

set_option maxRecDepth 1000000 in
private theorem leaf3584LocalValidity :
    LeafFacts leaf3584Box leaf3584Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3584Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (9162461457/9162063872) }) = true
      norm_num [leaf3584Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3584CertificateValid :
    WideCertificateValid leaf3584Box leaf3584Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi238ValidityFacts
    leaf3584LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3584CoverageChecked :
    coverageCheck (innerAD leaf3584Box) leaf3584InnerLog = true := by
  rfl'

private theorem leaf3584InnerLogValid :
    leaf3584InnerLog.Valid 8 (innerAD leaf3584Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint71PositiveFacts.valid leaf3584CoverageChecked

private noncomputable def leaf3584InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3584InputLogOnePlusV_eq :
    leaf3584InputLogOnePlusV = outerEnclosure 24
      (leaf3584Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3584RoundedFacts : LeafRoundedFacts 8
    leaf3584Certificate.logOnePlusV leaf3584InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3584InputLogOnePlusV_eq }

private noncomputable def leaf3584Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi238InputQChi innerPair109Input
    leaf3584InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3584LowerChecked :
    lowerCheck 24 leaf3584Box leaf3584Inputs = true := by
  rfl'

private theorem leaf3584CoversExact : CoversExact 8
    leaf3584Box leaf3584Certificate leaf3584InnerLog leaf3584Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi238RoundedFacts
    innerPair109RoundedFacts leaf3584RoundedFacts (by rfl)

private theorem leaf3584FlatSound : Sound leaf3584Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3584CertificateValid
    leaf3584InnerLogValid leaf3584CoversExact leaf3584LowerChecked

private noncomputable def leaf3585Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3585Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430858752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2089061233/1073741824) }, upper := { exponent := 0, mantissa := (16097/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867780607/274861717504) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3585InnerLog : WideLogData :=
  innerPair539Data

set_option maxRecDepth 1000000 in
private theorem leaf3585LocalValidity :
    LeafFacts leaf3585Box leaf3585Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3585Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430858752) }) = true
      norm_num [leaf3585Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3585CertificateValid :
    WideCertificateValid leaf3585Box leaf3585Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi192ValidityFacts
    leaf3585LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3585CoverageChecked :
    coverageCheck (innerAD leaf3585Box) leaf3585InnerLog = true := by
  rfl'

private theorem leaf3585InnerLogValid :
    leaf3585InnerLog.Valid 8 (innerAD leaf3585Box) :=
  wideLogDataValid_of_cachedCheck endpoint273PositiveFacts
    endpoint274PositiveFacts.valid leaf3585CoverageChecked

private noncomputable def leaf3585InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3585InputLogOnePlusV_eq :
    leaf3585InputLogOnePlusV = outerEnclosure 24
      (leaf3585Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3585RoundedFacts : LeafRoundedFacts 8
    leaf3585Certificate.logOnePlusV leaf3585InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3585InputLogOnePlusV_eq }

private noncomputable def leaf3585Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi192InputQChi innerPair539Input
    leaf3585InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3585LowerChecked :
    lowerCheck 24 leaf3585Box leaf3585Inputs = true := by
  rfl'

private theorem leaf3585CoversExact : CoversExact 8
    leaf3585Box leaf3585Certificate leaf3585InnerLog leaf3585Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi192RoundedFacts
    innerPair539RoundedFacts leaf3585RoundedFacts (by rfl)

private theorem leaf3585FlatSound : Sound leaf3585Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3585CertificateValid
    leaf3585InnerLogValid leaf3585CoversExact leaf3585LowerChecked

private noncomputable def leaf3586Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (61/256), chiHi := (123/512) }

private noncomputable def leaf3586Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484405/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137430892544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4186150645/2147483648) }, upper := { exponent := 0, mantissa := (251/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi239LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274867814399/274861785088) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3586InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3586LocalValidity :
    LeafFacts leaf3586Box leaf3586Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3586Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137430892544) }) = true
      norm_num [leaf3586Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3586CertificateValid :
    WideCertificateValid leaf3586Box leaf3586Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi239ValidityFacts
    leaf3586LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3586CoverageChecked :
    coverageCheck (innerAD leaf3586Box) leaf3586InnerLog = true := by
  rfl'

private theorem leaf3586InnerLogValid :
    leaf3586InnerLog.Valid 8 (innerAD leaf3586Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3586CoverageChecked

private noncomputable def leaf3586InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3586InputLogOnePlusV_eq :
    leaf3586InputLogOnePlusV = outerEnclosure 24
      (leaf3586Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3586RoundedFacts : LeafRoundedFacts 8
    leaf3586Certificate.logOnePlusV leaf3586InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3586InputLogOnePlusV_eq }

private noncomputable def leaf3586Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi239InputQChi innerPair108Input
    leaf3586InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3586LowerChecked :
    lowerCheck 24 leaf3586Box leaf3586Inputs = true := by
  rfl'

private theorem leaf3586CoversExact : CoversExact 8
    leaf3586Box leaf3586Certificate leaf3586InnerLog leaf3586Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi239RoundedFacts
    innerPair108RoundedFacts leaf3586RoundedFacts (by rfl)

private theorem leaf3586FlatSound : Sound leaf3586Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3586CertificateValid
    leaf3586InnerLogValid leaf3586CoversExact leaf3586LowerChecked

private noncomputable def leaf3587Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (123/512), chiHi := (31/128) }

private noncomputable def leaf3587Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484407/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137430827008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4202861303/2147483648) }, upper := { exponent := 0, mantissa := (63/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi240LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274867748863/274861654016) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3587InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3587LocalValidity :
    LeafFacts leaf3587Box leaf3587Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3587Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137430827008) }) = true
      norm_num [leaf3587Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3587CertificateValid :
    WideCertificateValid leaf3587Box leaf3587Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi240ValidityFacts
    leaf3587LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3587CoverageChecked :
    coverageCheck (innerAD leaf3587Box) leaf3587InnerLog = true := by
  rfl'

private theorem leaf3587InnerLogValid :
    leaf3587InnerLog.Valid 8 (innerAD leaf3587Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3587CoverageChecked

private noncomputable def leaf3587InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3587InputLogOnePlusV_eq :
    leaf3587InputLogOnePlusV = outerEnclosure 24
      (leaf3587Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3587RoundedFacts : LeafRoundedFacts 8
    leaf3587Certificate.logOnePlusV leaf3587InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3587InputLogOnePlusV_eq }

private noncomputable def leaf3587Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi240InputQChi innerPair108Input
    leaf3587InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3587LowerChecked :
    lowerCheck 24 leaf3587Box leaf3587Inputs = true := by
  rfl'

private theorem leaf3587CoversExact : CoversExact 8
    leaf3587Box leaf3587Certificate leaf3587InnerLog leaf3587Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi240RoundedFacts
    innerPair108RoundedFacts leaf3587RoundedFacts (by rfl)

private theorem leaf3587FlatSound : Sound leaf3587Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3587CertificateValid
    leaf3587InnerLogValid leaf3587CoversExact leaf3587LowerChecked

private noncomputable def leaf3588Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3588Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742455/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430792704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2097580395/1073741824) }, upper := { exponent := 0, mantissa := (32323/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867714559/274861585408) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3588InnerLog : WideLogData :=
  innerPair239Data

set_option maxRecDepth 1000000 in
private theorem leaf3588LocalValidity :
    LeafFacts leaf3588Box leaf3588Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3588Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430792704) }) = true
      norm_num [leaf3588Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3588CertificateValid :
    WideCertificateValid leaf3588Box leaf3588Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi189ValidityFacts
    leaf3588LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3588CoverageChecked :
    coverageCheck (innerAD leaf3588Box) leaf3588InnerLog = true := by
  rfl'

private theorem leaf3588InnerLogValid :
    leaf3588InnerLog.Valid 8 (innerAD leaf3588Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint275PositiveFacts.valid leaf3588CoverageChecked

private noncomputable def leaf3588InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3588InputLogOnePlusV_eq :
    leaf3588InputLogOnePlusV = outerEnclosure 24
      (leaf3588Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3588RoundedFacts : LeafRoundedFacts 8
    leaf3588Certificate.logOnePlusV leaf3588InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3588InputLogOnePlusV_eq }

private noncomputable def leaf3588Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi189InputQChi innerPair239Input
    leaf3588InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3588LowerChecked :
    lowerCheck 24 leaf3588Box leaf3588Inputs = true := by
  rfl'

private theorem leaf3588CoversExact : CoversExact 8
    leaf3588Box leaf3588Certificate leaf3588InnerLog leaf3588Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi189RoundedFacts
    innerPair239RoundedFacts leaf3588RoundedFacts (by rfl)

private theorem leaf3588FlatSound : Sound leaf3588Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3588CertificateValid
    leaf3588InnerLogValid leaf3588CoversExact leaf3588LowerChecked

private noncomputable def leaf3589Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3589Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430760448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2101643377/1073741824) }, upper := { exponent := 0, mantissa := (16193/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867682303/274861520896) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3589InnerLog : WideLogData :=
  innerPair530Data

set_option maxRecDepth 1000000 in
private theorem leaf3589LocalValidity :
    LeafFacts leaf3589Box leaf3589Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3589Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430760448) }) = true
      norm_num [leaf3589Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3589CertificateValid :
    WideCertificateValid leaf3589Box leaf3589Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi189ValidityFacts
    leaf3589LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3589CoverageChecked :
    coverageCheck (innerAD leaf3589Box) leaf3589InnerLog = true := by
  rfl'

private theorem leaf3589InnerLogValid :
    leaf3589InnerLog.Valid 8 (innerAD leaf3589Box) :=
  wideLogDataValid_of_cachedCheck endpoint266PositiveFacts
    endpoint276PositiveFacts.valid leaf3589CoverageChecked

private noncomputable def leaf3589InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629457/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3589InputLogOnePlusV_eq :
    leaf3589InputLogOnePlusV = outerEnclosure 24
      (leaf3589Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3589RoundedFacts : LeafRoundedFacts 8
    leaf3589Certificate.logOnePlusV leaf3589InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3589InputLogOnePlusV_eq }

private noncomputable def leaf3589Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi189InputQChi innerPair530Input
    leaf3589InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3589LowerChecked :
    lowerCheck 24 leaf3589Box leaf3589Inputs = true := by
  rfl'

private theorem leaf3589CoversExact : CoversExact 8
    leaf3589Box leaf3589Certificate leaf3589InnerLog leaf3589Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi189RoundedFacts
    innerPair530RoundedFacts leaf3589RoundedFacts (by rfl)

private theorem leaf3589FlatSound : Sound leaf3589Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3589CertificateValid
    leaf3589InnerLogValid leaf3589CoversExact leaf3589LowerChecked

private noncomputable def leaf3590Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3590Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742457/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810221056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2114094457/1073741824) }, upper := { exponent := 0, mantissa := (509/256) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622528341/91620442112) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3590InnerLog : WideLogData :=
  innerPair320Data

set_option maxRecDepth 1000000 in
private theorem leaf3590LocalValidity :
    LeafFacts leaf3590Box leaf3590Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3590Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810221056) }) = true
      norm_num [leaf3590Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3590CertificateValid :
    WideCertificateValid leaf3590Box leaf3590Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi190ValidityFacts
    leaf3590LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3590CoverageChecked :
    coverageCheck (innerAD leaf3590Box) leaf3590InnerLog = true := by
  rfl'

private theorem leaf3590InnerLogValid :
    leaf3590InnerLog.Valid 8 (innerAD leaf3590Box) :=
  wideLogDataValid_of_cachedCheck endpoint85PositiveFacts
    endpoint277PositiveFacts.valid leaf3590CoverageChecked

private noncomputable def leaf3590InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629463/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3590InputLogOnePlusV_eq :
    leaf3590InputLogOnePlusV = outerEnclosure 24
      (leaf3590Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3590RoundedFacts : LeafRoundedFacts 8
    leaf3590Certificate.logOnePlusV leaf3590InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3590InputLogOnePlusV_eq }

private noncomputable def leaf3590Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi190InputQChi innerPair320Input
    leaf3590InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3590LowerChecked :
    lowerCheck 24 leaf3590Box leaf3590Inputs = true := by
  rfl'

private theorem leaf3590CoversExact : CoversExact 8
    leaf3590Box leaf3590Certificate leaf3590InnerLog leaf3590Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi190RoundedFacts
    innerPair320RoundedFacts leaf3590RoundedFacts (by rfl)

private theorem leaf3590FlatSound : Sound leaf3590Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3590CertificateValid
    leaf3590InnerLogValid leaf3590CoversExact leaf3590LowerChecked

private noncomputable def leaf3591Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3591Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9816773193/9816473600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2118222971/1073741824) }, upper := { exponent := 0, mantissa := (255/128) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (19633246793/19632947200) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3591InnerLog : WideLogData :=
  innerPair536Data

set_option maxRecDepth 1000000 in
private theorem leaf3591LocalValidity :
    LeafFacts leaf3591Box leaf3591Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3591Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9816773193/9816473600) }) = true
      norm_num [leaf3591Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3591CertificateValid :
    WideCertificateValid leaf3591Box leaf3591Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi190ValidityFacts
    leaf3591LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3591CoverageChecked :
    coverageCheck (innerAD leaf3591Box) leaf3591InnerLog = true := by
  rfl'

private theorem leaf3591InnerLogValid :
    leaf3591InnerLog.Valid 8 (innerAD leaf3591Box) :=
  wideLogDataValid_of_cachedCheck endpoint269PositiveFacts
    endpoint278PositiveFacts.valid leaf3591CoverageChecked

private noncomputable def leaf3591InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3591InputLogOnePlusV_eq :
    leaf3591InputLogOnePlusV = outerEnclosure 24
      (leaf3591Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3591RoundedFacts : LeafRoundedFacts 8
    leaf3591Certificate.logOnePlusV leaf3591InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3591InputLogOnePlusV_eq }

private noncomputable def leaf3591Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi190InputQChi innerPair536Input
    leaf3591InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3591LowerChecked :
    lowerCheck 24 leaf3591Box leaf3591Inputs = true := by
  rfl'

private theorem leaf3591CoversExact : CoversExact 8
    leaf3591Box leaf3591Certificate leaf3591InnerLog leaf3591Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi190RoundedFacts
    innerPair536RoundedFacts leaf3591RoundedFacts (by rfl)

private theorem leaf3591FlatSound : Sound leaf3591Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3591CertificateValid
    leaf3591InnerLogValid leaf3591CoversExact leaf3591LowerChecked

private noncomputable def leaf3592Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3592Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742459/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430728192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2105706359/1073741824) }, upper := { exponent := 0, mantissa := (32449/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867650047/274861456384) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3592InnerLog : WideLogData :=
  innerPair315Data

set_option maxRecDepth 1000000 in
private theorem leaf3592LocalValidity :
    LeafFacts leaf3592Box leaf3592Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3592Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430728192) }) = true
      norm_num [leaf3592Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3592CertificateValid :
    WideCertificateValid leaf3592Box leaf3592Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi189ValidityFacts
    leaf3592LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3592CoverageChecked :
    coverageCheck (innerAD leaf3592Box) leaf3592InnerLog = true := by
  rfl'

private theorem leaf3592InnerLogValid :
    leaf3592InnerLog.Valid 8 (innerAD leaf3592Box) :=
  wideLogDataValid_of_cachedCheck endpoint83PositiveFacts
    endpoint279PositiveFacts.valid leaf3592CoverageChecked

private noncomputable def leaf3592InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3592InputLogOnePlusV_eq :
    leaf3592InputLogOnePlusV = outerEnclosure 24
      (leaf3592Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3592RoundedFacts : LeafRoundedFacts 8
    leaf3592Certificate.logOnePlusV leaf3592InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3592InputLogOnePlusV_eq }

private noncomputable def leaf3592Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi189InputQChi innerPair315Input
    leaf3592InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3592LowerChecked :
    lowerCheck 24 leaf3592Box leaf3592Inputs = true := by
  rfl'

private theorem leaf3592CoversExact : CoversExact 8
    leaf3592Box leaf3592Certificate leaf3592InnerLog leaf3592Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi189RoundedFacts
    innerPair315RoundedFacts leaf3592RoundedFacts (by rfl)

private theorem leaf3592FlatSound : Sound leaf3592Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3592CertificateValid
    leaf3592InnerLogValid leaf3592CoversExact leaf3592LowerChecked

private noncomputable def leaf3593Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3593Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742461/1073741824) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137430695936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2109769341/1073741824) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274867617791/274861391872) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3593InnerLog : WideLogData :=
  innerPair238Data

set_option maxRecDepth 1000000 in
private theorem leaf3593LocalValidity :
    LeafFacts leaf3593Box leaf3593Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3593Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137430695936) }) = true
      norm_num [leaf3593Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3593CertificateValid :
    WideCertificateValid leaf3593Box leaf3593Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi189ValidityFacts
    leaf3593LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3593CoverageChecked :
    coverageCheck (innerAD leaf3593Box) leaf3593InnerLog = true := by
  rfl'

private theorem leaf3593InnerLogValid :
    leaf3593InnerLog.Valid 8 (innerAD leaf3593Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint267PositiveFacts.valid leaf3593CoverageChecked

private noncomputable def leaf3593InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3593InputLogOnePlusV_eq :
    leaf3593InputLogOnePlusV = outerEnclosure 24
      (leaf3593Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3593RoundedFacts : LeafRoundedFacts 8
    leaf3593Certificate.logOnePlusV leaf3593InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3593InputLogOnePlusV_eq }

private noncomputable def leaf3593Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi189InputQChi innerPair238Input
    leaf3593InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3593LowerChecked :
    lowerCheck 24 leaf3593Box leaf3593Inputs = true := by
  rfl'

private theorem leaf3593CoversExact : CoversExact 8
    leaf3593Box leaf3593Certificate leaf3593InnerLog leaf3593Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi189RoundedFacts
    innerPair238RoundedFacts leaf3593RoundedFacts (by rfl)

private theorem leaf3593FlatSound : Sound leaf3593Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3593CertificateValid
    leaf3593InnerLogValid leaf3593CoversExact leaf3593LowerChecked

private noncomputable def leaf3594Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3594Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742461/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68717412351/68715298816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2122351485/1073741824) }, upper := { exponent := 0, mantissa := (511/256) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137432711167/137430597632) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3594InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3594LocalValidity :
    LeafFacts leaf3594Box leaf3594Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3594Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68717412351/68715298816) }) = true
      norm_num [leaf3594Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3594CertificateValid :
    WideCertificateValid leaf3594Box leaf3594Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi190ValidityFacts
    leaf3594LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3594CoverageChecked :
    coverageCheck (innerAD leaf3594Box) leaf3594InnerLog = true := by
  rfl'

private theorem leaf3594InnerLogValid :
    leaf3594InnerLog.Valid 8 (innerAD leaf3594Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3594CoverageChecked

private noncomputable def leaf3594InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3594InputLogOnePlusV_eq :
    leaf3594InputLogOnePlusV = outerEnclosure 24
      (leaf3594Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3594RoundedFacts : LeafRoundedFacts 8
    leaf3594Certificate.logOnePlusV leaf3594InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3594InputLogOnePlusV_eq }

private noncomputable def leaf3594Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi190InputQChi innerPair108Input
    leaf3594InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3594LowerChecked :
    lowerCheck 24 leaf3594Box leaf3594Inputs = true := by
  rfl'

private theorem leaf3594CoversExact : CoversExact 8
    leaf3594Box leaf3594Certificate leaf3594InnerLog leaf3594Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi190RoundedFacts
    innerPair108RoundedFacts leaf3594RoundedFacts (by rfl)

private theorem leaf3594FlatSound : Sound leaf3594Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3594CertificateValid
    leaf3594InnerLogValid leaf3594CoversExact leaf3594LowerChecked

private noncomputable def leaf3595Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3595Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (1073742463/1073741824) }, vSqrt := { lower := (65527/65536), upper := (532693119/532676608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2126479999/1073741824) }, upper := { exponent := 1, mantissa := (1) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1065369727/1065353216) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3595InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3595LocalValidity :
    LeafFacts leaf3595Box leaf3595Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3595Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (532693119/532676608) }) = true
      norm_num [leaf3595Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3595CertificateValid :
    WideCertificateValid leaf3595Box leaf3595Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi190ValidityFacts
    leaf3595LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3595CoverageChecked :
    coverageCheck (innerAD leaf3595Box) leaf3595InnerLog = true := by
  rfl'

private theorem leaf3595InnerLogValid :
    leaf3595InnerLog.Valid 8 (innerAD leaf3595Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3595CoverageChecked

private noncomputable def leaf3595InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3595InputLogOnePlusV_eq :
    leaf3595InputLogOnePlusV = outerEnclosure 24
      (leaf3595Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3595RoundedFacts : LeafRoundedFacts 8
    leaf3595Certificate.logOnePlusV leaf3595InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3595InputLogOnePlusV_eq }

private noncomputable def leaf3595Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi190InputQChi innerPair108Input
    leaf3595InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3595LowerChecked :
    lowerCheck 24 leaf3595Box leaf3595Inputs = true := by
  rfl'

private theorem leaf3595CoversExact : CoversExact 8
    leaf3595Box leaf3595Certificate leaf3595InnerLog leaf3595Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi190RoundedFacts
    innerPair108RoundedFacts leaf3595RoundedFacts (by rfl)

private theorem leaf3595FlatSound : Sound leaf3595Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3595CertificateValid
    leaf3595InnerLogValid leaf3595CoversExact leaf3595LowerChecked

private noncomputable def component73Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node0_sound : Sound component73Node0Box :=
  sound_of_literal_split component73Node0Box leaf3561Box leaf3562Box
    .k (249/64) (by rfl) (by rfl)
    leaf3561FlatSound leaf3562FlatSound

private noncomputable def component73Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node1_sound : Sound component73Node1Box :=
  sound_of_literal_split component73Node1Box leaf3563Box leaf3564Box
    .k (249/64) (by rfl) (by rfl)
    leaf3563FlatSound leaf3564FlatSound

private noncomputable def component73Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node2_sound : Sound component73Node2Box :=
  sound_of_literal_split component73Node2Box component73Node0Box component73Node1Box
    .chi (61/256) (by rfl) (by rfl)
    component73Node0_sound component73Node1_sound

private noncomputable def component73Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node3_sound : Sound component73Node3Box :=
  sound_of_literal_split component73Node3Box leaf3565Box leaf3566Box
    .k (251/64) (by rfl) (by rfl)
    leaf3565FlatSound leaf3566FlatSound

private noncomputable def component73Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node4_sound : Sound component73Node4Box :=
  sound_of_literal_split component73Node4Box leaf3567Box leaf3568Box
    .k (251/64) (by rfl) (by rfl)
    leaf3567FlatSound leaf3568FlatSound

private noncomputable def component73Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node5_sound : Sound component73Node5Box :=
  sound_of_literal_split component73Node5Box component73Node3Box component73Node4Box
    .chi (61/256) (by rfl) (by rfl)
    component73Node3_sound component73Node4_sound

private noncomputable def component73Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node6_sound : Sound component73Node6Box :=
  sound_of_literal_split component73Node6Box component73Node2Box component73Node5Box
    .k (125/32) (by rfl) (by rfl)
    component73Node2_sound component73Node5_sound

private noncomputable def component73Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node7_sound : Sound component73Node7Box :=
  sound_of_literal_split component73Node7Box leaf3569Box leaf3570Box
    .k (249/64) (by rfl) (by rfl)
    leaf3569FlatSound leaf3570FlatSound

private noncomputable def component73Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node8_sound : Sound component73Node8Box :=
  sound_of_literal_split component73Node8Box leaf3571Box leaf3572Box
    .k (249/64) (by rfl) (by rfl)
    leaf3571FlatSound leaf3572FlatSound

private noncomputable def component73Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node9_sound : Sound component73Node9Box :=
  sound_of_literal_split component73Node9Box component73Node7Box component73Node8Box
    .chi (63/256) (by rfl) (by rfl)
    component73Node7_sound component73Node8_sound

private noncomputable def component73Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node10_sound : Sound component73Node10Box :=
  sound_of_literal_split component73Node10Box leaf3573Box leaf3574Box
    .k (251/64) (by rfl) (by rfl)
    leaf3573FlatSound leaf3574FlatSound

private noncomputable def component73Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node11_sound : Sound component73Node11Box :=
  sound_of_literal_split component73Node11Box leaf3575Box leaf3576Box
    .k (251/64) (by rfl) (by rfl)
    leaf3575FlatSound leaf3576FlatSound

private noncomputable def component73Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node12_sound : Sound component73Node12Box :=
  sound_of_literal_split component73Node12Box component73Node10Box component73Node11Box
    .chi (63/256) (by rfl) (by rfl)
    component73Node10_sound component73Node11_sound

private noncomputable def component73Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node13_sound : Sound component73Node13Box :=
  sound_of_literal_split component73Node13Box component73Node9Box component73Node12Box
    .k (125/32) (by rfl) (by rfl)
    component73Node9_sound component73Node12_sound

private noncomputable def component73Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node14_sound : Sound component73Node14Box :=
  sound_of_literal_split component73Node14Box component73Node6Box component73Node13Box
    .chi (31/128) (by rfl) (by rfl)
    component73Node6_sound component73Node13_sound

private noncomputable def component73Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node15_sound : Sound component73Node15Box :=
  sound_of_literal_split component73Node15Box leaf3577Box leaf3578Box
    .k (253/64) (by rfl) (by rfl)
    leaf3577FlatSound leaf3578FlatSound

private noncomputable def component73Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node16_sound : Sound component73Node16Box :=
  sound_of_literal_split component73Node16Box leaf3579Box leaf3580Box
    .k (253/64) (by rfl) (by rfl)
    leaf3579FlatSound leaf3580FlatSound

private noncomputable def component73Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node17_sound : Sound component73Node17Box :=
  sound_of_literal_split component73Node17Box component73Node15Box component73Node16Box
    .chi (61/256) (by rfl) (by rfl)
    component73Node15_sound component73Node16_sound

private noncomputable def component73Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node18_sound : Sound component73Node18Box :=
  sound_of_literal_split component73Node18Box leaf3581Box leaf3582Box
    .chi (121/512) (by rfl) (by rfl)
    leaf3581FlatSound leaf3582FlatSound

private noncomputable def component73Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node19_sound : Sound component73Node19Box :=
  sound_of_literal_split component73Node19Box leaf3583Box leaf3584Box
    .chi (121/512) (by rfl) (by rfl)
    leaf3583FlatSound leaf3584FlatSound

private noncomputable def component73Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node20_sound : Sound component73Node20Box :=
  sound_of_literal_split component73Node20Box component73Node18Box component73Node19Box
    .k (255/64) (by rfl) (by rfl)
    component73Node18_sound component73Node19_sound

private noncomputable def component73Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node21_sound : Sound component73Node21Box :=
  sound_of_literal_split component73Node21Box leaf3586Box leaf3587Box
    .chi (123/512) (by rfl) (by rfl)
    leaf3586FlatSound leaf3587FlatSound

private noncomputable def component73Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node22_sound : Sound component73Node22Box :=
  sound_of_literal_split component73Node22Box leaf3585Box component73Node21Box
    .k (255/64) (by rfl) (by rfl)
    leaf3585FlatSound component73Node21_sound

private noncomputable def component73Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node23_sound : Sound component73Node23Box :=
  sound_of_literal_split component73Node23Box component73Node20Box component73Node22Box
    .chi (61/256) (by rfl) (by rfl)
    component73Node20_sound component73Node22_sound

private noncomputable def component73Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component73Node24_sound : Sound component73Node24Box :=
  sound_of_literal_split component73Node24Box component73Node17Box component73Node23Box
    .k (127/32) (by rfl) (by rfl)
    component73Node17_sound component73Node23_sound

private noncomputable def component73Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node25_sound : Sound component73Node25Box :=
  sound_of_literal_split component73Node25Box leaf3588Box leaf3589Box
    .k (253/64) (by rfl) (by rfl)
    leaf3588FlatSound leaf3589FlatSound

private noncomputable def component73Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node26_sound : Sound component73Node26Box :=
  sound_of_literal_split component73Node26Box leaf3590Box leaf3591Box
    .k (253/64) (by rfl) (by rfl)
    leaf3590FlatSound leaf3591FlatSound

private noncomputable def component73Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node27_sound : Sound component73Node27Box :=
  sound_of_literal_split component73Node27Box component73Node25Box component73Node26Box
    .chi (63/256) (by rfl) (by rfl)
    component73Node25_sound component73Node26_sound

private noncomputable def component73Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component73Node28_sound : Sound component73Node28Box :=
  sound_of_literal_split component73Node28Box leaf3592Box leaf3593Box
    .k (255/64) (by rfl) (by rfl)
    leaf3592FlatSound leaf3593FlatSound

private noncomputable def component73Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node29_sound : Sound component73Node29Box :=
  sound_of_literal_split component73Node29Box leaf3594Box leaf3595Box
    .k (255/64) (by rfl) (by rfl)
    leaf3594FlatSound leaf3595FlatSound

private noncomputable def component73Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node30_sound : Sound component73Node30Box :=
  sound_of_literal_split component73Node30Box component73Node28Box component73Node29Box
    .chi (63/256) (by rfl) (by rfl)
    component73Node28_sound component73Node29_sound

private noncomputable def component73Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node31_sound : Sound component73Node31Box :=
  sound_of_literal_split component73Node31Box component73Node27Box component73Node30Box
    .k (127/32) (by rfl) (by rfl)
    component73Node27_sound component73Node30_sound

private noncomputable def component73Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component73Node32_sound : Sound component73Node32Box :=
  sound_of_literal_split component73Node32Box component73Node24Box component73Node31Box
    .chi (31/128) (by rfl) (by rfl)
    component73Node24_sound component73Node31_sound

noncomputable def component73Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component73_sound : Sound component73Box :=
  sound_of_literal_split component73Box component73Node14Box component73Node32Box
    .k (63/16) (by rfl) (by rfl)
    component73Node14_sound component73Node32_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
