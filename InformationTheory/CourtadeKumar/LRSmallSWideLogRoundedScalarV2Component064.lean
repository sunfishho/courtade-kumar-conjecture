import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf3029Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3029Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433308672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1778308575/1073741824) }, upper := { exponent := 0, mantissa := (27409/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870230527/274866617344) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3029InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3029LocalValidity :
    LeafFacts leaf3029Box leaf3029Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3029Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433308672) }) = true
      norm_num [leaf3029Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3029CertificateValid :
    WideCertificateValid leaf3029Box leaf3029Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi187ValidityFacts
    leaf3029LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3029CoverageChecked :
    coverageCheck (innerAD leaf3029Box) leaf3029InnerLog = true := by
  rfl'

private theorem leaf3029InnerLogValid :
    leaf3029InnerLog.Valid 8 (innerAD leaf3029Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3029CoverageChecked

private noncomputable def leaf3029InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3029InputLogOnePlusV_eq :
    leaf3029InputLogOnePlusV = outerEnclosure 24
      (leaf3029Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3029RoundedFacts : LeafRoundedFacts 8
    leaf3029Certificate.logOnePlusV leaf3029InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3029InputLogOnePlusV_eq }

private noncomputable def leaf3029Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi187InputQChi innerPair56Input
    leaf3029InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3029LowerChecked :
    lowerCheck 24 leaf3029Box leaf3029Inputs = true := by
  rfl'

private theorem leaf3029CoversExact : CoversExact 8
    leaf3029Box leaf3029Certificate leaf3029InnerLog leaf3029Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf3029RoundedFacts (by rfl)

private theorem leaf3029FlatSound : Sound leaf3029Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3029CertificateValid
    leaf3029InnerLogValid leaf3029CoversExact leaf3029LowerChecked

private noncomputable def leaf3030Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3030Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811094528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1781454109/1073741824) }, upper := { exponent := 0, mantissa := (13729/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623401813/91622189056) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3030InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3030LocalValidity :
    LeafFacts leaf3030Box leaf3030Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3030Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811094528) }) = true
      norm_num [leaf3030Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3030CertificateValid :
    WideCertificateValid leaf3030Box leaf3030Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi187ValidityFacts
    leaf3030LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3030CoverageChecked :
    coverageCheck (innerAD leaf3030Box) leaf3030InnerLog = true := by
  rfl'

private theorem leaf3030InnerLogValid :
    leaf3030InnerLog.Valid 8 (innerAD leaf3030Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3030CoverageChecked

private noncomputable def leaf3030InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3030InputLogOnePlusV_eq :
    leaf3030InputLogOnePlusV = outerEnclosure 24
      (leaf3030Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3030RoundedFacts : LeafRoundedFacts 8
    leaf3030Certificate.logOnePlusV leaf3030InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3030InputLogOnePlusV_eq }

private noncomputable def leaf3030Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi187InputQChi innerPair56Input
    leaf3030InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3030LowerChecked :
    lowerCheck 24 leaf3030Box leaf3030Inputs = true := by
  rfl'

private theorem leaf3030CoversExact : CoversExact 8
    leaf3030Box leaf3030Certificate leaf3030InnerLog leaf3030Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf3030RoundedFacts (by rfl)

private theorem leaf3030FlatSound : Sound leaf3030Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3030CertificateValid
    leaf3030InnerLogValid leaf3030CoversExact leaf3030LowerChecked

private noncomputable def leaf3031Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3031Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433193472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1792987741/1073741824) }, upper := { exponent := 0, mantissa := (13817/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870115327/274866386944) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3031InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3031LocalValidity :
    LeafFacts leaf3031Box leaf3031Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3031Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433193472) }) = true
      norm_num [leaf3031Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3031CertificateValid :
    WideCertificateValid leaf3031Box leaf3031Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi188ValidityFacts
    leaf3031LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3031CoverageChecked :
    coverageCheck (innerAD leaf3031Box) leaf3031InnerLog = true := by
  rfl'

private theorem leaf3031InnerLogValid :
    leaf3031InnerLog.Valid 8 (innerAD leaf3031Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3031CoverageChecked

private noncomputable def leaf3031InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3031InputLogOnePlusV_eq :
    leaf3031InputLogOnePlusV = outerEnclosure 24
      (leaf3031Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3031RoundedFacts : LeafRoundedFacts 8
    leaf3031Certificate.logOnePlusV leaf3031InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3031InputLogOnePlusV_eq }

private noncomputable def leaf3031Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi188InputQChi innerPair56Input
    leaf3031InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3031LowerChecked :
    lowerCheck 24 leaf3031Box leaf3031Inputs = true := by
  rfl'

private theorem leaf3031CoversExact : CoversExact 8
    leaf3031Box leaf3031Certificate leaf3031InnerLog leaf3031Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf3031RoundedFacts (by rfl)

private theorem leaf3031FlatSound : Sound leaf3031Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3031CertificateValid
    leaf3031InnerLogValid leaf3031CoversExact leaf3031LowerChecked

private noncomputable def leaf3032Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3032Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433167872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1796198807/1073741824) }, upper := { exponent := 0, mantissa := (6921/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870089727/274866335744) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3032InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3032LocalValidity :
    LeafFacts leaf3032Box leaf3032Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3032Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433167872) }) = true
      norm_num [leaf3032Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3032CertificateValid :
    WideCertificateValid leaf3032Box leaf3032Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi188ValidityFacts
    leaf3032LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3032CoverageChecked :
    coverageCheck (innerAD leaf3032Box) leaf3032InnerLog = true := by
  rfl'

private theorem leaf3032InnerLogValid :
    leaf3032InnerLog.Valid 8 (innerAD leaf3032Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3032CoverageChecked

private noncomputable def leaf3032InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3032InputLogOnePlusV_eq :
    leaf3032InputLogOnePlusV = outerEnclosure 24
      (leaf3032Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3032RoundedFacts : LeafRoundedFacts 8
    leaf3032Certificate.logOnePlusV leaf3032InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3032InputLogOnePlusV_eq }

private noncomputable def leaf3032Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi188InputQChi innerPair57Input
    leaf3032InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3032LowerChecked :
    lowerCheck 24 leaf3032Box leaf3032Inputs = true := by
  rfl'

private theorem leaf3032CoversExact : CoversExact 8
    leaf3032Box leaf3032Certificate leaf3032InnerLog leaf3032Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi188RoundedFacts
    innerPair57RoundedFacts leaf3032RoundedFacts (by rfl)

private theorem leaf3032FlatSound : Sound leaf3032Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3032CertificateValid
    leaf3032InnerLogValid leaf3032CoversExact leaf3032LowerChecked

private noncomputable def leaf3033Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3033Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433258496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1784599643/1073741824) }, upper := { exponent := 0, mantissa := (27507/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870180351/274866516992) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3033InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3033LocalValidity :
    LeafFacts leaf3033Box leaf3033Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3033Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433258496) }) = true
      norm_num [leaf3033Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3033CertificateValid :
    WideCertificateValid leaf3033Box leaf3033Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi187ValidityFacts
    leaf3033LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3033CoverageChecked :
    coverageCheck (innerAD leaf3033Box) leaf3033InnerLog = true := by
  rfl'

private theorem leaf3033InnerLogValid :
    leaf3033InnerLog.Valid 8 (innerAD leaf3033Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3033CoverageChecked

private noncomputable def leaf3033InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3033InputLogOnePlusV_eq :
    leaf3033InputLogOnePlusV = outerEnclosure 24
      (leaf3033Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3033RoundedFacts : LeafRoundedFacts 8
    leaf3033Certificate.logOnePlusV leaf3033InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3033InputLogOnePlusV_eq }

private noncomputable def leaf3033Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi187InputQChi innerPair56Input
    leaf3033InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3033LowerChecked :
    lowerCheck 24 leaf3033Box leaf3033Inputs = true := by
  rfl'

private theorem leaf3033CoversExact : CoversExact 8
    leaf3033Box leaf3033Certificate leaf3033InnerLog leaf3033Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf3033RoundedFacts (by rfl)

private theorem leaf3033FlatSound : Sound leaf3033Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3033CertificateValid
    leaf3033InnerLogValid leaf3033CoversExact leaf3033LowerChecked

private noncomputable def leaf3034Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3034Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433233408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1787745177/1073741824) }, upper := { exponent := 0, mantissa := (6889/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870155263/274866466816) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3034InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3034LocalValidity :
    LeafFacts leaf3034Box leaf3034Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3034Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433233408) }) = true
      norm_num [leaf3034Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3034CertificateValid :
    WideCertificateValid leaf3034Box leaf3034Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi187ValidityFacts
    leaf3034LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3034CoverageChecked :
    coverageCheck (innerAD leaf3034Box) leaf3034InnerLog = true := by
  rfl'

private theorem leaf3034InnerLogValid :
    leaf3034InnerLog.Valid 8 (innerAD leaf3034Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3034CoverageChecked

private noncomputable def leaf3034InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3034InputLogOnePlusV_eq :
    leaf3034InputLogOnePlusV = outerEnclosure 24
      (leaf3034Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3034RoundedFacts : LeafRoundedFacts 8
    leaf3034Certificate.logOnePlusV leaf3034InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3034InputLogOnePlusV_eq }

private noncomputable def leaf3034Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi187InputQChi innerPair56Input
    leaf3034InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3034LowerChecked :
    lowerCheck 24 leaf3034Box leaf3034Inputs = true := by
  rfl'

private theorem leaf3034CoversExact : CoversExact 8
    leaf3034Box leaf3034Certificate leaf3034InnerLog leaf3034Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf3034RoundedFacts (by rfl)

private theorem leaf3034FlatSound : Sound leaf3034Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3034CertificateValid
    leaf3034InnerLogValid leaf3034CoversExact leaf3034LowerChecked

private noncomputable def leaf3035Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3035Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811047424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1799409873/1073741824) }, upper := { exponent := 0, mantissa := (13867/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623354709/91622094848) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3035InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3035LocalValidity :
    LeafFacts leaf3035Box leaf3035Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3035Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811047424) }) = true
      norm_num [leaf3035Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3035CertificateValid :
    WideCertificateValid leaf3035Box leaf3035Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi188ValidityFacts
    leaf3035LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3035CoverageChecked :
    coverageCheck (innerAD leaf3035Box) leaf3035InnerLog = true := by
  rfl'

private theorem leaf3035InnerLogValid :
    leaf3035InnerLog.Valid 8 (innerAD leaf3035Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3035CoverageChecked

private noncomputable def leaf3035InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3035InputLogOnePlusV_eq :
    leaf3035InputLogOnePlusV = outerEnclosure 24
      (leaf3035Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3035RoundedFacts : LeafRoundedFacts 8
    leaf3035Certificate.logOnePlusV leaf3035InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3035InputLogOnePlusV_eq }

private noncomputable def leaf3035Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi188InputQChi innerPair57Input
    leaf3035InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3035LowerChecked :
    lowerCheck 24 leaf3035Box leaf3035Inputs = true := by
  rfl'

private theorem leaf3035CoversExact : CoversExact 8
    leaf3035Box leaf3035Certificate leaf3035InnerLog leaf3035Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi188RoundedFacts
    innerPair57RoundedFacts leaf3035RoundedFacts (by rfl)

private theorem leaf3035FlatSound : Sound leaf3035Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3035CertificateValid
    leaf3035InnerLogValid leaf3035CoversExact leaf3035LowerChecked

private noncomputable def leaf3036Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3036Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433116672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1802620939/1073741824) }, upper := { exponent := 0, mantissa := (3473/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870038527/274866233344) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3036InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3036LocalValidity :
    LeafFacts leaf3036Box leaf3036Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3036Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433116672) }) = true
      norm_num [leaf3036Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3036CertificateValid :
    WideCertificateValid leaf3036Box leaf3036Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi188ValidityFacts
    leaf3036LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3036CoverageChecked :
    coverageCheck (innerAD leaf3036Box) leaf3036InnerLog = true := by
  rfl'

private theorem leaf3036InnerLogValid :
    leaf3036InnerLog.Valid 8 (innerAD leaf3036Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3036CoverageChecked

private noncomputable def leaf3036InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3036InputLogOnePlusV_eq :
    leaf3036InputLogOnePlusV = outerEnclosure 24
      (leaf3036Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3036RoundedFacts : LeafRoundedFacts 8
    leaf3036Certificate.logOnePlusV leaf3036InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3036InputLogOnePlusV_eq }

private noncomputable def leaf3036Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi188InputQChi innerPair57Input
    leaf3036InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3036LowerChecked :
    lowerCheck 24 leaf3036Box leaf3036Inputs = true := by
  rfl'

private theorem leaf3036CoversExact : CoversExact 8
    leaf3036Box leaf3036Certificate leaf3036InnerLog leaf3036Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi188RoundedFacts
    innerPair57RoundedFacts leaf3036RoundedFacts (by rfl)

private theorem leaf3036FlatSound : Sound leaf3036Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3036CertificateValid
    leaf3036InnerLogValid leaf3036CoversExact leaf3036LowerChecked

private noncomputable def leaf3037Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3037Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433078272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1807666907/1073741824) }, upper := { exponent := 0, mantissa := (27859/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870000127/274866156544) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3037InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3037LocalValidity :
    LeafFacts leaf3037Box leaf3037Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3037Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433078272) }) = true
      norm_num [leaf3037Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3037CertificateValid :
    WideCertificateValid leaf3037Box leaf3037Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi193ValidityFacts
    leaf3037LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3037CoverageChecked :
    coverageCheck (innerAD leaf3037Box) leaf3037InnerLog = true := by
  rfl'

private theorem leaf3037InnerLogValid :
    leaf3037InnerLog.Valid 8 (innerAD leaf3037Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3037CoverageChecked

private noncomputable def leaf3037InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3037InputLogOnePlusV_eq :
    leaf3037InputLogOnePlusV = outerEnclosure 24
      (leaf3037Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3037RoundedFacts : LeafRoundedFacts 8
    leaf3037Certificate.logOnePlusV leaf3037InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3037InputLogOnePlusV_eq }

private noncomputable def leaf3037Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi193InputQChi innerPair57Input
    leaf3037InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3037LowerChecked :
    lowerCheck 24 leaf3037Box leaf3037Inputs = true := by
  rfl'

private theorem leaf3037CoversExact : CoversExact 8
    leaf3037Box leaf3037Certificate leaf3037InnerLog leaf3037Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi193RoundedFacts
    innerPair57RoundedFacts leaf3037RoundedFacts (by rfl)

private theorem leaf3037FlatSound : Sound leaf3037Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3037CertificateValid
    leaf3037InnerLogValid leaf3037CoversExact leaf3037LowerChecked

private noncomputable def leaf3038Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3038Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486610432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1810943505/1073741824) }, upper := { exponent := 0, mantissa := (13955/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973994803/54973220864) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3038InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3038LocalValidity :
    LeafFacts leaf3038Box leaf3038Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3038Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486610432) }) = true
      norm_num [leaf3038Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3038CertificateValid :
    WideCertificateValid leaf3038Box leaf3038Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi193ValidityFacts
    leaf3038LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3038CoverageChecked :
    coverageCheck (innerAD leaf3038Box) leaf3038InnerLog = true := by
  rfl'

private theorem leaf3038InnerLogValid :
    leaf3038InnerLog.Valid 8 (innerAD leaf3038Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3038CoverageChecked

private noncomputable def leaf3038InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3038InputLogOnePlusV_eq :
    leaf3038InputLogOnePlusV = outerEnclosure 24
      (leaf3038Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3038RoundedFacts : LeafRoundedFacts 8
    leaf3038Certificate.logOnePlusV leaf3038InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3038InputLogOnePlusV_eq }

private noncomputable def leaf3038Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi193InputQChi innerPair57Input
    leaf3038InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3038LowerChecked :
    lowerCheck 24 leaf3038Box leaf3038Inputs = true := by
  rfl'

private theorem leaf3038CoversExact : CoversExact 8
    leaf3038Box leaf3038Certificate leaf3038InnerLog leaf3038Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi193RoundedFacts
    innerPair57RoundedFacts leaf3038RoundedFacts (by rfl)

private theorem leaf3038FlatSound : Sound leaf3038Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3038CertificateValid
    leaf3038InnerLogValid leaf3038CoversExact leaf3038LowerChecked

private noncomputable def leaf3039Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3039Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432963072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1822346073/1073741824) }, upper := { exponent := 0, mantissa := (7021/4096) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869884927/274865926144) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3039InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3039LocalValidity :
    LeafFacts leaf3039Box leaf3039Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3039Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432963072) }) = true
      norm_num [leaf3039Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3039CertificateValid :
    WideCertificateValid leaf3039Box leaf3039Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi194ValidityFacts
    leaf3039LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3039CoverageChecked :
    coverageCheck (innerAD leaf3039Box) leaf3039InnerLog = true := by
  rfl'

private theorem leaf3039InnerLogValid :
    leaf3039InnerLog.Valid 8 (innerAD leaf3039Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3039CoverageChecked

private noncomputable def leaf3039InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3039InputLogOnePlusV_eq :
    leaf3039InputLogOnePlusV = outerEnclosure 24
      (leaf3039Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3039RoundedFacts : LeafRoundedFacts 8
    leaf3039Certificate.logOnePlusV leaf3039InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3039InputLogOnePlusV_eq }

private noncomputable def leaf3039Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3039InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3039LowerChecked :
    lowerCheck 24 leaf3039Box leaf3039Inputs = true := by
  rfl'

private theorem leaf3039CoversExact : CoversExact 8
    leaf3039Box leaf3039Certificate leaf3039InnerLog leaf3039Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3039RoundedFacts (by rfl)

private theorem leaf3039FlatSound : Sound leaf3039Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3039CertificateValid
    leaf3039InnerLogValid leaf3039CoversExact leaf3039LowerChecked

private noncomputable def leaf3040Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3040Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270326272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1825688203/1073741824) }, upper := { exponent := 0, mantissa := (3517/2048) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541095367/30540652544) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3040InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3040LocalValidity :
    LeafFacts leaf3040Box leaf3040Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3040Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270326272) }) = true
      norm_num [leaf3040Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3040CertificateValid :
    WideCertificateValid leaf3040Box leaf3040Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi194ValidityFacts
    leaf3040LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3040CoverageChecked :
    coverageCheck (innerAD leaf3040Box) leaf3040InnerLog = true := by
  rfl'

private theorem leaf3040InnerLogValid :
    leaf3040InnerLog.Valid 8 (innerAD leaf3040Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3040CoverageChecked

private noncomputable def leaf3040InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3040InputLogOnePlusV_eq :
    leaf3040InputLogOnePlusV = outerEnclosure 24
      (leaf3040Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3040RoundedFacts : LeafRoundedFacts 8
    leaf3040Certificate.logOnePlusV leaf3040InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3040InputLogOnePlusV_eq }

private noncomputable def leaf3040Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3040InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3040LowerChecked :
    lowerCheck 24 leaf3040Box leaf3040Inputs = true := by
  rfl'

private theorem leaf3040CoversExact : CoversExact 8
    leaf3040Box leaf3040Certificate leaf3040InnerLog leaf3040Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3040RoundedFacts (by rfl)

private theorem leaf3040FlatSound : Sound leaf3040Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3040CertificateValid
    leaf3040InnerLogValid leaf3040CoversExact leaf3040LowerChecked

private noncomputable def leaf3041Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3041Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433026048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1814220103/1073741824) }, upper := { exponent := 0, mantissa := (27961/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869947903/274866052096) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3041InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3041LocalValidity :
    LeafFacts leaf3041Box leaf3041Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3041Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433026048) }) = true
      norm_num [leaf3041Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3041CertificateValid :
    WideCertificateValid leaf3041Box leaf3041Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi193ValidityFacts
    leaf3041LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3041CoverageChecked :
    coverageCheck (innerAD leaf3041Box) leaf3041InnerLog = true := by
  rfl'

private theorem leaf3041InnerLogValid :
    leaf3041InnerLog.Valid 8 (innerAD leaf3041Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3041CoverageChecked

private noncomputable def leaf3041InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3041InputLogOnePlusV_eq :
    leaf3041InputLogOnePlusV = outerEnclosure 24
      (leaf3041Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3041RoundedFacts : LeafRoundedFacts 8
    leaf3041Certificate.logOnePlusV leaf3041InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3041InputLogOnePlusV_eq }

private noncomputable def leaf3041Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3041InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3041LowerChecked :
    lowerCheck 24 leaf3041Box leaf3041Inputs = true := by
  rfl'

private theorem leaf3041CoversExact : CoversExact 8
    leaf3041Box leaf3041Certificate leaf3041InnerLog leaf3041Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3041RoundedFacts (by rfl)

private theorem leaf3041FlatSound : Sound leaf3041Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3041CertificateValid
    leaf3041InnerLogValid leaf3041CoversExact leaf3041LowerChecked

private noncomputable def leaf3042Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3042Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432999936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1817496701/1073741824) }, upper := { exponent := 0, mantissa := (7003/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869921791/274865999872) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3042InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3042LocalValidity :
    LeafFacts leaf3042Box leaf3042Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3042Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432999936) }) = true
      norm_num [leaf3042Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3042CertificateValid :
    WideCertificateValid leaf3042Box leaf3042Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi193ValidityFacts
    leaf3042LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3042CoverageChecked :
    coverageCheck (innerAD leaf3042Box) leaf3042InnerLog = true := by
  rfl'

private theorem leaf3042InnerLogValid :
    leaf3042InnerLog.Valid 8 (innerAD leaf3042Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3042CoverageChecked

private noncomputable def leaf3042InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3042InputLogOnePlusV_eq :
    leaf3042InputLogOnePlusV = outerEnclosure 24
      (leaf3042Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3042RoundedFacts : LeafRoundedFacts 8
    leaf3042Certificate.logOnePlusV leaf3042InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3042InputLogOnePlusV_eq }

private noncomputable def leaf3042Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3042InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3042LowerChecked :
    lowerCheck 24 leaf3042Box leaf3042Inputs = true := by
  rfl'

private theorem leaf3042CoversExact : CoversExact 8
    leaf3042Box leaf3042Certificate leaf3042InnerLog leaf3042Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3042RoundedFacts (by rfl)

private theorem leaf3042FlatSound : Sound leaf3042Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3042CertificateValid
    leaf3042InnerLogValid leaf3042CoversExact leaf3042LowerChecked

private noncomputable def leaf3043Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3043Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432909824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1829030333/1073741824) }, upper := { exponent := 0, mantissa := (7047/4096) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869831679/274865819648) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3043InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3043LocalValidity :
    LeafFacts leaf3043Box leaf3043Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3043Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432909824) }) = true
      norm_num [leaf3043Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3043CertificateValid :
    WideCertificateValid leaf3043Box leaf3043Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi194ValidityFacts
    leaf3043LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3043CoverageChecked :
    coverageCheck (innerAD leaf3043Box) leaf3043InnerLog = true := by
  rfl'

private theorem leaf3043InnerLogValid :
    leaf3043InnerLog.Valid 8 (innerAD leaf3043Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3043CoverageChecked

private noncomputable def leaf3043InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3043InputLogOnePlusV_eq :
    leaf3043InputLogOnePlusV = outerEnclosure 24
      (leaf3043Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3043RoundedFacts : LeafRoundedFacts 8
    leaf3043Certificate.logOnePlusV leaf3043InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3043InputLogOnePlusV_eq }

private noncomputable def leaf3043Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3043InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3043LowerChecked :
    lowerCheck 24 leaf3043Box leaf3043Inputs = true := by
  rfl'

private theorem leaf3043CoversExact : CoversExact 8
    leaf3043Box leaf3043Certificate leaf3043InnerLog leaf3043Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3043RoundedFacts (by rfl)

private theorem leaf3043FlatSound : Sound leaf3043Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3043CertificateValid
    leaf3043InnerLogValid leaf3043CoversExact leaf3043LowerChecked

private noncomputable def leaf3044Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3044Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486576640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1832372463/1073741824) }, upper := { exponent := 0, mantissa := (1765/1024) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973961011/54973153280) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3044InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3044LocalValidity :
    LeafFacts leaf3044Box leaf3044Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3044Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486576640) }) = true
      norm_num [leaf3044Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3044CertificateValid :
    WideCertificateValid leaf3044Box leaf3044Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi194ValidityFacts
    leaf3044LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3044CoverageChecked :
    coverageCheck (innerAD leaf3044Box) leaf3044InnerLog = true := by
  rfl'

private theorem leaf3044InnerLogValid :
    leaf3044InnerLog.Valid 8 (innerAD leaf3044Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3044CoverageChecked

private noncomputable def leaf3044InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3044InputLogOnePlusV_eq :
    leaf3044InputLogOnePlusV = outerEnclosure 24
      (leaf3044Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3044RoundedFacts : LeafRoundedFacts 8
    leaf3044Certificate.logOnePlusV leaf3044InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3044InputLogOnePlusV_eq }

private noncomputable def leaf3044Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3044InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3044LowerChecked :
    lowerCheck 24 leaf3044Box leaf3044Inputs = true := by
  rfl'

private theorem leaf3044CoversExact : CoversExact 8
    leaf3044Box leaf3044Certificate leaf3044InnerLog leaf3044Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3044RoundedFacts (by rfl)

private theorem leaf3044FlatSound : Sound leaf3044Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3044CertificateValid
    leaf3044InnerLogValid leaf3044CoversExact leaf3044LowerChecked

private noncomputable def leaf3045Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3045Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054071296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1790890711/1073741824) }, upper := { exponent := 0, mantissa := (27605/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108225115/6108142592) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3045InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf3045LocalValidity :
    LeafFacts leaf3045Box leaf3045Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3045Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054071296) }) = true
      norm_num [leaf3045Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3045CertificateValid :
    WideCertificateValid leaf3045Box leaf3045Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi187ValidityFacts
    leaf3045LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3045CoverageChecked :
    coverageCheck (innerAD leaf3045Box) leaf3045InnerLog = true := by
  rfl'

private theorem leaf3045InnerLogValid :
    leaf3045InnerLog.Valid 8 (innerAD leaf3045Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf3045CoverageChecked

private noncomputable def leaf3045InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3045InputLogOnePlusV_eq :
    leaf3045InputLogOnePlusV = outerEnclosure 24
      (leaf3045Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3045RoundedFacts : LeafRoundedFacts 8
    leaf3045Certificate.logOnePlusV leaf3045InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3045InputLogOnePlusV_eq }

private noncomputable def leaf3045Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi187InputQChi innerPair56Input
    leaf3045InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3045LowerChecked :
    lowerCheck 24 leaf3045Box leaf3045Inputs = true := by
  rfl'

private theorem leaf3045CoversExact : CoversExact 8
    leaf3045Box leaf3045Certificate leaf3045InnerLog leaf3045Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf3045RoundedFacts (by rfl)

private theorem leaf3045FlatSound : Sound leaf3045Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3045CertificateValid
    leaf3045InnerLogValid leaf3045CoversExact leaf3045LowerChecked

private noncomputable def leaf3046Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3046Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084304896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1794036245/1073741824) }, upper := { exponent := 0, mantissa := (13827/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168829711/16168609792) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3046InnerLog : WideLogData :=
  innerPair173Data

set_option maxRecDepth 1000000 in
private theorem leaf3046LocalValidity :
    LeafFacts leaf3046Box leaf3046Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3046Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084304896) }) = true
      norm_num [leaf3046Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3046CertificateValid :
    WideCertificateValid leaf3046Box leaf3046Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi187ValidityFacts
    leaf3046LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3046CoverageChecked :
    coverageCheck (innerAD leaf3046Box) leaf3046InnerLog = true := by
  rfl'

private theorem leaf3046InnerLogValid :
    leaf3046InnerLog.Valid 8 (innerAD leaf3046Box) :=
  wideLogDataValid_of_cachedCheck endpoint48PositiveFacts
    endpoint20PositiveFacts.valid leaf3046CoverageChecked

private noncomputable def leaf3046InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3046InputLogOnePlusV_eq :
    leaf3046InputLogOnePlusV = outerEnclosure 24
      (leaf3046Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3046RoundedFacts : LeafRoundedFacts 8
    leaf3046Certificate.logOnePlusV leaf3046InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3046InputLogOnePlusV_eq }

private noncomputable def leaf3046Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi187InputQChi innerPair173Input
    leaf3046InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3046LowerChecked :
    lowerCheck 24 leaf3046Box leaf3046Inputs = true := by
  rfl'

private theorem leaf3046CoversExact : CoversExact 8
    leaf3046Box leaf3046Certificate leaf3046InnerLog leaf3046Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi187RoundedFacts
    innerPair173RoundedFacts leaf3046RoundedFacts (by rfl)

private theorem leaf3046FlatSound : Sound leaf3046Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3046CertificateValid
    leaf3046InnerLogValid leaf3046CoversExact leaf3046LowerChecked

private noncomputable def leaf3047Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3047Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433091072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1805832005/1073741824) }, upper := { exponent := 0, mantissa := (13917/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870012927/274866182144) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3047InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3047LocalValidity :
    LeafFacts leaf3047Box leaf3047Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3047Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433091072) }) = true
      norm_num [leaf3047Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3047CertificateValid :
    WideCertificateValid leaf3047Box leaf3047Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi188ValidityFacts
    leaf3047LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3047CoverageChecked :
    coverageCheck (innerAD leaf3047Box) leaf3047InnerLog = true := by
  rfl'

private theorem leaf3047InnerLogValid :
    leaf3047InnerLog.Valid 8 (innerAD leaf3047Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3047CoverageChecked

private noncomputable def leaf3047InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3047InputLogOnePlusV_eq :
    leaf3047InputLogOnePlusV = outerEnclosure 24
      (leaf3047Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3047RoundedFacts : LeafRoundedFacts 8
    leaf3047Certificate.logOnePlusV leaf3047InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3047InputLogOnePlusV_eq }

private noncomputable def leaf3047Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi188InputQChi innerPair57Input
    leaf3047InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3047LowerChecked :
    lowerCheck 24 leaf3047Box leaf3047Inputs = true := by
  rfl'

private theorem leaf3047CoversExact : CoversExact 8
    leaf3047Box leaf3047Certificate leaf3047InnerLog leaf3047Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi188RoundedFacts
    innerPair57RoundedFacts leaf3047RoundedFacts (by rfl)

private theorem leaf3047FlatSound : Sound leaf3047Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3047CertificateValid
    leaf3047InnerLogValid leaf3047CoversExact leaf3047LowerChecked

private noncomputable def leaf3048Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3048Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090113536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1809043071/1073741824) }, upper := { exponent := 0, mantissa := (6971/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180369901/10180227072) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3048InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf3048LocalValidity :
    LeafFacts leaf3048Box leaf3048Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3048Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090113536) }) = true
      norm_num [leaf3048Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3048CertificateValid :
    WideCertificateValid leaf3048Box leaf3048Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi188ValidityFacts
    leaf3048LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3048CoverageChecked :
    coverageCheck (innerAD leaf3048Box) leaf3048InnerLog = true := by
  rfl'

private theorem leaf3048InnerLogValid :
    leaf3048InnerLog.Valid 8 (innerAD leaf3048Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf3048CoverageChecked

private noncomputable def leaf3048InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3048InputLogOnePlusV_eq :
    leaf3048InputLogOnePlusV = outerEnclosure 24
      (leaf3048Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3048RoundedFacts : LeafRoundedFacts 8
    leaf3048Certificate.logOnePlusV leaf3048InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3048InputLogOnePlusV_eq }

private noncomputable def leaf3048Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi188InputQChi innerPair57Input
    leaf3048InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3048LowerChecked :
    lowerCheck 24 leaf3048Box leaf3048Inputs = true := by
  rfl'

private theorem leaf3048CoversExact : CoversExact 8
    leaf3048Box leaf3048Certificate leaf3048InnerLog leaf3048Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi188RoundedFacts
    innerPair57RoundedFacts leaf3048RoundedFacts (by rfl)

private theorem leaf3048FlatSound : Sound leaf3048Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3048CertificateValid
    leaf3048InnerLogValid leaf3048CoversExact leaf3048LowerChecked

private noncomputable def leaf3049Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3049Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433158144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1797181779/1073741824) }, upper := { exponent := 0, mantissa := (27703/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870079999/274866316288) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3049InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3049LocalValidity :
    LeafFacts leaf3049Box leaf3049Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3049Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433158144) }) = true
      norm_num [leaf3049Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3049CertificateValid :
    WideCertificateValid leaf3049Box leaf3049Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi187ValidityFacts
    leaf3049LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3049CoverageChecked :
    coverageCheck (innerAD leaf3049Box) leaf3049InnerLog = true := by
  rfl'

private theorem leaf3049InnerLogValid :
    leaf3049InnerLog.Valid 8 (innerAD leaf3049Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3049CoverageChecked

private noncomputable def leaf3049InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3049InputLogOnePlusV_eq :
    leaf3049InputLogOnePlusV = outerEnclosure 24
      (leaf3049Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3049RoundedFacts : LeafRoundedFacts 8
    leaf3049Certificate.logOnePlusV leaf3049InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3049InputLogOnePlusV_eq }

private noncomputable def leaf3049Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi187InputQChi innerPair420Input
    leaf3049InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3049LowerChecked :
    lowerCheck 24 leaf3049Box leaf3049Inputs = true := by
  rfl'

private theorem leaf3049CoversExact : CoversExact 8
    leaf3049Box leaf3049Certificate leaf3049InnerLog leaf3049Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi187RoundedFacts
    innerPair420RoundedFacts leaf3049RoundedFacts (by rfl)

private theorem leaf3049FlatSound : Sound leaf3049Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3049CertificateValid
    leaf3049InnerLogValid leaf3049CoversExact leaf3049LowerChecked

private noncomputable def leaf3050Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3050Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811044352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1800327313/1073741824) }, upper := { exponent := 0, mantissa := (3469/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623351637/91622088704) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3050InnerLog : WideLogData :=
  innerPair420Data

set_option maxRecDepth 1000000 in
private theorem leaf3050LocalValidity :
    LeafFacts leaf3050Box leaf3050Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3050Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811044352) }) = true
      norm_num [leaf3050Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3050CertificateValid :
    WideCertificateValid leaf3050Box leaf3050Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi187ValidityFacts
    leaf3050LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3050CoverageChecked :
    coverageCheck (innerAD leaf3050Box) leaf3050InnerLog = true := by
  rfl'

private theorem leaf3050InnerLogValid :
    leaf3050InnerLog.Valid 8 (innerAD leaf3050Box) :=
  wideLogDataValid_of_cachedCheck endpoint133PositiveFacts
    endpoint20PositiveFacts.valid leaf3050CoverageChecked

private noncomputable def leaf3050InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf3050InputLogOnePlusV_eq :
    leaf3050InputLogOnePlusV = outerEnclosure 24
      (leaf3050Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3050RoundedFacts : LeafRoundedFacts 8
    leaf3050Certificate.logOnePlusV leaf3050InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3050InputLogOnePlusV_eq }

private noncomputable def leaf3050Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi187InputQChi innerPair420Input
    leaf3050InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3050LowerChecked :
    lowerCheck 24 leaf3050Box leaf3050Inputs = true := by
  rfl'

private theorem leaf3050CoversExact : CoversExact 8
    leaf3050Box leaf3050Certificate leaf3050InnerLog leaf3050Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi187RoundedFacts
    innerPair420RoundedFacts leaf3050RoundedFacts (by rfl)

private theorem leaf3050FlatSound : Sound leaf3050Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3050CertificateValid
    leaf3050InnerLogValid leaf3050CoversExact leaf3050LowerChecked

private noncomputable def leaf3051Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3051Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433039872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1812254137/1073741824) }, upper := { exponent := 0, mantissa := (13967/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869961727/274866079744) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3051InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3051LocalValidity :
    LeafFacts leaf3051Box leaf3051Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3051Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433039872) }) = true
      norm_num [leaf3051Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3051CertificateValid :
    WideCertificateValid leaf3051Box leaf3051Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi188ValidityFacts
    leaf3051LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3051CoverageChecked :
    coverageCheck (innerAD leaf3051Box) leaf3051InnerLog = true := by
  rfl'

private theorem leaf3051InnerLogValid :
    leaf3051InnerLog.Valid 8 (innerAD leaf3051Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3051CoverageChecked

private noncomputable def leaf3051InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3051InputLogOnePlusV_eq :
    leaf3051InputLogOnePlusV = outerEnclosure 24
      (leaf3051Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3051RoundedFacts : LeafRoundedFacts 8
    leaf3051Certificate.logOnePlusV leaf3051InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3051InputLogOnePlusV_eq }

private noncomputable def leaf3051Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3051InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3051LowerChecked :
    lowerCheck 24 leaf3051Box leaf3051Inputs = true := by
  rfl'

private theorem leaf3051CoversExact : CoversExact 8
    leaf3051Box leaf3051Certificate leaf3051InnerLog leaf3051Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3051RoundedFacts (by rfl)

private theorem leaf3051FlatSound : Sound leaf3051Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3051CertificateValid
    leaf3051InnerLogValid leaf3051CoversExact leaf3051LowerChecked

private noncomputable def leaf3052Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3052Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433014272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1815465203/1073741824) }, upper := { exponent := 0, mantissa := (1749/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869936127/274866028544) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3052InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3052LocalValidity :
    LeafFacts leaf3052Box leaf3052Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3052Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433014272) }) = true
      norm_num [leaf3052Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3052CertificateValid :
    WideCertificateValid leaf3052Box leaf3052Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi188ValidityFacts
    leaf3052LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3052CoverageChecked :
    coverageCheck (innerAD leaf3052Box) leaf3052InnerLog = true := by
  rfl'

private theorem leaf3052InnerLogValid :
    leaf3052InnerLog.Valid 8 (innerAD leaf3052Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3052CoverageChecked

private noncomputable def leaf3052InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3052InputLogOnePlusV_eq :
    leaf3052InputLogOnePlusV = outerEnclosure 24
      (leaf3052Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3052RoundedFacts : LeafRoundedFacts 8
    leaf3052Certificate.logOnePlusV leaf3052InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3052InputLogOnePlusV_eq }

private noncomputable def leaf3052Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3052InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3052LowerChecked :
    lowerCheck 24 leaf3052Box leaf3052Inputs = true := by
  rfl'

private theorem leaf3052CoversExact : CoversExact 8
    leaf3052Box leaf3052Certificate leaf3052InnerLog leaf3052Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3052RoundedFacts (by rfl)

private theorem leaf3052FlatSound : Sound leaf3052Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3052CertificateValid
    leaf3052InnerLogValid leaf3052CoversExact leaf3052LowerChecked

private noncomputable def leaf3053Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3053Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432973824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1820773299/1073741824) }, upper := { exponent := 0, mantissa := (28063/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869895679/274865947648) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3053InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3053LocalValidity :
    LeafFacts leaf3053Box leaf3053Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3053Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432973824) }) = true
      norm_num [leaf3053Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3053CertificateValid :
    WideCertificateValid leaf3053Box leaf3053Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi193ValidityFacts
    leaf3053LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3053CoverageChecked :
    coverageCheck (innerAD leaf3053Box) leaf3053InnerLog = true := by
  rfl'

private theorem leaf3053InnerLogValid :
    leaf3053InnerLog.Valid 8 (innerAD leaf3053Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3053CoverageChecked

private noncomputable def leaf3053InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3053InputLogOnePlusV_eq :
    leaf3053InputLogOnePlusV = outerEnclosure 24
      (leaf3053Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3053RoundedFacts : LeafRoundedFacts 8
    leaf3053Certificate.logOnePlusV leaf3053InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3053InputLogOnePlusV_eq }

private noncomputable def leaf3053Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3053InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3053LowerChecked :
    lowerCheck 24 leaf3053Box leaf3053Inputs = true := by
  rfl'

private theorem leaf3053CoversExact : CoversExact 8
    leaf3053Box leaf3053Certificate leaf3053InnerLog leaf3053Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3053RoundedFacts (by rfl)

private theorem leaf3053FlatSound : Sound leaf3053Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3053CertificateValid
    leaf3053InnerLogValid leaf3053CoversExact leaf3053LowerChecked

private noncomputable def leaf3054Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3054Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432947712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1824049897/1073741824) }, upper := { exponent := 0, mantissa := (14057/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869869567/274865895424) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3054InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3054LocalValidity :
    LeafFacts leaf3054Box leaf3054Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3054Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432947712) }) = true
      norm_num [leaf3054Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3054CertificateValid :
    WideCertificateValid leaf3054Box leaf3054Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi193ValidityFacts
    leaf3054LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3054CoverageChecked :
    coverageCheck (innerAD leaf3054Box) leaf3054InnerLog = true := by
  rfl'

private theorem leaf3054InnerLogValid :
    leaf3054InnerLog.Valid 8 (innerAD leaf3054Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3054CoverageChecked

private noncomputable def leaf3054InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3054InputLogOnePlusV_eq :
    leaf3054InputLogOnePlusV = outerEnclosure 24
      (leaf3054Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3054RoundedFacts : LeafRoundedFacts 8
    leaf3054Certificate.logOnePlusV leaf3054InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3054InputLogOnePlusV_eq }

private noncomputable def leaf3054Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3054InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3054LowerChecked :
    lowerCheck 24 leaf3054Box leaf3054Inputs = true := by
  rfl'

private theorem leaf3054CoversExact : CoversExact 8
    leaf3054Box leaf3054Certificate leaf3054InnerLog leaf3054Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3054RoundedFacts (by rfl)

private theorem leaf3054FlatSound : Sound leaf3054Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3054CertificateValid
    leaf3054InnerLogValid leaf3054CoversExact leaf3054LowerChecked

private noncomputable def leaf3055Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3055Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810952192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1835714593/1073741824) }, upper := { exponent := 0, mantissa := (7073/4096) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623259477/91621904384) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3055InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3055LocalValidity :
    LeafFacts leaf3055Box leaf3055Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3055Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810952192) }) = true
      norm_num [leaf3055Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3055CertificateValid :
    WideCertificateValid leaf3055Box leaf3055Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi194ValidityFacts
    leaf3055LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3055CoverageChecked :
    coverageCheck (innerAD leaf3055Box) leaf3055InnerLog = true := by
  rfl'

private theorem leaf3055InnerLogValid :
    leaf3055InnerLog.Valid 8 (innerAD leaf3055Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3055CoverageChecked

private noncomputable def leaf3055InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3055InputLogOnePlusV_eq :
    leaf3055InputLogOnePlusV = outerEnclosure 24
      (leaf3055Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3055RoundedFacts : LeafRoundedFacts 8
    leaf3055Certificate.logOnePlusV leaf3055InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3055InputLogOnePlusV_eq }

private noncomputable def leaf3055Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3055InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3055LowerChecked :
    lowerCheck 24 leaf3055Box leaf3055Inputs = true := by
  rfl'

private theorem leaf3055CoversExact : CoversExact 8
    leaf3055Box leaf3055Certificate leaf3055InnerLog leaf3055Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3055RoundedFacts (by rfl)

private theorem leaf3055FlatSound : Sound leaf3055Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3055CertificateValid
    leaf3055InnerLogValid leaf3055CoversExact leaf3055LowerChecked

private noncomputable def leaf3056Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3056Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432829952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1839056723/1073741824) }, upper := { exponent := 0, mantissa := (3543/2048) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869751807/274865659904) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3056InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3056LocalValidity :
    LeafFacts leaf3056Box leaf3056Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3056Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432829952) }) = true
      norm_num [leaf3056Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3056CertificateValid :
    WideCertificateValid leaf3056Box leaf3056Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi194ValidityFacts
    leaf3056LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3056CoverageChecked :
    coverageCheck (innerAD leaf3056Box) leaf3056InnerLog = true := by
  rfl'

private theorem leaf3056InnerLogValid :
    leaf3056InnerLog.Valid 8 (innerAD leaf3056Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3056CoverageChecked

private noncomputable def leaf3056InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3056InputLogOnePlusV_eq :
    leaf3056InputLogOnePlusV = outerEnclosure 24
      (leaf3056Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3056RoundedFacts : LeafRoundedFacts 8
    leaf3056Certificate.logOnePlusV leaf3056InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3056InputLogOnePlusV_eq }

private noncomputable def leaf3056Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3056InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3056LowerChecked :
    lowerCheck 24 leaf3056Box leaf3056Inputs = true := by
  rfl'

private theorem leaf3056CoversExact : CoversExact 8
    leaf3056Box leaf3056Certificate leaf3056InnerLog leaf3056Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3056RoundedFacts (by rfl)

private theorem leaf3056FlatSound : Sound leaf3056Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3056CertificateValid
    leaf3056InnerLogValid leaf3056CoversExact leaf3056LowerChecked

private noncomputable def leaf3057Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3057Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486584320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1827326495/1073741824) }, upper := { exponent := 0, mantissa := (28165/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973968691/54973168640) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3057InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3057LocalValidity :
    LeafFacts leaf3057Box leaf3057Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3057Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486584320) }) = true
      norm_num [leaf3057Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3057CertificateValid :
    WideCertificateValid leaf3057Box leaf3057Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi193ValidityFacts
    leaf3057LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3057CoverageChecked :
    coverageCheck (innerAD leaf3057Box) leaf3057InnerLog = true := by
  rfl'

private theorem leaf3057InnerLogValid :
    leaf3057InnerLog.Valid 8 (innerAD leaf3057Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3057CoverageChecked

private noncomputable def leaf3057InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3057InputLogOnePlusV_eq :
    leaf3057InputLogOnePlusV = outerEnclosure 24
      (leaf3057Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3057RoundedFacts : LeafRoundedFacts 8
    leaf3057Certificate.logOnePlusV leaf3057InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3057InputLogOnePlusV_eq }

private noncomputable def leaf3057Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3057InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3057LowerChecked :
    lowerCheck 24 leaf3057Box leaf3057Inputs = true := by
  rfl'

private theorem leaf3057CoversExact : CoversExact 8
    leaf3057Box leaf3057Certificate leaf3057InnerLog leaf3057Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3057RoundedFacts (by rfl)

private theorem leaf3057FlatSound : Sound leaf3057Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3057CertificateValid
    leaf3057InnerLogValid leaf3057CoversExact leaf3057LowerChecked

private noncomputable def leaf3058Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3058Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432895488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1830603093/1073741824) }, upper := { exponent := 0, mantissa := (3527/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869817343/274865790976) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3058InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3058LocalValidity :
    LeafFacts leaf3058Box leaf3058Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3058Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432895488) }) = true
      norm_num [leaf3058Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3058CertificateValid :
    WideCertificateValid leaf3058Box leaf3058Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi193ValidityFacts
    leaf3058LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3058CoverageChecked :
    coverageCheck (innerAD leaf3058Box) leaf3058InnerLog = true := by
  rfl'

private theorem leaf3058InnerLogValid :
    leaf3058InnerLog.Valid 8 (innerAD leaf3058Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3058CoverageChecked

private noncomputable def leaf3058InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3058InputLogOnePlusV_eq :
    leaf3058InputLogOnePlusV = outerEnclosure 24
      (leaf3058Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3058RoundedFacts : LeafRoundedFacts 8
    leaf3058Certificate.logOnePlusV leaf3058InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3058InputLogOnePlusV_eq }

private noncomputable def leaf3058Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi193InputQChi innerPair64Input
    leaf3058InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3058LowerChecked :
    lowerCheck 24 leaf3058Box leaf3058Inputs = true := by
  rfl'

private theorem leaf3058CoversExact : CoversExact 8
    leaf3058Box leaf3058Certificate leaf3058InnerLog leaf3058Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi193RoundedFacts
    innerPair64RoundedFacts leaf3058RoundedFacts (by rfl)

private theorem leaf3058FlatSound : Sound leaf3058Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3058CertificateValid
    leaf3058InnerLogValid leaf3058CoversExact leaf3058LowerChecked

private noncomputable def leaf3059Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3059Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432803328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1842398853/1073741824) }, upper := { exponent := 0, mantissa := (7099/4096) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869725183/274865606656) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3059InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3059LocalValidity :
    LeafFacts leaf3059Box leaf3059Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3059Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432803328) }) = true
      norm_num [leaf3059Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3059CertificateValid :
    WideCertificateValid leaf3059Box leaf3059Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi194ValidityFacts
    leaf3059LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3059CoverageChecked :
    coverageCheck (innerAD leaf3059Box) leaf3059InnerLog = true := by
  rfl'

private theorem leaf3059InnerLogValid :
    leaf3059InnerLog.Valid 8 (innerAD leaf3059Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3059CoverageChecked

private noncomputable def leaf3059InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3059InputLogOnePlusV_eq :
    leaf3059InputLogOnePlusV = outerEnclosure 24
      (leaf3059Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3059RoundedFacts : LeafRoundedFacts 8
    leaf3059Certificate.logOnePlusV leaf3059InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3059InputLogOnePlusV_eq }

private noncomputable def leaf3059Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3059InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3059LowerChecked :
    lowerCheck 24 leaf3059Box leaf3059Inputs = true := by
  rfl'

private theorem leaf3059CoversExact : CoversExact 8
    leaf3059Box leaf3059Certificate leaf3059InnerLog leaf3059Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3059RoundedFacts (by rfl)

private theorem leaf3059FlatSound : Sound leaf3059Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3059CertificateValid
    leaf3059InnerLogValid leaf3059CoversExact leaf3059LowerChecked

private noncomputable def leaf3060Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3060Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810925568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1845740983/1073741824) }, upper := { exponent := 0, mantissa := (889/512) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623232853/91621851136) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3060InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3060LocalValidity :
    LeafFacts leaf3060Box leaf3060Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3060Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810925568) }) = true
      norm_num [leaf3060Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3060CertificateValid :
    WideCertificateValid leaf3060Box leaf3060Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi194ValidityFacts
    leaf3060LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3060CoverageChecked :
    coverageCheck (innerAD leaf3060Box) leaf3060InnerLog = true := by
  rfl'

private theorem leaf3060InnerLogValid :
    leaf3060InnerLog.Valid 8 (innerAD leaf3060Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3060CoverageChecked

private noncomputable def leaf3060InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3060InputLogOnePlusV_eq :
    leaf3060InputLogOnePlusV = outerEnclosure 24
      (leaf3060Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3060RoundedFacts : LeafRoundedFacts 8
    leaf3060Certificate.logOnePlusV leaf3060InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3060InputLogOnePlusV_eq }

private noncomputable def leaf3060Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi194InputQChi innerPair64Input
    leaf3060InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3060LowerChecked :
    lowerCheck 24 leaf3060Box leaf3060Inputs = true := by
  rfl'

private theorem leaf3060CoversExact : CoversExact 8
    leaf3060Box leaf3060Certificate leaf3060InnerLog leaf3060Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf3060RoundedFacts (by rfl)

private theorem leaf3060FlatSound : Sound leaf3060Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3060CertificateValid
    leaf3060InnerLogValid leaf3060CoversExact leaf3060LowerChecked

private noncomputable def leaf3061Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3061Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432847872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1837025239/1073741824) }, upper := { exponent := 0, mantissa := (28309/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869769727/274865695744) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3061InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3061LocalValidity :
    LeafFacts leaf3061Box leaf3061Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3061Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432847872) }) = true
      norm_num [leaf3061Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3061CertificateValid :
    WideCertificateValid leaf3061Box leaf3061Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi195ValidityFacts
    leaf3061LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3061CoverageChecked :
    coverageCheck (innerAD leaf3061Box) leaf3061InnerLog = true := by
  rfl'

private theorem leaf3061InnerLogValid :
    leaf3061InnerLog.Valid 8 (innerAD leaf3061Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3061CoverageChecked

private noncomputable def leaf3061InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3061InputLogOnePlusV_eq :
    leaf3061InputLogOnePlusV = outerEnclosure 24
      (leaf3061Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3061RoundedFacts : LeafRoundedFacts 8
    leaf3061Certificate.logOnePlusV leaf3061InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3061InputLogOnePlusV_eq }

private noncomputable def leaf3061Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi195InputQChi innerPair64Input
    leaf3061InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3061LowerChecked :
    lowerCheck 24 leaf3061Box leaf3061Inputs = true := by
  rfl'

private theorem leaf3061CoversExact : CoversExact 8
    leaf3061Box leaf3061Certificate leaf3061InnerLog leaf3061Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf3061RoundedFacts (by rfl)

private theorem leaf3061FlatSound : Sound leaf3061Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3061CertificateValid
    leaf3061InnerLogValid leaf3061CoversExact leaf3061LowerChecked

private noncomputable def leaf3062Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3062Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432732672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1851704405/1073741824) }, upper := { exponent := 0, mantissa := (14267/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869654527/274865465344) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3062InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3062LocalValidity :
    LeafFacts leaf3062Box leaf3062Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3062Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432732672) }) = true
      norm_num [leaf3062Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3062CertificateValid :
    WideCertificateValid leaf3062Box leaf3062Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi196ValidityFacts
    leaf3062LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3062CoverageChecked :
    coverageCheck (innerAD leaf3062Box) leaf3062InnerLog = true := by
  rfl'

private theorem leaf3062InnerLogValid :
    leaf3062InnerLog.Valid 8 (innerAD leaf3062Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3062CoverageChecked

private noncomputable def leaf3062InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3062InputLogOnePlusV_eq :
    leaf3062InputLogOnePlusV = outerEnclosure 24
      (leaf3062Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3062RoundedFacts : LeafRoundedFacts 8
    leaf3062Certificate.logOnePlusV leaf3062InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3062InputLogOnePlusV_eq }

private noncomputable def leaf3062Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi196InputQChi innerPair64Input
    leaf3062InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3062LowerChecked :
    lowerCheck 24 leaf3062Box leaf3062Inputs = true := by
  rfl'

private theorem leaf3062CoversExact : CoversExact 8
    leaf3062Box leaf3062Certificate leaf3062InnerLog leaf3062Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf3062RoundedFacts (by rfl)

private theorem leaf3062FlatSound : Sound leaf3062Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3062CertificateValid
    leaf3062InnerLogValid leaf3062CoversExact leaf3062LowerChecked

private noncomputable def leaf3063Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3063Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432820736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1840432901/1073741824) }, upper := { exponent := 0, mantissa := (14181/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869742591/274865641472) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3063InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3063LocalValidity :
    LeafFacts leaf3063Box leaf3063Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3063Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432820736) }) = true
      norm_num [leaf3063Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3063CertificateValid :
    WideCertificateValid leaf3063Box leaf3063Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi195ValidityFacts
    leaf3063LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3063CoverageChecked :
    coverageCheck (innerAD leaf3063Box) leaf3063InnerLog = true := by
  rfl'

private theorem leaf3063InnerLogValid :
    leaf3063InnerLog.Valid 8 (innerAD leaf3063Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3063CoverageChecked

private noncomputable def leaf3063InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3063InputLogOnePlusV_eq :
    leaf3063InputLogOnePlusV = outerEnclosure 24
      (leaf3063Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3063RoundedFacts : LeafRoundedFacts 8
    leaf3063Certificate.logOnePlusV leaf3063InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3063InputLogOnePlusV_eq }

private noncomputable def leaf3063Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi195InputQChi innerPair64Input
    leaf3063InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3063LowerChecked :
    lowerCheck 24 leaf3063Box leaf3063Inputs = true := by
  rfl'

private theorem leaf3063CoversExact : CoversExact 8
    leaf3063Box leaf3063Certificate leaf3063InnerLog leaf3063Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf3063RoundedFacts (by rfl)

private theorem leaf3063FlatSound : Sound leaf3063Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3063CertificateValid
    leaf3063InnerLogValid leaf3063CoversExact leaf3063LowerChecked

private noncomputable def leaf3064Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3064Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432705024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1855177599/1073741824) }, upper := { exponent := 0, mantissa := (7147/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869626879/274865410048) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3064InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3064LocalValidity :
    LeafFacts leaf3064Box leaf3064Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3064Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432705024) }) = true
      norm_num [leaf3064Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3064CertificateValid :
    WideCertificateValid leaf3064Box leaf3064Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi196ValidityFacts
    leaf3064LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3064CoverageChecked :
    coverageCheck (innerAD leaf3064Box) leaf3064InnerLog = true := by
  rfl'

private theorem leaf3064InnerLogValid :
    leaf3064InnerLog.Valid 8 (innerAD leaf3064Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3064CoverageChecked

private noncomputable def leaf3064InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3064InputLogOnePlusV_eq :
    leaf3064InputLogOnePlusV = outerEnclosure 24
      (leaf3064Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3064RoundedFacts : LeafRoundedFacts 8
    leaf3064Certificate.logOnePlusV leaf3064InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3064InputLogOnePlusV_eq }

private noncomputable def leaf3064Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi196InputQChi innerPair64Input
    leaf3064InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3064LowerChecked :
    lowerCheck 24 leaf3064Box leaf3064Inputs = true := by
  rfl'

private theorem leaf3064CoversExact : CoversExact 8
    leaf3064Box leaf3064Certificate leaf3064InnerLog leaf3064Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf3064RoundedFacts (by rfl)

private theorem leaf3064FlatSound : Sound leaf3064Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3064CertificateValid
    leaf3064InnerLogValid leaf3064CoversExact leaf3064LowerChecked

private noncomputable def leaf3065Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3065Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054062080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1843840563/1073741824) }, upper := { exponent := 0, mantissa := (28415/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108215899/6108124160) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3065InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3065LocalValidity :
    LeafFacts leaf3065Box leaf3065Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3065Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054062080) }) = true
      norm_num [leaf3065Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3065CertificateValid :
    WideCertificateValid leaf3065Box leaf3065Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi195ValidityFacts
    leaf3065LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3065CoverageChecked :
    coverageCheck (innerAD leaf3065Box) leaf3065InnerLog = true := by
  rfl'

private theorem leaf3065InnerLogValid :
    leaf3065InnerLog.Valid 8 (innerAD leaf3065Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3065CoverageChecked

private noncomputable def leaf3065InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3065InputLogOnePlusV_eq :
    leaf3065InputLogOnePlusV = outerEnclosure 24
      (leaf3065Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3065RoundedFacts : LeafRoundedFacts 8
    leaf3065Certificate.logOnePlusV leaf3065InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3065InputLogOnePlusV_eq }

private noncomputable def leaf3065Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi195InputQChi innerPair64Input
    leaf3065InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3065LowerChecked :
    lowerCheck 24 leaf3065Box leaf3065Inputs = true := by
  rfl'

private theorem leaf3065CoversExact : CoversExact 8
    leaf3065Box leaf3065Certificate leaf3065InnerLog leaf3065Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf3065RoundedFacts (by rfl)

private theorem leaf3065FlatSound : Sound leaf3065Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3065CertificateValid
    leaf3065InnerLogValid leaf3065CoversExact leaf3065LowerChecked

private noncomputable def leaf3066Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3066Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432677376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1858650793/1073741824) }, upper := { exponent := 0, mantissa := (14321/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869599231/274865354752) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3066InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3066LocalValidity :
    LeafFacts leaf3066Box leaf3066Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3066Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432677376) }) = true
      norm_num [leaf3066Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3066CertificateValid :
    WideCertificateValid leaf3066Box leaf3066Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi196ValidityFacts
    leaf3066LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3066CoverageChecked :
    coverageCheck (innerAD leaf3066Box) leaf3066InnerLog = true := by
  rfl'

private theorem leaf3066InnerLogValid :
    leaf3066InnerLog.Valid 8 (innerAD leaf3066Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3066CoverageChecked

private noncomputable def leaf3066InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3066InputLogOnePlusV_eq :
    leaf3066InputLogOnePlusV = outerEnclosure 24
      (leaf3066Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3066RoundedFacts : LeafRoundedFacts 8
    leaf3066Certificate.logOnePlusV leaf3066InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3066InputLogOnePlusV_eq }

private noncomputable def leaf3066Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi196InputQChi innerPair64Input
    leaf3066InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3066LowerChecked :
    lowerCheck 24 leaf3066Box leaf3066Inputs = true := by
  rfl'

private theorem leaf3066CoversExact : CoversExact 8
    leaf3066Box leaf3066Certificate leaf3066InnerLog leaf3066Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf3066RoundedFacts (by rfl)

private theorem leaf3066FlatSound : Sound leaf3066Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3066CertificateValid
    leaf3066InnerLogValid leaf3066CoversExact leaf3066LowerChecked

private noncomputable def leaf3067Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3067Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196110848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1847248225/1073741824) }, upper := { exponent := 0, mantissa := (7117/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392318333/6392221696) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3067InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3067LocalValidity :
    LeafFacts leaf3067Box leaf3067Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3067Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196110848) }) = true
      norm_num [leaf3067Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3067CertificateValid :
    WideCertificateValid leaf3067Box leaf3067Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi195ValidityFacts
    leaf3067LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3067CoverageChecked :
    coverageCheck (innerAD leaf3067Box) leaf3067InnerLog = true := by
  rfl'

private theorem leaf3067InnerLogValid :
    leaf3067InnerLog.Valid 8 (innerAD leaf3067Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3067CoverageChecked

private noncomputable def leaf3067InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3067InputLogOnePlusV_eq :
    leaf3067InputLogOnePlusV = outerEnclosure 24
      (leaf3067Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3067RoundedFacts : LeafRoundedFacts 8
    leaf3067Certificate.logOnePlusV leaf3067InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3067InputLogOnePlusV_eq }

private noncomputable def leaf3067Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi195InputQChi innerPair64Input
    leaf3067InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3067LowerChecked :
    lowerCheck 24 leaf3067Box leaf3067Inputs = true := by
  rfl'

private theorem leaf3067CoversExact : CoversExact 8
    leaf3067Box leaf3067Certificate leaf3067InnerLog leaf3067Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf3067RoundedFacts (by rfl)

private theorem leaf3067FlatSound : Sound leaf3067Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3067CertificateValid
    leaf3067InnerLogValid leaf3067CoversExact leaf3067LowerChecked

private noncomputable def leaf3068Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3068Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432649728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1862123987/1073741824) }, upper := { exponent := 0, mantissa := (3587/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869571583/274865299456) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3068InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf3068LocalValidity :
    LeafFacts leaf3068Box leaf3068Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3068Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432649728) }) = true
      norm_num [leaf3068Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3068CertificateValid :
    WideCertificateValid leaf3068Box leaf3068Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi196ValidityFacts
    leaf3068LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3068CoverageChecked :
    coverageCheck (innerAD leaf3068Box) leaf3068InnerLog = true := by
  rfl'

private theorem leaf3068InnerLogValid :
    leaf3068InnerLog.Valid 8 (innerAD leaf3068Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf3068CoverageChecked

private noncomputable def leaf3068InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3068InputLogOnePlusV_eq :
    leaf3068InputLogOnePlusV = outerEnclosure 24
      (leaf3068Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3068RoundedFacts : LeafRoundedFacts 8
    leaf3068Certificate.logOnePlusV leaf3068InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3068InputLogOnePlusV_eq }

private noncomputable def leaf3068Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi196InputQChi innerPair204Input
    leaf3068InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3068LowerChecked :
    lowerCheck 24 leaf3068Box leaf3068Inputs = true := by
  rfl'

private theorem leaf3068CoversExact : CoversExact 8
    leaf3068Box leaf3068Certificate leaf3068InnerLog leaf3068Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi196RoundedFacts
    innerPair204RoundedFacts leaf3068RoundedFacts (by rfl)

private theorem leaf3068FlatSound : Sound leaf3068Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3068CertificateValid
    leaf3068InnerLogValid leaf3068CoversExact leaf3068LowerChecked

private noncomputable def leaf3069Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3069Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084271616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1866383571/1073741824) }, upper := { exponent := 0, mantissa := (28759/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168796431/16168543232) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3069InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3069LocalValidity :
    LeafFacts leaf3069Box leaf3069Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3069Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084271616) }) = true
      norm_num [leaf3069Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3069CertificateValid :
    WideCertificateValid leaf3069Box leaf3069Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi197ValidityFacts
    leaf3069LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3069CoverageChecked :
    coverageCheck (innerAD leaf3069Box) leaf3069InnerLog = true := by
  rfl'

private theorem leaf3069InnerLogValid :
    leaf3069InnerLog.Valid 8 (innerAD leaf3069Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3069CoverageChecked

private noncomputable def leaf3069InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3069InputLogOnePlusV_eq :
    leaf3069InputLogOnePlusV = outerEnclosure 24
      (leaf3069Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3069RoundedFacts : LeafRoundedFacts 8
    leaf3069Certificate.logOnePlusV leaf3069InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3069InputLogOnePlusV_eq }

private noncomputable def leaf3069Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi197InputQChi innerPair66Input
    leaf3069InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3069LowerChecked :
    lowerCheck 24 leaf3069Box leaf3069Inputs = true := by
  rfl'

private theorem leaf3069CoversExact : CoversExact 8
    leaf3069Box leaf3069Certificate leaf3069InnerLog leaf3069Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi197RoundedFacts
    innerPair66RoundedFacts leaf3069RoundedFacts (by rfl)

private theorem leaf3069FlatSound : Sound leaf3069Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3069CertificateValid
    leaf3069InnerLogValid leaf3069CoversExact leaf3069LowerChecked

private noncomputable def leaf3070Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3070Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810863104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1869922297/1073741824) }, upper := { exponent := 0, mantissa := (14407/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623170389/91621726208) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3070InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3070LocalValidity :
    LeafFacts leaf3070Box leaf3070Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3070Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810863104) }) = true
      norm_num [leaf3070Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3070CertificateValid :
    WideCertificateValid leaf3070Box leaf3070Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi197ValidityFacts
    leaf3070LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3070CoverageChecked :
    coverageCheck (innerAD leaf3070Box) leaf3070InnerLog = true := by
  rfl'

private theorem leaf3070InnerLogValid :
    leaf3070InnerLog.Valid 8 (innerAD leaf3070Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3070CoverageChecked

private noncomputable def leaf3070InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3070InputLogOnePlusV_eq :
    leaf3070InputLogOnePlusV = outerEnclosure 24
      (leaf3070Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3070RoundedFacts : LeafRoundedFacts 8
    leaf3070Certificate.logOnePlusV leaf3070InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3070InputLogOnePlusV_eq }

private noncomputable def leaf3070Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi197InputQChi innerPair66Input
    leaf3070InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3070LowerChecked :
    lowerCheck 24 leaf3070Box leaf3070Inputs = true := by
  rfl'

private theorem leaf3070CoversExact : CoversExact 8
    leaf3070Box leaf3070Certificate leaf3070InnerLog leaf3070Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi197RoundedFacts
    innerPair66RoundedFacts leaf3070RoundedFacts (by rfl)

private theorem leaf3070FlatSound : Sound leaf3070Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3070CertificateValid
    leaf3070InnerLogValid leaf3070CoversExact leaf3070LowerChecked

private noncomputable def leaf3071Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3071Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196104704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1881062737/1073741824) }, upper := { exponent := 0, mantissa := (3623/2048) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392312189/6392209408) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3071InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3071LocalValidity :
    LeafFacts leaf3071Box leaf3071Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3071Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196104704) }) = true
      norm_num [leaf3071Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3071CertificateValid :
    WideCertificateValid leaf3071Box leaf3071Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi198ValidityFacts
    leaf3071LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3071CoverageChecked :
    coverageCheck (innerAD leaf3071Box) leaf3071InnerLog = true := by
  rfl'

private theorem leaf3071InnerLogValid :
    leaf3071InnerLog.Valid 8 (innerAD leaf3071Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3071CoverageChecked

private noncomputable def leaf3071InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3071InputLogOnePlusV_eq :
    leaf3071InputLogOnePlusV = outerEnclosure 24
      (leaf3071Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3071RoundedFacts : LeafRoundedFacts 8
    leaf3071Certificate.logOnePlusV leaf3071InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3071InputLogOnePlusV_eq }

private noncomputable def leaf3071Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3071InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3071LowerChecked :
    lowerCheck 24 leaf3071Box leaf3071Inputs = true := by
  rfl'

private theorem leaf3071CoversExact : CoversExact 8
    leaf3071Box leaf3071Certificate leaf3071InnerLog leaf3071Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3071RoundedFacts (by rfl)

private theorem leaf3071FlatSound : Sound leaf3071Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3071CertificateValid
    leaf3071InnerLogValid leaf3071CoversExact leaf3071LowerChecked

private noncomputable def leaf3072Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3072Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486494720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1884666995/1073741824) }, upper := { exponent := 0, mantissa := (1815/1024) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973879091/54972989440) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3072InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3072LocalValidity :
    LeafFacts leaf3072Box leaf3072Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3072Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486494720) }) = true
      norm_num [leaf3072Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3072CertificateValid :
    WideCertificateValid leaf3072Box leaf3072Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi198ValidityFacts
    leaf3072LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3072CoverageChecked :
    coverageCheck (innerAD leaf3072Box) leaf3072InnerLog = true := by
  rfl'

private theorem leaf3072InnerLogValid :
    leaf3072InnerLog.Valid 8 (innerAD leaf3072Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3072CoverageChecked

private noncomputable def leaf3072InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3072InputLogOnePlusV_eq :
    leaf3072InputLogOnePlusV = outerEnclosure 24
      (leaf3072Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3072RoundedFacts : LeafRoundedFacts 8
    leaf3072Certificate.logOnePlusV leaf3072InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3072InputLogOnePlusV_eq }

private noncomputable def leaf3072Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3072InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3072LowerChecked :
    lowerCheck 24 leaf3072Box leaf3072Inputs = true := by
  rfl'

private theorem leaf3072CoversExact : CoversExact 8
    leaf3072Box leaf3072Certificate leaf3072InnerLog leaf3072Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3072RoundedFacts (by rfl)

private theorem leaf3072FlatSound : Sound leaf3072Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3072CertificateValid
    leaf3072InnerLogValid leaf3072CoversExact leaf3072LowerChecked

private noncomputable def leaf3073Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3073Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432561152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1873461023/1073741824) }, upper := { exponent := 0, mantissa := (28869/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869483007/274865122304) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3073InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3073LocalValidity :
    LeafFacts leaf3073Box leaf3073Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3073Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432561152) }) = true
      norm_num [leaf3073Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3073CertificateValid :
    WideCertificateValid leaf3073Box leaf3073Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi197ValidityFacts
    leaf3073LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3073CoverageChecked :
    coverageCheck (innerAD leaf3073Box) leaf3073InnerLog = true := by
  rfl'

private theorem leaf3073InnerLogValid :
    leaf3073InnerLog.Valid 8 (innerAD leaf3073Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3073CoverageChecked

private noncomputable def leaf3073InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3073InputLogOnePlusV_eq :
    leaf3073InputLogOnePlusV = outerEnclosure 24
      (leaf3073Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3073RoundedFacts : LeafRoundedFacts 8
    leaf3073Certificate.logOnePlusV leaf3073InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3073InputLogOnePlusV_eq }

private noncomputable def leaf3073Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi197InputQChi innerPair66Input
    leaf3073InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3073LowerChecked :
    lowerCheck 24 leaf3073Box leaf3073Inputs = true := by
  rfl'

private theorem leaf3073CoversExact : CoversExact 8
    leaf3073Box leaf3073Certificate leaf3073InnerLog leaf3073Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi197RoundedFacts
    innerPair66RoundedFacts leaf3073RoundedFacts (by rfl)

private theorem leaf3073FlatSound : Sound leaf3073Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3073CertificateValid
    leaf3073InnerLogValid leaf3073CoversExact leaf3073LowerChecked

private noncomputable def leaf3074Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3074Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432532992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1876999749/1073741824) }, upper := { exponent := 0, mantissa := (7231/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869454847/274865065984) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3074InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3074LocalValidity :
    LeafFacts leaf3074Box leaf3074Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3074Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432532992) }) = true
      norm_num [leaf3074Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3074CertificateValid :
    WideCertificateValid leaf3074Box leaf3074Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi197ValidityFacts
    leaf3074LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3074CoverageChecked :
    coverageCheck (innerAD leaf3074Box) leaf3074InnerLog = true := by
  rfl'

private theorem leaf3074InnerLogValid :
    leaf3074InnerLog.Valid 8 (innerAD leaf3074Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3074CoverageChecked

private noncomputable def leaf3074InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3074InputLogOnePlusV_eq :
    leaf3074InputLogOnePlusV = outerEnclosure 24
      (leaf3074Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3074RoundedFacts : LeafRoundedFacts 8
    leaf3074Certificate.logOnePlusV leaf3074InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3074InputLogOnePlusV_eq }

private noncomputable def leaf3074Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi197InputQChi innerPair66Input
    leaf3074InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3074LowerChecked :
    lowerCheck 24 leaf3074Box leaf3074Inputs = true := by
  rfl'

private theorem leaf3074CoversExact : CoversExact 8
    leaf3074Box leaf3074Certificate leaf3074InnerLog leaf3074Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi197RoundedFacts
    innerPair66RoundedFacts leaf3074RoundedFacts (by rfl)

private theorem leaf3074FlatSound : Sound leaf3074Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3074CertificateValid
    leaf3074InnerLogValid leaf3074CoversExact leaf3074LowerChecked

private noncomputable def leaf3075Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3075Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810814976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1888271253/1073741824) }, upper := { exponent := 0, mantissa := (3637/2048) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623122261/91621629952) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3075InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3075LocalValidity :
    LeafFacts leaf3075Box leaf3075Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3075Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810814976) }) = true
      norm_num [leaf3075Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3075CertificateValid :
    WideCertificateValid leaf3075Box leaf3075Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi198ValidityFacts
    leaf3075LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3075CoverageChecked :
    coverageCheck (innerAD leaf3075Box) leaf3075InnerLog = true := by
  rfl'

private theorem leaf3075InnerLogValid :
    leaf3075InnerLog.Valid 8 (innerAD leaf3075Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3075CoverageChecked

private noncomputable def leaf3075InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3075InputLogOnePlusV_eq :
    leaf3075InputLogOnePlusV = outerEnclosure 24
      (leaf3075Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3075RoundedFacts : LeafRoundedFacts 8
    leaf3075Certificate.logOnePlusV leaf3075InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3075InputLogOnePlusV_eq }

private noncomputable def leaf3075Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3075InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3075LowerChecked :
    lowerCheck 24 leaf3075Box leaf3075Inputs = true := by
  rfl'

private theorem leaf3075CoversExact : CoversExact 8
    leaf3075Box leaf3075Certificate leaf3075InnerLog leaf3075Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3075RoundedFacts (by rfl)

private theorem leaf3075FlatSound : Sound leaf3075Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3075CertificateValid
    leaf3075InnerLogValid leaf3075CoversExact leaf3075LowerChecked

private noncomputable def leaf3076Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3076Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432416256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1891875511/1073741824) }, upper := { exponent := 0, mantissa := (911/512) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869338111/274864832512) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3076InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3076LocalValidity :
    LeafFacts leaf3076Box leaf3076Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3076Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432416256) }) = true
      norm_num [leaf3076Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3076CertificateValid :
    WideCertificateValid leaf3076Box leaf3076Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi198ValidityFacts
    leaf3076LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3076CoverageChecked :
    coverageCheck (innerAD leaf3076Box) leaf3076InnerLog = true := by
  rfl'

private theorem leaf3076InnerLogValid :
    leaf3076InnerLog.Valid 8 (innerAD leaf3076Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3076CoverageChecked

private noncomputable def leaf3076InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3076InputLogOnePlusV_eq :
    leaf3076InputLogOnePlusV = outerEnclosure 24
      (leaf3076Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3076RoundedFacts : LeafRoundedFacts 8
    leaf3076Certificate.logOnePlusV leaf3076InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3076InputLogOnePlusV_eq }

private noncomputable def leaf3076Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3076InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3076LowerChecked :
    lowerCheck 24 leaf3076Box leaf3076Inputs = true := by
  rfl'

private theorem leaf3076CoversExact : CoversExact 8
    leaf3076Box leaf3076Certificate leaf3076InnerLog leaf3076Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3076RoundedFacts (by rfl)

private theorem leaf3076FlatSound : Sound leaf3076Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3076CertificateValid
    leaf3076InnerLogValid leaf3076CoversExact leaf3076LowerChecked

private noncomputable def leaf3077Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3077Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084278784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1850655887/1073741824) }, upper := { exponent := 0, mantissa := (28521/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168803599/16168557568) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3077InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3077LocalValidity :
    LeafFacts leaf3077Box leaf3077Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3077Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084278784) }) = true
      norm_num [leaf3077Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3077CertificateValid :
    WideCertificateValid leaf3077Box leaf3077Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi195ValidityFacts
    leaf3077LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3077CoverageChecked :
    coverageCheck (innerAD leaf3077Box) leaf3077InnerLog = true := by
  rfl'

private theorem leaf3077InnerLogValid :
    leaf3077InnerLog.Valid 8 (innerAD leaf3077Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3077CoverageChecked

private noncomputable def leaf3077InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3077InputLogOnePlusV_eq :
    leaf3077InputLogOnePlusV = outerEnclosure 24
      (leaf3077Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3077RoundedFacts : LeafRoundedFacts 8
    leaf3077Certificate.logOnePlusV leaf3077InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3077InputLogOnePlusV_eq }

private noncomputable def leaf3077Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi195InputQChi innerPair64Input
    leaf3077InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3077LowerChecked :
    lowerCheck 24 leaf3077Box leaf3077Inputs = true := by
  rfl'

private theorem leaf3077CoversExact : CoversExact 8
    leaf3077Box leaf3077Certificate leaf3077InnerLog leaf3077Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf3077RoundedFacts (by rfl)

private theorem leaf3077FlatSound : Sound leaf3077Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3077CertificateValid
    leaf3077InnerLogValid leaf3077CoversExact leaf3077LowerChecked

private noncomputable def leaf3078Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3078Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810904064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1854063549/1073741824) }, upper := { exponent := 0, mantissa := (14287/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623211349/91621808128) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3078InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3078LocalValidity :
    LeafFacts leaf3078Box leaf3078Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3078Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810904064) }) = true
      norm_num [leaf3078Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3078CertificateValid :
    WideCertificateValid leaf3078Box leaf3078Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi195ValidityFacts
    leaf3078LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3078CoverageChecked :
    coverageCheck (innerAD leaf3078Box) leaf3078InnerLog = true := by
  rfl'

private theorem leaf3078InnerLogValid :
    leaf3078InnerLog.Valid 8 (innerAD leaf3078Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3078CoverageChecked

private noncomputable def leaf3078InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3078InputLogOnePlusV_eq :
    leaf3078InputLogOnePlusV = outerEnclosure 24
      (leaf3078Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3078RoundedFacts : LeafRoundedFacts 8
    leaf3078Certificate.logOnePlusV leaf3078InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3078InputLogOnePlusV_eq }

private noncomputable def leaf3078Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi195InputQChi innerPair64Input
    leaf3078InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3078LowerChecked :
    lowerCheck 24 leaf3078Box leaf3078Inputs = true := by
  rfl'

private theorem leaf3078CoversExact : CoversExact 8
    leaf3078Box leaf3078Certificate leaf3078InnerLog leaf3078Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf3078RoundedFacts (by rfl)

private theorem leaf3078FlatSound : Sound leaf3078Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3078CertificateValid
    leaf3078InnerLogValid leaf3078CoversExact leaf3078LowerChecked

private noncomputable def leaf3079Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3079Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486524416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1865597181/1073741824) }, upper := { exponent := 0, mantissa := (14375/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973908787/54973048832) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3079InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3079LocalValidity :
    LeafFacts leaf3079Box leaf3079Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3079Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486524416) }) = true
      norm_num [leaf3079Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3079CertificateValid :
    WideCertificateValid leaf3079Box leaf3079Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi196ValidityFacts
    leaf3079LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3079CoverageChecked :
    coverageCheck (innerAD leaf3079Box) leaf3079InnerLog = true := by
  rfl'

private theorem leaf3079InnerLogValid :
    leaf3079InnerLog.Valid 8 (innerAD leaf3079Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3079CoverageChecked

private noncomputable def leaf3079InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3079InputLogOnePlusV_eq :
    leaf3079InputLogOnePlusV = outerEnclosure 24
      (leaf3079Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3079RoundedFacts : LeafRoundedFacts 8
    leaf3079Certificate.logOnePlusV leaf3079InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3079InputLogOnePlusV_eq }

private noncomputable def leaf3079Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi196InputQChi innerPair430Input
    leaf3079InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3079LowerChecked :
    lowerCheck 24 leaf3079Box leaf3079Inputs = true := by
  rfl'

private theorem leaf3079CoversExact : CoversExact 8
    leaf3079Box leaf3079Certificate leaf3079InnerLog leaf3079Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi196RoundedFacts
    innerPair430RoundedFacts leaf3079RoundedFacts (by rfl)

private theorem leaf3079FlatSound : Sound leaf3079Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3079CertificateValid
    leaf3079InnerLogValid leaf3079CoversExact leaf3079LowerChecked

private noncomputable def leaf3080Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3080Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432594432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1869070375/1073741824) }, upper := { exponent := 0, mantissa := (7201/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869516287/274865188864) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3080InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3080LocalValidity :
    LeafFacts leaf3080Box leaf3080Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3080Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432594432) }) = true
      norm_num [leaf3080Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3080CertificateValid :
    WideCertificateValid leaf3080Box leaf3080Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi196ValidityFacts
    leaf3080LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3080CoverageChecked :
    coverageCheck (innerAD leaf3080Box) leaf3080InnerLog = true := by
  rfl'

private theorem leaf3080InnerLogValid :
    leaf3080InnerLog.Valid 8 (innerAD leaf3080Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3080CoverageChecked

private noncomputable def leaf3080InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3080InputLogOnePlusV_eq :
    leaf3080InputLogOnePlusV = outerEnclosure 24
      (leaf3080Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3080RoundedFacts : LeafRoundedFacts 8
    leaf3080Certificate.logOnePlusV leaf3080InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3080InputLogOnePlusV_eq }

private noncomputable def leaf3080Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi196InputQChi innerPair430Input
    leaf3080InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3080LowerChecked :
    lowerCheck 24 leaf3080Box leaf3080Inputs = true := by
  rfl'

private theorem leaf3080CoversExact : CoversExact 8
    leaf3080Box leaf3080Certificate leaf3080InnerLog leaf3080Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi196RoundedFacts
    innerPair430RoundedFacts leaf3080RoundedFacts (by rfl)

private theorem leaf3080FlatSound : Sound leaf3080Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3080CertificateValid
    leaf3080InnerLogValid leaf3080CoversExact leaf3080LowerChecked

private noncomputable def leaf3081Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3081Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432685056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1857471211/1073741824) }, upper := { exponent := 0, mantissa := (28627/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869606911/274865370112) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3081InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3081LocalValidity :
    LeafFacts leaf3081Box leaf3081Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3081Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432685056) }) = true
      norm_num [leaf3081Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3081CertificateValid :
    WideCertificateValid leaf3081Box leaf3081Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi195ValidityFacts
    leaf3081LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3081CoverageChecked :
    coverageCheck (innerAD leaf3081Box) leaf3081InnerLog = true := by
  rfl'

private theorem leaf3081InnerLogValid :
    leaf3081InnerLog.Valid 8 (innerAD leaf3081Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3081CoverageChecked

private noncomputable def leaf3081InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3081InputLogOnePlusV_eq :
    leaf3081InputLogOnePlusV = outerEnclosure 24
      (leaf3081Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3081RoundedFacts : LeafRoundedFacts 8
    leaf3081Certificate.logOnePlusV leaf3081InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3081InputLogOnePlusV_eq }

private noncomputable def leaf3081Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi195InputQChi innerPair64Input
    leaf3081InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3081LowerChecked :
    lowerCheck 24 leaf3081Box leaf3081Inputs = true := by
  rfl'

private theorem leaf3081CoversExact : CoversExact 8
    leaf3081Box leaf3081Certificate leaf3081InnerLog leaf3081Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf3081RoundedFacts (by rfl)

private theorem leaf3081FlatSound : Sound leaf3081Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3081CertificateValid
    leaf3081InnerLogValid leaf3081CoversExact leaf3081LowerChecked

private noncomputable def leaf3082Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3082Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486531584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1860878873/1073741824) }, upper := { exponent := 0, mantissa := (3585/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973915955/54973063168) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3082InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf3082LocalValidity :
    LeafFacts leaf3082Box leaf3082Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3082Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486531584) }) = true
      norm_num [leaf3082Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3082CertificateValid :
    WideCertificateValid leaf3082Box leaf3082Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi195ValidityFacts
    leaf3082LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3082CoverageChecked :
    coverageCheck (innerAD leaf3082Box) leaf3082InnerLog = true := by
  rfl'

private theorem leaf3082InnerLogValid :
    leaf3082InnerLog.Valid 8 (innerAD leaf3082Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf3082CoverageChecked

private noncomputable def leaf3082InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3082InputLogOnePlusV_eq :
    leaf3082InputLogOnePlusV = outerEnclosure 24
      (leaf3082Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3082RoundedFacts : LeafRoundedFacts 8
    leaf3082Certificate.logOnePlusV leaf3082InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3082InputLogOnePlusV_eq }

private noncomputable def leaf3082Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi195InputQChi innerPair204Input
    leaf3082InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3082LowerChecked :
    lowerCheck 24 leaf3082Box leaf3082Inputs = true := by
  rfl'

private theorem leaf3082CoversExact : CoversExact 8
    leaf3082Box leaf3082Certificate leaf3082InnerLog leaf3082Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi195RoundedFacts
    innerPair204RoundedFacts leaf3082RoundedFacts (by rfl)

private theorem leaf3082FlatSound : Sound leaf3082Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3082CertificateValid
    leaf3082InnerLogValid leaf3082CoversExact leaf3082LowerChecked

private noncomputable def leaf3083Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3083Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432566784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1872543569/1073741824) }, upper := { exponent := 0, mantissa := (14429/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869488639/274865133568) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3083InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3083LocalValidity :
    LeafFacts leaf3083Box leaf3083Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3083Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432566784) }) = true
      norm_num [leaf3083Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3083CertificateValid :
    WideCertificateValid leaf3083Box leaf3083Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi196ValidityFacts
    leaf3083LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3083CoverageChecked :
    coverageCheck (innerAD leaf3083Box) leaf3083InnerLog = true := by
  rfl'

private theorem leaf3083InnerLogValid :
    leaf3083InnerLog.Valid 8 (innerAD leaf3083Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3083CoverageChecked

private noncomputable def leaf3083InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3083InputLogOnePlusV_eq :
    leaf3083InputLogOnePlusV = outerEnclosure 24
      (leaf3083Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3083RoundedFacts : LeafRoundedFacts 8
    leaf3083Certificate.logOnePlusV leaf3083InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3083InputLogOnePlusV_eq }

private noncomputable def leaf3083Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi196InputQChi innerPair430Input
    leaf3083InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3083LowerChecked :
    lowerCheck 24 leaf3083Box leaf3083Inputs = true := by
  rfl'

private theorem leaf3083CoversExact : CoversExact 8
    leaf3083Box leaf3083Certificate leaf3083InnerLog leaf3083Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi196RoundedFacts
    innerPair430RoundedFacts leaf3083RoundedFacts (by rfl)

private theorem leaf3083FlatSound : Sound leaf3083Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3083CertificateValid
    leaf3083InnerLogValid leaf3083CoversExact leaf3083LowerChecked

private noncomputable def leaf3084Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3084Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084267008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1876016763/1073741824) }, upper := { exponent := 0, mantissa := (1807/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168791823/16168534016) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3084InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3084LocalValidity :
    LeafFacts leaf3084Box leaf3084Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3084Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084267008) }) = true
      norm_num [leaf3084Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3084CertificateValid :
    WideCertificateValid leaf3084Box leaf3084Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi196ValidityFacts
    leaf3084LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3084CoverageChecked :
    coverageCheck (innerAD leaf3084Box) leaf3084InnerLog = true := by
  rfl'

private theorem leaf3084InnerLogValid :
    leaf3084InnerLog.Valid 8 (innerAD leaf3084Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3084CoverageChecked

private noncomputable def leaf3084InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3084InputLogOnePlusV_eq :
    leaf3084InputLogOnePlusV = outerEnclosure 24
      (leaf3084Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3084RoundedFacts : LeafRoundedFacts 8
    leaf3084Certificate.logOnePlusV leaf3084InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3084InputLogOnePlusV_eq }

private noncomputable def leaf3084Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi196InputQChi innerPair430Input
    leaf3084InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3084LowerChecked :
    lowerCheck 24 leaf3084Box leaf3084Inputs = true := by
  rfl'

private theorem leaf3084CoversExact : CoversExact 8
    leaf3084Box leaf3084Certificate leaf3084InnerLog leaf3084Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi196RoundedFacts
    innerPair430RoundedFacts leaf3084RoundedFacts (by rfl)

private theorem leaf3084FlatSound : Sound leaf3084Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3084CertificateValid
    leaf3084InnerLogValid leaf3084CoversExact leaf3084LowerChecked

private noncomputable def leaf3085Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3085Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810834944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1880538475/1073741824) }, upper := { exponent := 0, mantissa := (28979/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623142229/91621669888) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3085InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3085LocalValidity :
    LeafFacts leaf3085Box leaf3085Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3085Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810834944) }) = true
      norm_num [leaf3085Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3085CertificateValid :
    WideCertificateValid leaf3085Box leaf3085Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi197ValidityFacts
    leaf3085LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3085CoverageChecked :
    coverageCheck (innerAD leaf3085Box) leaf3085InnerLog = true := by
  rfl'

private theorem leaf3085InnerLogValid :
    leaf3085InnerLog.Valid 8 (innerAD leaf3085Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3085CoverageChecked

private noncomputable def leaf3085InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3085InputLogOnePlusV_eq :
    leaf3085InputLogOnePlusV = outerEnclosure 24
      (leaf3085Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3085RoundedFacts : LeafRoundedFacts 8
    leaf3085Certificate.logOnePlusV leaf3085InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3085InputLogOnePlusV_eq }

private noncomputable def leaf3085Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3085InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3085LowerChecked :
    lowerCheck 24 leaf3085Box leaf3085Inputs = true := by
  rfl'

private theorem leaf3085CoversExact : CoversExact 8
    leaf3085Box leaf3085Certificate leaf3085InnerLog leaf3085Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3085RoundedFacts (by rfl)

private theorem leaf3085FlatSound : Sound leaf3085Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3085CertificateValid
    leaf3085InnerLogValid leaf3085CoversExact leaf3085LowerChecked

private noncomputable def leaf3086Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3086Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432476672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1884077201/1073741824) }, upper := { exponent := 0, mantissa := (14517/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869398527/274864953344) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3086InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3086LocalValidity :
    LeafFacts leaf3086Box leaf3086Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3086Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432476672) }) = true
      norm_num [leaf3086Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3086CertificateValid :
    WideCertificateValid leaf3086Box leaf3086Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi197ValidityFacts
    leaf3086LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3086CoverageChecked :
    coverageCheck (innerAD leaf3086Box) leaf3086InnerLog = true := by
  rfl'

private theorem leaf3086InnerLogValid :
    leaf3086InnerLog.Valid 8 (innerAD leaf3086Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3086CoverageChecked

private noncomputable def leaf3086InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3086InputLogOnePlusV_eq :
    leaf3086InputLogOnePlusV = outerEnclosure 24
      (leaf3086Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3086RoundedFacts : LeafRoundedFacts 8
    leaf3086Certificate.logOnePlusV leaf3086InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3086InputLogOnePlusV_eq }

private noncomputable def leaf3086Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3086InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3086LowerChecked :
    lowerCheck 24 leaf3086Box leaf3086Inputs = true := by
  rfl'

private theorem leaf3086CoversExact : CoversExact 8
    leaf3086Box leaf3086Certificate leaf3086InnerLog leaf3086Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3086RoundedFacts (by rfl)

private theorem leaf3086FlatSound : Sound leaf3086Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3086CertificateValid
    leaf3086InnerLogValid leaf3086CoversExact leaf3086LowerChecked

private noncomputable def leaf3087Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3087Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432387584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1895479769/1073741824) }, upper := { exponent := 0, mantissa := (3651/2048) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869309439/274864775168) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3087InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3087LocalValidity :
    LeafFacts leaf3087Box leaf3087Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3087Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432387584) }) = true
      norm_num [leaf3087Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3087CertificateValid :
    WideCertificateValid leaf3087Box leaf3087Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi198ValidityFacts
    leaf3087LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3087CoverageChecked :
    coverageCheck (innerAD leaf3087Box) leaf3087InnerLog = true := by
  rfl'

private theorem leaf3087InnerLogValid :
    leaf3087InnerLog.Valid 8 (innerAD leaf3087Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3087CoverageChecked

private noncomputable def leaf3087InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3087InputLogOnePlusV_eq :
    leaf3087InputLogOnePlusV = outerEnclosure 24
      (leaf3087Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3087RoundedFacts : LeafRoundedFacts 8
    leaf3087Certificate.logOnePlusV leaf3087InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3087InputLogOnePlusV_eq }

private noncomputable def leaf3087Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3087InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3087LowerChecked :
    lowerCheck 24 leaf3087Box leaf3087Inputs = true := by
  rfl'

private theorem leaf3087CoversExact : CoversExact 8
    leaf3087Box leaf3087Certificate leaf3087InnerLog leaf3087Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3087RoundedFacts (by rfl)

private theorem leaf3087FlatSound : Sound leaf3087Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3087CertificateValid
    leaf3087InnerLogValid leaf3087CoversExact leaf3087LowerChecked

private noncomputable def leaf3088Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3088Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810786304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1899084027/1073741824) }, upper := { exponent := 0, mantissa := (1829/1024) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623093589/91621572608) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3088InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3088LocalValidity :
    LeafFacts leaf3088Box leaf3088Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3088Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810786304) }) = true
      norm_num [leaf3088Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3088CertificateValid :
    WideCertificateValid leaf3088Box leaf3088Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi198ValidityFacts
    leaf3088LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3088CoverageChecked :
    coverageCheck (innerAD leaf3088Box) leaf3088InnerLog = true := by
  rfl'

private theorem leaf3088InnerLogValid :
    leaf3088InnerLog.Valid 8 (innerAD leaf3088Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3088CoverageChecked

private noncomputable def leaf3088InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3088InputLogOnePlusV_eq :
    leaf3088InputLogOnePlusV = outerEnclosure 24
      (leaf3088Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3088RoundedFacts : LeafRoundedFacts 8
    leaf3088Certificate.logOnePlusV leaf3088InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3088InputLogOnePlusV_eq }

private noncomputable def leaf3088Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3088InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3088LowerChecked :
    lowerCheck 24 leaf3088Box leaf3088Inputs = true := by
  rfl'

private theorem leaf3088CoversExact : CoversExact 8
    leaf3088Box leaf3088Certificate leaf3088InnerLog leaf3088Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3088RoundedFacts (by rfl)

private theorem leaf3088FlatSound : Sound leaf3088Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3088CertificateValid
    leaf3088InnerLogValid leaf3088CoversExact leaf3088LowerChecked

private noncomputable def leaf3089Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3089Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432448512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1887615927/1073741824) }, upper := { exponent := 0, mantissa := (29089/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869370367/274864897024) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3089InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3089LocalValidity :
    LeafFacts leaf3089Box leaf3089Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3089Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432448512) }) = true
      norm_num [leaf3089Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3089CertificateValid :
    WideCertificateValid leaf3089Box leaf3089Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi197ValidityFacts
    leaf3089LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3089CoverageChecked :
    coverageCheck (innerAD leaf3089Box) leaf3089InnerLog = true := by
  rfl'

private theorem leaf3089InnerLogValid :
    leaf3089InnerLog.Valid 8 (innerAD leaf3089Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3089CoverageChecked

private noncomputable def leaf3089InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3089InputLogOnePlusV_eq :
    leaf3089InputLogOnePlusV = outerEnclosure 24
      (leaf3089Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3089RoundedFacts : LeafRoundedFacts 8
    leaf3089Certificate.logOnePlusV leaf3089InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3089InputLogOnePlusV_eq }

private noncomputable def leaf3089Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3089InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3089LowerChecked :
    lowerCheck 24 leaf3089Box leaf3089Inputs = true := by
  rfl'

private theorem leaf3089CoversExact : CoversExact 8
    leaf3089Box leaf3089Certificate leaf3089InnerLog leaf3089Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3089RoundedFacts (by rfl)

private theorem leaf3089FlatSound : Sound leaf3089Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3089CertificateValid
    leaf3089InnerLogValid leaf3089CoversExact leaf3089LowerChecked

private noncomputable def leaf3090Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3090Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270268928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1891154653/1073741824) }, upper := { exponent := 0, mantissa := (3643/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541038023/30540537856) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3090InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3090LocalValidity :
    LeafFacts leaf3090Box leaf3090Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3090Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270268928) }) = true
      norm_num [leaf3090Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3090CertificateValid :
    WideCertificateValid leaf3090Box leaf3090Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi197ValidityFacts
    leaf3090LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3090CoverageChecked :
    coverageCheck (innerAD leaf3090Box) leaf3090InnerLog = true := by
  rfl'

private theorem leaf3090InnerLogValid :
    leaf3090InnerLog.Valid 8 (innerAD leaf3090Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3090CoverageChecked

private noncomputable def leaf3090InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3090InputLogOnePlusV_eq :
    leaf3090InputLogOnePlusV = outerEnclosure 24
      (leaf3090Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3090RoundedFacts : LeafRoundedFacts 8
    leaf3090Certificate.logOnePlusV leaf3090InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3090InputLogOnePlusV_eq }

private noncomputable def leaf3090Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3090InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3090LowerChecked :
    lowerCheck 24 leaf3090Box leaf3090Inputs = true := by
  rfl'

private theorem leaf3090CoversExact : CoversExact 8
    leaf3090Box leaf3090Certificate leaf3090InnerLog leaf3090Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3090RoundedFacts (by rfl)

private theorem leaf3090FlatSound : Sound leaf3090Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3090CertificateValid
    leaf3090InnerLogValid leaf3090CoversExact leaf3090LowerChecked

private noncomputable def leaf3091Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3091Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1616904963/1616850944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1902688285/1073741824) }, upper := { exponent := 0, mantissa := (3665/2048) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3233755907/3233701888) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3091InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3091LocalValidity :
    LeafFacts leaf3091Box leaf3091Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3091Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1616904963/1616850944) }) = true
      norm_num [leaf3091Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3091CertificateValid :
    WideCertificateValid leaf3091Box leaf3091Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi198ValidityFacts
    leaf3091LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3091CoverageChecked :
    coverageCheck (innerAD leaf3091Box) leaf3091InnerLog = true := by
  rfl'

private theorem leaf3091InnerLogValid :
    leaf3091InnerLog.Valid 8 (innerAD leaf3091Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3091CoverageChecked

private noncomputable def leaf3091InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3091InputLogOnePlusV_eq :
    leaf3091InputLogOnePlusV = outerEnclosure 24
      (leaf3091Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3091RoundedFacts : LeafRoundedFacts 8
    leaf3091Certificate.logOnePlusV leaf3091InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3091InputLogOnePlusV_eq }

private noncomputable def leaf3091Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3091InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3091LowerChecked :
    lowerCheck 24 leaf3091Box leaf3091Inputs = true := by
  rfl'

private theorem leaf3091CoversExact : CoversExact 8
    leaf3091Box leaf3091Certificate leaf3091InnerLog leaf3091Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3091RoundedFacts (by rfl)

private theorem leaf3091FlatSound : Sound leaf3091Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3091CertificateValid
    leaf3091InnerLogValid leaf3091CoversExact leaf3091LowerChecked

private noncomputable def leaf3092Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3092Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432301568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1906292543/1073741824) }, upper := { exponent := 0, mantissa := (459/256) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869223423/274864603136) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3092InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3092LocalValidity :
    LeafFacts leaf3092Box leaf3092Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3092Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432301568) }) = true
      norm_num [leaf3092Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3092CertificateValid :
    WideCertificateValid leaf3092Box leaf3092Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi198ValidityFacts
    leaf3092LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3092CoverageChecked :
    coverageCheck (innerAD leaf3092Box) leaf3092InnerLog = true := by
  rfl'

private theorem leaf3092InnerLogValid :
    leaf3092InnerLog.Valid 8 (innerAD leaf3092Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3092CoverageChecked

private noncomputable def leaf3092InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3092InputLogOnePlusV_eq :
    leaf3092InputLogOnePlusV = outerEnclosure 24
      (leaf3092Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3092RoundedFacts : LeafRoundedFacts 8
    leaf3092Certificate.logOnePlusV leaf3092InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3092InputLogOnePlusV_eq }

private noncomputable def leaf3092Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi198InputQChi innerPair71Input
    leaf3092InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3092LowerChecked :
    lowerCheck 24 leaf3092Box leaf3092Inputs = true := by
  rfl'

private theorem leaf3092CoversExact : CoversExact 8
    leaf3092Box leaf3092Certificate leaf3092InnerLog leaf3092Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi198RoundedFacts
    innerPair71RoundedFacts leaf3092RoundedFacts (by rfl)

private theorem leaf3092FlatSound : Sound leaf3092Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3092CertificateValid
    leaf3092InnerLogValid leaf3092CoversExact leaf3092LowerChecked

private noncomputable def component64Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node0_sound : Sound component64Node0Box :=
  sound_of_literal_split component64Node0Box leaf3029Box leaf3030Box
    .k (225/64) (by rfl) (by rfl)
    leaf3029FlatSound leaf3030FlatSound

private noncomputable def component64Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node1_sound : Sound component64Node1Box :=
  sound_of_literal_split component64Node1Box leaf3031Box leaf3032Box
    .k (225/64) (by rfl) (by rfl)
    leaf3031FlatSound leaf3032FlatSound

private noncomputable def component64Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node2_sound : Sound component64Node2Box :=
  sound_of_literal_split component64Node2Box component64Node0Box component64Node1Box
    .chi (49/256) (by rfl) (by rfl)
    component64Node0_sound component64Node1_sound

private noncomputable def component64Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node3_sound : Sound component64Node3Box :=
  sound_of_literal_split component64Node3Box leaf3033Box leaf3034Box
    .k (227/64) (by rfl) (by rfl)
    leaf3033FlatSound leaf3034FlatSound

private noncomputable def component64Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node4_sound : Sound component64Node4Box :=
  sound_of_literal_split component64Node4Box leaf3035Box leaf3036Box
    .k (227/64) (by rfl) (by rfl)
    leaf3035FlatSound leaf3036FlatSound

private noncomputable def component64Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node5_sound : Sound component64Node5Box :=
  sound_of_literal_split component64Node5Box component64Node3Box component64Node4Box
    .chi (49/256) (by rfl) (by rfl)
    component64Node3_sound component64Node4_sound

private noncomputable def component64Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node6_sound : Sound component64Node6Box :=
  sound_of_literal_split component64Node6Box component64Node2Box component64Node5Box
    .k (113/32) (by rfl) (by rfl)
    component64Node2_sound component64Node5_sound

private noncomputable def component64Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node7_sound : Sound component64Node7Box :=
  sound_of_literal_split component64Node7Box leaf3037Box leaf3038Box
    .k (225/64) (by rfl) (by rfl)
    leaf3037FlatSound leaf3038FlatSound

private noncomputable def component64Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node8_sound : Sound component64Node8Box :=
  sound_of_literal_split component64Node8Box leaf3039Box leaf3040Box
    .k (225/64) (by rfl) (by rfl)
    leaf3039FlatSound leaf3040FlatSound

private noncomputable def component64Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node9_sound : Sound component64Node9Box :=
  sound_of_literal_split component64Node9Box component64Node7Box component64Node8Box
    .chi (51/256) (by rfl) (by rfl)
    component64Node7_sound component64Node8_sound

private noncomputable def component64Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node10_sound : Sound component64Node10Box :=
  sound_of_literal_split component64Node10Box leaf3041Box leaf3042Box
    .k (227/64) (by rfl) (by rfl)
    leaf3041FlatSound leaf3042FlatSound

private noncomputable def component64Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node11_sound : Sound component64Node11Box :=
  sound_of_literal_split component64Node11Box leaf3043Box leaf3044Box
    .k (227/64) (by rfl) (by rfl)
    leaf3043FlatSound leaf3044FlatSound

private noncomputable def component64Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node12_sound : Sound component64Node12Box :=
  sound_of_literal_split component64Node12Box component64Node10Box component64Node11Box
    .chi (51/256) (by rfl) (by rfl)
    component64Node10_sound component64Node11_sound

private noncomputable def component64Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node13_sound : Sound component64Node13Box :=
  sound_of_literal_split component64Node13Box component64Node9Box component64Node12Box
    .k (113/32) (by rfl) (by rfl)
    component64Node9_sound component64Node12_sound

private noncomputable def component64Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node14_sound : Sound component64Node14Box :=
  sound_of_literal_split component64Node14Box component64Node6Box component64Node13Box
    .chi (25/128) (by rfl) (by rfl)
    component64Node6_sound component64Node13_sound

private noncomputable def component64Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node15_sound : Sound component64Node15Box :=
  sound_of_literal_split component64Node15Box leaf3045Box leaf3046Box
    .k (229/64) (by rfl) (by rfl)
    leaf3045FlatSound leaf3046FlatSound

private noncomputable def component64Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node16_sound : Sound component64Node16Box :=
  sound_of_literal_split component64Node16Box leaf3047Box leaf3048Box
    .k (229/64) (by rfl) (by rfl)
    leaf3047FlatSound leaf3048FlatSound

private noncomputable def component64Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node17_sound : Sound component64Node17Box :=
  sound_of_literal_split component64Node17Box component64Node15Box component64Node16Box
    .chi (49/256) (by rfl) (by rfl)
    component64Node15_sound component64Node16_sound

private noncomputable def component64Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node18_sound : Sound component64Node18Box :=
  sound_of_literal_split component64Node18Box leaf3049Box leaf3050Box
    .k (231/64) (by rfl) (by rfl)
    leaf3049FlatSound leaf3050FlatSound

private noncomputable def component64Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node19_sound : Sound component64Node19Box :=
  sound_of_literal_split component64Node19Box leaf3051Box leaf3052Box
    .k (231/64) (by rfl) (by rfl)
    leaf3051FlatSound leaf3052FlatSound

private noncomputable def component64Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node20_sound : Sound component64Node20Box :=
  sound_of_literal_split component64Node20Box component64Node18Box component64Node19Box
    .chi (49/256) (by rfl) (by rfl)
    component64Node18_sound component64Node19_sound

private noncomputable def component64Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node21_sound : Sound component64Node21Box :=
  sound_of_literal_split component64Node21Box component64Node17Box component64Node20Box
    .k (115/32) (by rfl) (by rfl)
    component64Node17_sound component64Node20_sound

private noncomputable def component64Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node22_sound : Sound component64Node22Box :=
  sound_of_literal_split component64Node22Box leaf3053Box leaf3054Box
    .k (229/64) (by rfl) (by rfl)
    leaf3053FlatSound leaf3054FlatSound

private noncomputable def component64Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node23_sound : Sound component64Node23Box :=
  sound_of_literal_split component64Node23Box leaf3055Box leaf3056Box
    .k (229/64) (by rfl) (by rfl)
    leaf3055FlatSound leaf3056FlatSound

private noncomputable def component64Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node24_sound : Sound component64Node24Box :=
  sound_of_literal_split component64Node24Box component64Node22Box component64Node23Box
    .chi (51/256) (by rfl) (by rfl)
    component64Node22_sound component64Node23_sound

private noncomputable def component64Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node25_sound : Sound component64Node25Box :=
  sound_of_literal_split component64Node25Box leaf3057Box leaf3058Box
    .k (231/64) (by rfl) (by rfl)
    leaf3057FlatSound leaf3058FlatSound

private noncomputable def component64Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node26_sound : Sound component64Node26Box :=
  sound_of_literal_split component64Node26Box leaf3059Box leaf3060Box
    .k (231/64) (by rfl) (by rfl)
    leaf3059FlatSound leaf3060FlatSound

private noncomputable def component64Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node27_sound : Sound component64Node27Box :=
  sound_of_literal_split component64Node27Box component64Node25Box component64Node26Box
    .chi (51/256) (by rfl) (by rfl)
    component64Node25_sound component64Node26_sound

private noncomputable def component64Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node28_sound : Sound component64Node28Box :=
  sound_of_literal_split component64Node28Box component64Node24Box component64Node27Box
    .k (115/32) (by rfl) (by rfl)
    component64Node24_sound component64Node27_sound

private noncomputable def component64Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node29_sound : Sound component64Node29Box :=
  sound_of_literal_split component64Node29Box component64Node21Box component64Node28Box
    .chi (25/128) (by rfl) (by rfl)
    component64Node21_sound component64Node28_sound

private noncomputable def component64Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component64Node30_sound : Sound component64Node30Box :=
  sound_of_literal_split component64Node30Box component64Node14Box component64Node29Box
    .k (57/16) (by rfl) (by rfl)
    component64Node14_sound component64Node29_sound

private noncomputable def component64Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node31_sound : Sound component64Node31Box :=
  sound_of_literal_split component64Node31Box leaf3061Box leaf3062Box
    .chi (53/256) (by rfl) (by rfl)
    leaf3061FlatSound leaf3062FlatSound

private noncomputable def component64Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node32_sound : Sound component64Node32Box :=
  sound_of_literal_split component64Node32Box leaf3063Box leaf3064Box
    .chi (53/256) (by rfl) (by rfl)
    leaf3063FlatSound leaf3064FlatSound

private noncomputable def component64Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node33_sound : Sound component64Node33Box :=
  sound_of_literal_split component64Node33Box component64Node31Box component64Node32Box
    .k (225/64) (by rfl) (by rfl)
    component64Node31_sound component64Node32_sound

private noncomputable def component64Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node34_sound : Sound component64Node34Box :=
  sound_of_literal_split component64Node34Box leaf3065Box leaf3066Box
    .chi (53/256) (by rfl) (by rfl)
    leaf3065FlatSound leaf3066FlatSound

private noncomputable def component64Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node35_sound : Sound component64Node35Box :=
  sound_of_literal_split component64Node35Box leaf3067Box leaf3068Box
    .chi (53/256) (by rfl) (by rfl)
    leaf3067FlatSound leaf3068FlatSound

private noncomputable def component64Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node36_sound : Sound component64Node36Box :=
  sound_of_literal_split component64Node36Box component64Node34Box component64Node35Box
    .k (227/64) (by rfl) (by rfl)
    component64Node34_sound component64Node35_sound

private noncomputable def component64Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node37_sound : Sound component64Node37Box :=
  sound_of_literal_split component64Node37Box component64Node33Box component64Node36Box
    .k (113/32) (by rfl) (by rfl)
    component64Node33_sound component64Node36_sound

private noncomputable def component64Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node38_sound : Sound component64Node38Box :=
  sound_of_literal_split component64Node38Box leaf3069Box leaf3070Box
    .k (225/64) (by rfl) (by rfl)
    leaf3069FlatSound leaf3070FlatSound

private noncomputable def component64Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node39_sound : Sound component64Node39Box :=
  sound_of_literal_split component64Node39Box leaf3071Box leaf3072Box
    .k (225/64) (by rfl) (by rfl)
    leaf3071FlatSound leaf3072FlatSound

private noncomputable def component64Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node40_sound : Sound component64Node40Box :=
  sound_of_literal_split component64Node40Box component64Node38Box component64Node39Box
    .chi (55/256) (by rfl) (by rfl)
    component64Node38_sound component64Node39_sound

private noncomputable def component64Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node41_sound : Sound component64Node41Box :=
  sound_of_literal_split component64Node41Box leaf3073Box leaf3074Box
    .k (227/64) (by rfl) (by rfl)
    leaf3073FlatSound leaf3074FlatSound

private noncomputable def component64Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node42_sound : Sound component64Node42Box :=
  sound_of_literal_split component64Node42Box leaf3075Box leaf3076Box
    .k (227/64) (by rfl) (by rfl)
    leaf3075FlatSound leaf3076FlatSound

private noncomputable def component64Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node43_sound : Sound component64Node43Box :=
  sound_of_literal_split component64Node43Box component64Node41Box component64Node42Box
    .chi (55/256) (by rfl) (by rfl)
    component64Node41_sound component64Node42_sound

private noncomputable def component64Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node44_sound : Sound component64Node44Box :=
  sound_of_literal_split component64Node44Box component64Node40Box component64Node43Box
    .k (113/32) (by rfl) (by rfl)
    component64Node40_sound component64Node43_sound

private noncomputable def component64Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node45_sound : Sound component64Node45Box :=
  sound_of_literal_split component64Node45Box component64Node37Box component64Node44Box
    .chi (27/128) (by rfl) (by rfl)
    component64Node37_sound component64Node44_sound

private noncomputable def component64Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node46_sound : Sound component64Node46Box :=
  sound_of_literal_split component64Node46Box leaf3077Box leaf3078Box
    .k (229/64) (by rfl) (by rfl)
    leaf3077FlatSound leaf3078FlatSound

private noncomputable def component64Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node47_sound : Sound component64Node47Box :=
  sound_of_literal_split component64Node47Box leaf3079Box leaf3080Box
    .k (229/64) (by rfl) (by rfl)
    leaf3079FlatSound leaf3080FlatSound

private noncomputable def component64Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node48_sound : Sound component64Node48Box :=
  sound_of_literal_split component64Node48Box component64Node46Box component64Node47Box
    .chi (53/256) (by rfl) (by rfl)
    component64Node46_sound component64Node47_sound

private noncomputable def component64Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node49_sound : Sound component64Node49Box :=
  sound_of_literal_split component64Node49Box leaf3081Box leaf3082Box
    .k (231/64) (by rfl) (by rfl)
    leaf3081FlatSound leaf3082FlatSound

private noncomputable def component64Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node50_sound : Sound component64Node50Box :=
  sound_of_literal_split component64Node50Box leaf3083Box leaf3084Box
    .k (231/64) (by rfl) (by rfl)
    leaf3083FlatSound leaf3084FlatSound

private noncomputable def component64Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node51_sound : Sound component64Node51Box :=
  sound_of_literal_split component64Node51Box component64Node49Box component64Node50Box
    .chi (53/256) (by rfl) (by rfl)
    component64Node49_sound component64Node50_sound

private noncomputable def component64Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component64Node52_sound : Sound component64Node52Box :=
  sound_of_literal_split component64Node52Box component64Node48Box component64Node51Box
    .k (115/32) (by rfl) (by rfl)
    component64Node48_sound component64Node51_sound

private noncomputable def component64Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node53_sound : Sound component64Node53Box :=
  sound_of_literal_split component64Node53Box leaf3085Box leaf3086Box
    .k (229/64) (by rfl) (by rfl)
    leaf3085FlatSound leaf3086FlatSound

private noncomputable def component64Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node54_sound : Sound component64Node54Box :=
  sound_of_literal_split component64Node54Box leaf3087Box leaf3088Box
    .k (229/64) (by rfl) (by rfl)
    leaf3087FlatSound leaf3088FlatSound

private noncomputable def component64Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node55_sound : Sound component64Node55Box :=
  sound_of_literal_split component64Node55Box component64Node53Box component64Node54Box
    .chi (55/256) (by rfl) (by rfl)
    component64Node53_sound component64Node54_sound

private noncomputable def component64Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component64Node56_sound : Sound component64Node56Box :=
  sound_of_literal_split component64Node56Box leaf3089Box leaf3090Box
    .k (231/64) (by rfl) (by rfl)
    leaf3089FlatSound leaf3090FlatSound

private noncomputable def component64Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node57_sound : Sound component64Node57Box :=
  sound_of_literal_split component64Node57Box leaf3091Box leaf3092Box
    .k (231/64) (by rfl) (by rfl)
    leaf3091FlatSound leaf3092FlatSound

private noncomputable def component64Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node58_sound : Sound component64Node58Box :=
  sound_of_literal_split component64Node58Box component64Node56Box component64Node57Box
    .chi (55/256) (by rfl) (by rfl)
    component64Node56_sound component64Node57_sound

private noncomputable def component64Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node59_sound : Sound component64Node59Box :=
  sound_of_literal_split component64Node59Box component64Node55Box component64Node58Box
    .k (115/32) (by rfl) (by rfl)
    component64Node55_sound component64Node58_sound

private noncomputable def component64Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node60_sound : Sound component64Node60Box :=
  sound_of_literal_split component64Node60Box component64Node52Box component64Node59Box
    .chi (27/128) (by rfl) (by rfl)
    component64Node52_sound component64Node59_sound

private noncomputable def component64Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component64Node61_sound : Sound component64Node61Box :=
  sound_of_literal_split component64Node61Box component64Node45Box component64Node60Box
    .k (57/16) (by rfl) (by rfl)
    component64Node45_sound component64Node60_sound

noncomputable def component64Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component64_sound : Sound component64Box :=
  sound_of_literal_split component64Box component64Node30Box component64Node61Box
    .chi (13/64) (by rfl) (by rfl)
    component64Node30_sound component64Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
