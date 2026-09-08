import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf2623Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2623Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434230272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1660875247/1073741824) }, upper := { exponent := 0, mantissa := (25609/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871152127/274868460544) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2623InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2623LocalValidity :
    LeafFacts leaf2623Box leaf2623Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2623Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434230272) }) = true
      norm_num [leaf2623Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2623CertificateValid :
    WideCertificateValid leaf2623Box leaf2623Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi183ValidityFacts
    leaf2623LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2623CoverageChecked :
    coverageCheck (innerAD leaf2623Box) leaf2623InnerLog = true := by
  rfl'

private theorem leaf2623InnerLogValid :
    leaf2623InnerLog.Valid 8 (innerAD leaf2623Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2623CoverageChecked

private noncomputable def leaf2623InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2623InputLogOnePlusV_eq :
    leaf2623InputLogOnePlusV = outerEnclosure 24
      (leaf2623Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2623RoundedFacts : LeafRoundedFacts 8
    leaf2623Certificate.logOnePlusV leaf2623InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2623InputLogOnePlusV_eq }

private noncomputable def leaf2623Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi183InputQChi innerPair41Input
    leaf2623InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2623LowerChecked :
    lowerCheck 24 leaf2623Box leaf2623Inputs = true := by
  rfl'

private theorem leaf2623CoversExact : CoversExact 8
    leaf2623Box leaf2623Certificate leaf2623InnerLog leaf2623Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi183RoundedFacts
    innerPair41RoundedFacts leaf2623RoundedFacts (by rfl)

private theorem leaf2623FlatSound : Sound leaf2623Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2623CertificateValid
    leaf2623InnerLogValid leaf2623CoversExact leaf2623LowerChecked

private noncomputable def leaf2624Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2624Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486841856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1663496525/1073741824) }, upper := { exponent := 0, mantissa := (12825/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974226227/54973683712) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2624InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2624LocalValidity :
    LeafFacts leaf2624Box leaf2624Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2624Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486841856) }) = true
      norm_num [leaf2624Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2624CertificateValid :
    WideCertificateValid leaf2624Box leaf2624Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi183ValidityFacts
    leaf2624LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2624CoverageChecked :
    coverageCheck (innerAD leaf2624Box) leaf2624InnerLog = true := by
  rfl'

private theorem leaf2624InnerLogValid :
    leaf2624InnerLog.Valid 8 (innerAD leaf2624Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2624CoverageChecked

private noncomputable def leaf2624InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2624InputLogOnePlusV_eq :
    leaf2624InputLogOnePlusV = outerEnclosure 24
      (leaf2624Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2624RoundedFacts : LeafRoundedFacts 8
    leaf2624Certificate.logOnePlusV leaf2624InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2624InputLogOnePlusV_eq }

private noncomputable def leaf2624Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi183InputQChi innerPair41Input
    leaf2624InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2624LowerChecked :
    lowerCheck 24 leaf2624Box leaf2624Inputs = true := by
  rfl'

private theorem leaf2624CoversExact : CoversExact 8
    leaf2624Box leaf2624Certificate leaf2624InnerLog leaf2624Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi183RoundedFacts
    innerPair41RoundedFacts leaf2624RoundedFacts (by rfl)

private theorem leaf2624FlatSound : Sound leaf2624Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2624CertificateValid
    leaf2624InnerLogValid leaf2624CoversExact leaf2624LowerChecked

private noncomputable def leaf2625Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2625Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434115072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1675554413/1073741824) }, upper := { exponent := 0, mantissa := (12917/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871036927/274868230144) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2625InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2625LocalValidity :
    LeafFacts leaf2625Box leaf2625Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2625Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434115072) }) = true
      norm_num [leaf2625Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2625CertificateValid :
    WideCertificateValid leaf2625Box leaf2625Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi184ValidityFacts
    leaf2625LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2625CoverageChecked :
    coverageCheck (innerAD leaf2625Box) leaf2625InnerLog = true := by
  rfl'

private theorem leaf2625InnerLogValid :
    leaf2625InnerLog.Valid 8 (innerAD leaf2625Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2625CoverageChecked

private noncomputable def leaf2625InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2625InputLogOnePlusV_eq :
    leaf2625InputLogOnePlusV = outerEnclosure 24
      (leaf2625Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2625RoundedFacts : LeafRoundedFacts 8
    leaf2625Certificate.logOnePlusV leaf2625InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2625InputLogOnePlusV_eq }

private noncomputable def leaf2625Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi184InputQChi innerPair41Input
    leaf2625InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2625LowerChecked :
    lowerCheck 24 leaf2625Box leaf2625Inputs = true := by
  rfl'

private theorem leaf2625CoversExact : CoversExact 8
    leaf2625Box leaf2625Certificate leaf2625InnerLog leaf2625Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi184RoundedFacts
    innerPair41RoundedFacts leaf2625RoundedFacts (by rfl)

private theorem leaf2625FlatSound : Sound leaf2625Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2625CertificateValid
    leaf2625InnerLogValid leaf2625CoversExact leaf2625LowerChecked

private noncomputable def leaf2626Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2626Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434093568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1678241223/1073741824) }, upper := { exponent := 0, mantissa := (6469/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871015423/274868187136) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2626InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2626LocalValidity :
    LeafFacts leaf2626Box leaf2626Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2626Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434093568) }) = true
      norm_num [leaf2626Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2626CertificateValid :
    WideCertificateValid leaf2626Box leaf2626Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi184ValidityFacts
    leaf2626LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2626CoverageChecked :
    coverageCheck (innerAD leaf2626Box) leaf2626InnerLog = true := by
  rfl'

private theorem leaf2626InnerLogValid :
    leaf2626InnerLog.Valid 8 (innerAD leaf2626Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2626CoverageChecked

private noncomputable def leaf2626InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2626InputLogOnePlusV_eq :
    leaf2626InputLogOnePlusV = outerEnclosure 24
      (leaf2626Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2626RoundedFacts : LeafRoundedFacts 8
    leaf2626Certificate.logOnePlusV leaf2626InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2626InputLogOnePlusV_eq }

private noncomputable def leaf2626Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2626InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2626LowerChecked :
    lowerCheck 24 leaf2626Box leaf2626Inputs = true := by
  rfl'

private theorem leaf2626CoversExact : CoversExact 8
    leaf2626Box leaf2626Certificate leaf2626InnerLog leaf2626Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2626RoundedFacts (by rfl)

private theorem leaf2626FlatSound : Sound leaf2626Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2626CertificateValid
    leaf2626InnerLogValid leaf2626CoversExact leaf2626LowerChecked

private noncomputable def leaf2627Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2627Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811396096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1666117803/1073741824) }, upper := { exponent := 0, mantissa := (25691/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623703381/91622792192) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2627InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2627LocalValidity :
    LeafFacts leaf2627Box leaf2627Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2627Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811396096) }) = true
      norm_num [leaf2627Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2627CertificateValid :
    WideCertificateValid leaf2627Box leaf2627Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi183ValidityFacts
    leaf2627LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2627CoverageChecked :
    coverageCheck (innerAD leaf2627Box) leaf2627InnerLog = true := by
  rfl'

private theorem leaf2627InnerLogValid :
    leaf2627InnerLog.Valid 8 (innerAD leaf2627Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2627CoverageChecked

private noncomputable def leaf2627InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2627InputLogOnePlusV_eq :
    leaf2627InputLogOnePlusV = outerEnclosure 24
      (leaf2627Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2627RoundedFacts : LeafRoundedFacts 8
    leaf2627Certificate.logOnePlusV leaf2627InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2627InputLogOnePlusV_eq }

private noncomputable def leaf2627Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi183InputQChi innerPair41Input
    leaf2627InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2627LowerChecked :
    lowerCheck 24 leaf2627Box leaf2627Inputs = true := by
  rfl'

private theorem leaf2627CoversExact : CoversExact 8
    leaf2627Box leaf2627Certificate leaf2627InnerLog leaf2627Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi183RoundedFacts
    innerPair41RoundedFacts leaf2627RoundedFacts (by rfl)

private theorem leaf2627FlatSound : Sound leaf2627Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2627CertificateValid
    leaf2627InnerLogValid leaf2627CoversExact leaf2627LowerChecked

private noncomputable def leaf2628Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2628Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434167296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1668739081/1073741824) }, upper := { exponent := 0, mantissa := (6433/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871089151/274868334592) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2628InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2628LocalValidity :
    LeafFacts leaf2628Box leaf2628Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2628Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434167296) }) = true
      norm_num [leaf2628Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2628CertificateValid :
    WideCertificateValid leaf2628Box leaf2628Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi183ValidityFacts
    leaf2628LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2628CoverageChecked :
    coverageCheck (innerAD leaf2628Box) leaf2628InnerLog = true := by
  rfl'

private theorem leaf2628InnerLogValid :
    leaf2628InnerLog.Valid 8 (innerAD leaf2628Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2628CoverageChecked

private noncomputable def leaf2628InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2628InputLogOnePlusV_eq :
    leaf2628InputLogOnePlusV = outerEnclosure 24
      (leaf2628Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2628RoundedFacts : LeafRoundedFacts 8
    leaf2628Certificate.logOnePlusV leaf2628InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2628InputLogOnePlusV_eq }

private noncomputable def leaf2628Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi183InputQChi innerPair41Input
    leaf2628InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2628LowerChecked :
    lowerCheck 24 leaf2628Box leaf2628Inputs = true := by
  rfl'

private theorem leaf2628CoversExact : CoversExact 8
    leaf2628Box leaf2628Certificate leaf2628InnerLog leaf2628Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi183RoundedFacts
    innerPair41RoundedFacts leaf2628RoundedFacts (by rfl)

private theorem leaf2628FlatSound : Sound leaf2628Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2628CertificateValid
    leaf2628InnerLogValid leaf2628CoversExact leaf2628LowerChecked

private noncomputable def leaf2629Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2629Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434072064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1680928033/1073741824) }, upper := { exponent := 0, mantissa := (12959/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870993919/274868144128) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2629InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2629LocalValidity :
    LeafFacts leaf2629Box leaf2629Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2629Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434072064) }) = true
      norm_num [leaf2629Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2629CertificateValid :
    WideCertificateValid leaf2629Box leaf2629Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi184ValidityFacts
    leaf2629LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2629CoverageChecked :
    coverageCheck (innerAD leaf2629Box) leaf2629InnerLog = true := by
  rfl'

private theorem leaf2629InnerLogValid :
    leaf2629InnerLog.Valid 8 (innerAD leaf2629Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2629CoverageChecked

private noncomputable def leaf2629InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2629InputLogOnePlusV_eq :
    leaf2629InputLogOnePlusV = outerEnclosure 24
      (leaf2629Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2629RoundedFacts : LeafRoundedFacts 8
    leaf2629Certificate.logOnePlusV leaf2629InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2629InputLogOnePlusV_eq }

private noncomputable def leaf2629Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2629InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2629LowerChecked :
    lowerCheck 24 leaf2629Box leaf2629Inputs = true := by
  rfl'

private theorem leaf2629CoversExact : CoversExact 8
    leaf2629Box leaf2629Certificate leaf2629InnerLog leaf2629Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2629RoundedFacts (by rfl)

private theorem leaf2629FlatSound : Sound leaf2629Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2629CertificateValid
    leaf2629InnerLogValid leaf2629CoversExact leaf2629LowerChecked

private noncomputable def leaf2630Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2630Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486810112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1683614843/1073741824) }, upper := { exponent := 0, mantissa := (3245/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974194483/54973620224) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2630InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2630LocalValidity :
    LeafFacts leaf2630Box leaf2630Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2630Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486810112) }) = true
      norm_num [leaf2630Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2630CertificateValid :
    WideCertificateValid leaf2630Box leaf2630Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi184ValidityFacts
    leaf2630LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2630CoverageChecked :
    coverageCheck (innerAD leaf2630Box) leaf2630InnerLog = true := by
  rfl'

private theorem leaf2630InnerLogValid :
    leaf2630InnerLog.Valid 8 (innerAD leaf2630Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2630CoverageChecked

private noncomputable def leaf2630InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2630InputLogOnePlusV_eq :
    leaf2630InputLogOnePlusV = outerEnclosure 24
      (leaf2630Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2630RoundedFacts : LeafRoundedFacts 8
    leaf2630Certificate.logOnePlusV leaf2630InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2630InputLogOnePlusV_eq }

private noncomputable def leaf2630Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2630InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2630LowerChecked :
    lowerCheck 24 leaf2630Box leaf2630Inputs = true := by
  rfl'

private theorem leaf2630CoversExact : CoversExact 8
    leaf2630Box leaf2630Certificate leaf2630InnerLog leaf2630Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2630RoundedFacts (by rfl)

private theorem leaf2630FlatSound : Sound leaf2630Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2630CertificateValid
    leaf2630InnerLogValid leaf2630CoversExact leaf2630LowerChecked

private noncomputable def leaf2631Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2631Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433999872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1690233579/1073741824) }, upper := { exponent := 0, mantissa := (26059/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870921727/274867999744) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2631InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2631LocalValidity :
    LeafFacts leaf2631Box leaf2631Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2631Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433999872) }) = true
      norm_num [leaf2631Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2631CertificateValid :
    WideCertificateValid leaf2631Box leaf2631Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi185ValidityFacts
    leaf2631LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2631CoverageChecked :
    coverageCheck (innerAD leaf2631Box) leaf2631InnerLog = true := by
  rfl'

private theorem leaf2631InnerLogValid :
    leaf2631InnerLog.Valid 8 (innerAD leaf2631Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2631CoverageChecked

private noncomputable def leaf2631InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2631InputLogOnePlusV_eq :
    leaf2631InputLogOnePlusV = outerEnclosure 24
      (leaf2631Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2631RoundedFacts : LeafRoundedFacts 8
    leaf2631Certificate.logOnePlusV leaf2631InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2631InputLogOnePlusV_eq }

private noncomputable def leaf2631Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2631InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2631LowerChecked :
    lowerCheck 24 leaf2631Box leaf2631Inputs = true := by
  rfl'

private theorem leaf2631CoversExact : CoversExact 8
    leaf2631Box leaf2631Certificate leaf2631InnerLog leaf2631Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2631RoundedFacts (by rfl)

private theorem leaf2631FlatSound : Sound leaf2631Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2631CertificateValid
    leaf2631InnerLogValid leaf2631CoversExact leaf2631LowerChecked

private noncomputable def leaf2632Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2632Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090147328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1692985921/1073741824) }, upper := { exponent := 0, mantissa := (13051/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180403693/10180294656) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2632InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2632LocalValidity :
    LeafFacts leaf2632Box leaf2632Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2632Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090147328) }) = true
      norm_num [leaf2632Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2632CertificateValid :
    WideCertificateValid leaf2632Box leaf2632Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi185ValidityFacts
    leaf2632LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2632CoverageChecked :
    coverageCheck (innerAD leaf2632Box) leaf2632InnerLog = true := by
  rfl'

private theorem leaf2632InnerLogValid :
    leaf2632InnerLog.Valid 8 (innerAD leaf2632Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2632CoverageChecked

private noncomputable def leaf2632InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2632InputLogOnePlusV_eq :
    leaf2632InputLogOnePlusV = outerEnclosure 24
      (leaf2632Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2632RoundedFacts : LeafRoundedFacts 8
    leaf2632Certificate.logOnePlusV leaf2632InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2632InputLogOnePlusV_eq }

private noncomputable def leaf2632Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2632InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2632LowerChecked :
    lowerCheck 24 leaf2632Box leaf2632Inputs = true := by
  rfl'

private theorem leaf2632CoversExact : CoversExact 8
    leaf2632Box leaf2632Certificate leaf2632InnerLog leaf2632Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2632RoundedFacts (by rfl)

private theorem leaf2632FlatSound : Sound leaf2632Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2632CertificateValid
    leaf2632InnerLogValid leaf2632CoversExact leaf2632LowerChecked

private noncomputable def leaf2633Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2633Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433884672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1704912745/1073741824) }, upper := { exponent := 0, mantissa := (6571/4096) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870806527/274867769344) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2633InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2633LocalValidity :
    LeafFacts leaf2633Box leaf2633Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2633Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433884672) }) = true
      norm_num [leaf2633Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2633CertificateValid :
    WideCertificateValid leaf2633Box leaf2633Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi186ValidityFacts
    leaf2633LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2633CoverageChecked :
    coverageCheck (innerAD leaf2633Box) leaf2633InnerLog = true := by
  rfl'

private theorem leaf2633InnerLogValid :
    leaf2633InnerLog.Valid 8 (innerAD leaf2633Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2633CoverageChecked

private noncomputable def leaf2633InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2633InputLogOnePlusV_eq :
    leaf2633InputLogOnePlusV = outerEnclosure 24
      (leaf2633Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2633RoundedFacts : LeafRoundedFacts 8
    leaf2633Certificate.logOnePlusV leaf2633InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2633InputLogOnePlusV_eq }

private noncomputable def leaf2633Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2633InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2633LowerChecked :
    lowerCheck 24 leaf2633Box leaf2633Inputs = true := by
  rfl'

private theorem leaf2633CoversExact : CoversExact 8
    leaf2633Box leaf2633Certificate leaf2633InnerLog leaf2633Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2633RoundedFacts (by rfl)

private theorem leaf2633FlatSound : Sound leaf2633Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2633CertificateValid
    leaf2633InnerLogValid leaf2633CoversExact leaf2633LowerChecked

private noncomputable def leaf2634Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2634Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084344832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1707730619/1073741824) }, upper := { exponent := 0, mantissa := (3291/2048) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168869647/16168689664) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2634InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2634LocalValidity :
    LeafFacts leaf2634Box leaf2634Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2634Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084344832) }) = true
      norm_num [leaf2634Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2634CertificateValid :
    WideCertificateValid leaf2634Box leaf2634Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi186ValidityFacts
    leaf2634LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2634CoverageChecked :
    coverageCheck (innerAD leaf2634Box) leaf2634InnerLog = true := by
  rfl'

private theorem leaf2634InnerLogValid :
    leaf2634InnerLog.Valid 8 (innerAD leaf2634Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2634CoverageChecked

private noncomputable def leaf2634InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2634InputLogOnePlusV_eq :
    leaf2634InputLogOnePlusV = outerEnclosure 24
      (leaf2634Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2634RoundedFacts : LeafRoundedFacts 8
    leaf2634Certificate.logOnePlusV leaf2634InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2634InputLogOnePlusV_eq }

private noncomputable def leaf2634Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2634InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2634LowerChecked :
    lowerCheck 24 leaf2634Box leaf2634Inputs = true := by
  rfl'

private theorem leaf2634CoversExact : CoversExact 8
    leaf2634Box leaf2634Certificate leaf2634InnerLog leaf2634Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2634RoundedFacts (by rfl)

private theorem leaf2634FlatSound : Sound leaf2634Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2634CertificateValid
    leaf2634InnerLogValid leaf2634CoversExact leaf2634LowerChecked

private noncomputable def leaf2635Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2635Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486791168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1695738263/1073741824) }, upper := { exponent := 0, mantissa := (26145/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974175539/54973582336) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2635InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2635LocalValidity :
    LeafFacts leaf2635Box leaf2635Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2635Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486791168) }) = true
      norm_num [leaf2635Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2635CertificateValid :
    WideCertificateValid leaf2635Box leaf2635Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi185ValidityFacts
    leaf2635LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2635CoverageChecked :
    coverageCheck (innerAD leaf2635Box) leaf2635InnerLog = true := by
  rfl'

private theorem leaf2635InnerLogValid :
    leaf2635InnerLog.Valid 8 (innerAD leaf2635Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2635CoverageChecked

private noncomputable def leaf2635InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2635InputLogOnePlusV_eq :
    leaf2635InputLogOnePlusV = outerEnclosure 24
      (leaf2635Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2635RoundedFacts : LeafRoundedFacts 8
    leaf2635Certificate.logOnePlusV leaf2635InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2635InputLogOnePlusV_eq }

private noncomputable def leaf2635Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2635InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2635LowerChecked :
    lowerCheck 24 leaf2635Box leaf2635Inputs = true := by
  rfl'

private theorem leaf2635CoversExact : CoversExact 8
    leaf2635Box leaf2635Certificate leaf2635InnerLog leaf2635Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2635RoundedFacts (by rfl)

private theorem leaf2635FlatSound : Sound leaf2635Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2635CertificateValid
    leaf2635InnerLogValid leaf2635CoversExact leaf2635LowerChecked

private noncomputable def leaf2636Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2636Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433933824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1698490605/1073741824) }, upper := { exponent := 0, mantissa := (6547/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870855679/274867867648) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2636InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2636LocalValidity :
    LeafFacts leaf2636Box leaf2636Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2636Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433933824) }) = true
      norm_num [leaf2636Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2636CertificateValid :
    WideCertificateValid leaf2636Box leaf2636Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi185ValidityFacts
    leaf2636LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2636CoverageChecked :
    coverageCheck (innerAD leaf2636Box) leaf2636InnerLog = true := by
  rfl'

private theorem leaf2636InnerLogValid :
    leaf2636InnerLog.Valid 8 (innerAD leaf2636Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2636CoverageChecked

private noncomputable def leaf2636InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2636InputLogOnePlusV_eq :
    leaf2636InputLogOnePlusV = outerEnclosure 24
      (leaf2636Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2636RoundedFacts : LeafRoundedFacts 8
    leaf2636Certificate.logOnePlusV leaf2636InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2636InputLogOnePlusV_eq }

private noncomputable def leaf2636Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2636InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2636LowerChecked :
    lowerCheck 24 leaf2636Box leaf2636Inputs = true := by
  rfl'

private theorem leaf2636CoversExact : CoversExact 8
    leaf2636Box leaf2636Certificate leaf2636InnerLog leaf2636Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2636RoundedFacts (by rfl)

private theorem leaf2636FlatSound : Sound leaf2636Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2636CertificateValid
    leaf2636InnerLogValid leaf2636CoversExact leaf2636LowerChecked

private noncomputable def leaf2637Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2637Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090142208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1710548493/1073741824) }, upper := { exponent := 0, mantissa := (6593/4096) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180398573/10180284416) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2637InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2637LocalValidity :
    LeafFacts leaf2637Box leaf2637Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2637Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090142208) }) = true
      norm_num [leaf2637Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2637CertificateValid :
    WideCertificateValid leaf2637Box leaf2637Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi186ValidityFacts
    leaf2637LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2637CoverageChecked :
    coverageCheck (innerAD leaf2637Box) leaf2637InnerLog = true := by
  rfl'

private theorem leaf2637InnerLogValid :
    leaf2637InnerLog.Valid 8 (innerAD leaf2637Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2637CoverageChecked

private noncomputable def leaf2637InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2637InputLogOnePlusV_eq :
    leaf2637InputLogOnePlusV = outerEnclosure 24
      (leaf2637Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2637RoundedFacts : LeafRoundedFacts 8
    leaf2637Certificate.logOnePlusV leaf2637InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2637InputLogOnePlusV_eq }

private noncomputable def leaf2637Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2637InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2637LowerChecked :
    lowerCheck 24 leaf2637Box leaf2637Inputs = true := by
  rfl'

private theorem leaf2637CoversExact : CoversExact 8
    leaf2637Box leaf2637Certificate leaf2637InnerLog leaf2637Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2637RoundedFacts (by rfl)

private theorem leaf2637FlatSound : Sound leaf2637Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2637CertificateValid
    leaf2637InnerLogValid leaf2637CoversExact leaf2637LowerChecked

private noncomputable def leaf2638Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2638Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433817088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1713366367/1073741824) }, upper := { exponent := 0, mantissa := (1651/1024) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870738943/274867634176) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2638InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2638LocalValidity :
    LeafFacts leaf2638Box leaf2638Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2638Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433817088) }) = true
      norm_num [leaf2638Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2638CertificateValid :
    WideCertificateValid leaf2638Box leaf2638Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi186ValidityFacts
    leaf2638LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2638CoverageChecked :
    coverageCheck (innerAD leaf2638Box) leaf2638InnerLog = true := by
  rfl'

private theorem leaf2638InnerLogValid :
    leaf2638InnerLog.Valid 8 (innerAD leaf2638Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2638CoverageChecked

private noncomputable def leaf2638InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2638InputLogOnePlusV_eq :
    leaf2638InputLogOnePlusV = outerEnclosure 24
      (leaf2638Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2638RoundedFacts : LeafRoundedFacts 8
    leaf2638Certificate.logOnePlusV leaf2638InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2638InputLogOnePlusV_eq }

private noncomputable def leaf2638Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2638InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2638LowerChecked :
    lowerCheck 24 leaf2638Box leaf2638Inputs = true := by
  rfl'

private theorem leaf2638CoversExact : CoversExact 8
    leaf2638Box leaf2638Certificate leaf2638InnerLog leaf2638Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2638RoundedFacts (by rfl)

private theorem leaf2638FlatSound : Sound leaf2638Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2638CertificateValid
    leaf2638InnerLogValid leaf2638CoversExact leaf2638LowerChecked

private noncomputable def leaf2639Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2639Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434146304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1671360359/1073741824) }, upper := { exponent := 0, mantissa := (25773/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871068159/274868292608) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2639InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2639LocalValidity :
    LeafFacts leaf2639Box leaf2639Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2639Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434146304) }) = true
      norm_num [leaf2639Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2639CertificateValid :
    WideCertificateValid leaf2639Box leaf2639Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi183ValidityFacts
    leaf2639LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2639CoverageChecked :
    coverageCheck (innerAD leaf2639Box) leaf2639InnerLog = true := by
  rfl'

private theorem leaf2639InnerLogValid :
    leaf2639InnerLog.Valid 8 (innerAD leaf2639Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2639CoverageChecked

private noncomputable def leaf2639InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2639InputLogOnePlusV_eq :
    leaf2639InputLogOnePlusV = outerEnclosure 24
      (leaf2639Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2639RoundedFacts : LeafRoundedFacts 8
    leaf2639Certificate.logOnePlusV leaf2639InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2639InputLogOnePlusV_eq }

private noncomputable def leaf2639Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi183InputQChi innerPair41Input
    leaf2639InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2639LowerChecked :
    lowerCheck 24 leaf2639Box leaf2639Inputs = true := by
  rfl'

private theorem leaf2639CoversExact : CoversExact 8
    leaf2639Box leaf2639Certificate leaf2639InnerLog leaf2639Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi183RoundedFacts
    innerPair41RoundedFacts leaf2639RoundedFacts (by rfl)

private theorem leaf2639FlatSound : Sound leaf2639Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2639CertificateValid
    leaf2639InnerLogValid leaf2639CoversExact leaf2639LowerChecked

private noncomputable def leaf2640Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2640Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270458368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1673981637/1073741824) }, upper := { exponent := 0, mantissa := (12907/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541227463/30540916736) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2640InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2640LocalValidity :
    LeafFacts leaf2640Box leaf2640Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2640Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270458368) }) = true
      norm_num [leaf2640Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2640CertificateValid :
    WideCertificateValid leaf2640Box leaf2640Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi183ValidityFacts
    leaf2640LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2640CoverageChecked :
    coverageCheck (innerAD leaf2640Box) leaf2640InnerLog = true := by
  rfl'

private theorem leaf2640InnerLogValid :
    leaf2640InnerLog.Valid 8 (innerAD leaf2640Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2640CoverageChecked

private noncomputable def leaf2640InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2640InputLogOnePlusV_eq :
    leaf2640InputLogOnePlusV = outerEnclosure 24
      (leaf2640Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2640RoundedFacts : LeafRoundedFacts 8
    leaf2640Certificate.logOnePlusV leaf2640InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2640InputLogOnePlusV_eq }

private noncomputable def leaf2640Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi183InputQChi innerPair41Input
    leaf2640InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2640LowerChecked :
    lowerCheck 24 leaf2640Box leaf2640Inputs = true := by
  rfl'

private theorem leaf2640CoversExact : CoversExact 8
    leaf2640Box leaf2640Certificate leaf2640InnerLog leaf2640Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi183RoundedFacts
    innerPair41RoundedFacts leaf2640RoundedFacts (by rfl)

private theorem leaf2640FlatSound : Sound leaf2640Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2640CertificateValid
    leaf2640InnerLogValid leaf2640CoversExact leaf2640LowerChecked

private noncomputable def leaf2641Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2641Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434029056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1686301653/1073741824) }, upper := { exponent := 0, mantissa := (13001/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870950911/274868058112) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2641InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2641LocalValidity :
    LeafFacts leaf2641Box leaf2641Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2641Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434029056) }) = true
      norm_num [leaf2641Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2641CertificateValid :
    WideCertificateValid leaf2641Box leaf2641Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi184ValidityFacts
    leaf2641LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2641CoverageChecked :
    coverageCheck (innerAD leaf2641Box) leaf2641InnerLog = true := by
  rfl'

private theorem leaf2641InnerLogValid :
    leaf2641InnerLog.Valid 8 (innerAD leaf2641Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2641CoverageChecked

private noncomputable def leaf2641InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2641InputLogOnePlusV_eq :
    leaf2641InputLogOnePlusV = outerEnclosure 24
      (leaf2641Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2641RoundedFacts : LeafRoundedFacts 8
    leaf2641Certificate.logOnePlusV leaf2641InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2641InputLogOnePlusV_eq }

private noncomputable def leaf2641Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2641InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2641LowerChecked :
    lowerCheck 24 leaf2641Box leaf2641Inputs = true := by
  rfl'

private theorem leaf2641CoversExact : CoversExact 8
    leaf2641Box leaf2641Certificate leaf2641InnerLog leaf2641Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2641RoundedFacts (by rfl)

private theorem leaf2641FlatSound : Sound leaf2641Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2641CertificateValid
    leaf2641InnerLogValid leaf2641CoversExact leaf2641LowerChecked

private noncomputable def leaf2642Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2642Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434007552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1688988463/1073741824) }, upper := { exponent := 0, mantissa := (6511/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870929407/274868015104) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2642InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2642LocalValidity :
    LeafFacts leaf2642Box leaf2642Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2642Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434007552) }) = true
      norm_num [leaf2642Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2642CertificateValid :
    WideCertificateValid leaf2642Box leaf2642Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi184ValidityFacts
    leaf2642LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2642CoverageChecked :
    coverageCheck (innerAD leaf2642Box) leaf2642InnerLog = true := by
  rfl'

private theorem leaf2642InnerLogValid :
    leaf2642InnerLog.Valid 8 (innerAD leaf2642Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2642CoverageChecked

private noncomputable def leaf2642InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2642InputLogOnePlusV_eq :
    leaf2642InputLogOnePlusV = outerEnclosure 24
      (leaf2642Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2642RoundedFacts : LeafRoundedFacts 8
    leaf2642Certificate.logOnePlusV leaf2642InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2642InputLogOnePlusV_eq }

private noncomputable def leaf2642Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2642InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2642LowerChecked :
    lowerCheck 24 leaf2642Box leaf2642Inputs = true := by
  rfl'

private theorem leaf2642CoversExact : CoversExact 8
    leaf2642Box leaf2642Certificate leaf2642InnerLog leaf2642Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2642RoundedFacts (by rfl)

private theorem leaf2642FlatSound : Sound leaf2642Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2642CertificateValid
    leaf2642InnerLogValid leaf2642CoversExact leaf2642LowerChecked

private noncomputable def leaf2643Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2643Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486820864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1676602915/1073741824) }, upper := { exponent := 0, mantissa := (25855/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974205235/54973641728) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2643InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf2643LocalValidity :
    LeafFacts leaf2643Box leaf2643Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2643Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486820864) }) = true
      norm_num [leaf2643Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2643CertificateValid :
    WideCertificateValid leaf2643Box leaf2643Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi183ValidityFacts
    leaf2643LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2643CoverageChecked :
    coverageCheck (innerAD leaf2643Box) leaf2643InnerLog = true := by
  rfl'

private theorem leaf2643InnerLogValid :
    leaf2643InnerLog.Valid 8 (innerAD leaf2643Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf2643CoverageChecked

private noncomputable def leaf2643InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2643InputLogOnePlusV_eq :
    leaf2643InputLogOnePlusV = outerEnclosure 24
      (leaf2643Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2643RoundedFacts : LeafRoundedFacts 8
    leaf2643Certificate.logOnePlusV leaf2643InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2643InputLogOnePlusV_eq }

private noncomputable def leaf2643Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi183InputQChi innerPair41Input
    leaf2643InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2643LowerChecked :
    lowerCheck 24 leaf2643Box leaf2643Inputs = true := by
  rfl'

private theorem leaf2643CoversExact : CoversExact 8
    leaf2643Box leaf2643Certificate leaf2643InnerLog leaf2643Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi183RoundedFacts
    innerPair41RoundedFacts leaf2643RoundedFacts (by rfl)

private theorem leaf2643FlatSound : Sound leaf2643Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2643CertificateValid
    leaf2643InnerLogValid leaf2643CoversExact leaf2643LowerChecked

private noncomputable def leaf2644Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2644Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434083328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1679224193/1073741824) }, upper := { exponent := 0, mantissa := (3237/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871005183/274868166656) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2644InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2644LocalValidity :
    LeafFacts leaf2644Box leaf2644Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2644Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434083328) }) = true
      norm_num [leaf2644Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2644CertificateValid :
    WideCertificateValid leaf2644Box leaf2644Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi183ValidityFacts
    leaf2644LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2644CoverageChecked :
    coverageCheck (innerAD leaf2644Box) leaf2644InnerLog = true := by
  rfl'

private theorem leaf2644InnerLogValid :
    leaf2644InnerLog.Valid 8 (innerAD leaf2644Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2644CoverageChecked

private noncomputable def leaf2644InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2644InputLogOnePlusV_eq :
    leaf2644InputLogOnePlusV = outerEnclosure 24
      (leaf2644Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2644RoundedFacts : LeafRoundedFacts 8
    leaf2644Certificate.logOnePlusV leaf2644InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2644InputLogOnePlusV_eq }

private noncomputable def leaf2644Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi183InputQChi innerPair50Input
    leaf2644InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2644LowerChecked :
    lowerCheck 24 leaf2644Box leaf2644Inputs = true := by
  rfl'

private theorem leaf2644CoversExact : CoversExact 8
    leaf2644Box leaf2644Certificate leaf2644InnerLog leaf2644Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi183RoundedFacts
    innerPair50RoundedFacts leaf2644RoundedFacts (by rfl)

private theorem leaf2644FlatSound : Sound leaf2644Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2644CertificateValid
    leaf2644InnerLogValid leaf2644CoversExact leaf2644LowerChecked

private noncomputable def leaf2645Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2645Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433986048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1691675273/1073741824) }, upper := { exponent := 0, mantissa := (13043/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870907903/274867972096) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2645InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2645LocalValidity :
    LeafFacts leaf2645Box leaf2645Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2645Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433986048) }) = true
      norm_num [leaf2645Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2645CertificateValid :
    WideCertificateValid leaf2645Box leaf2645Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi184ValidityFacts
    leaf2645LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2645CoverageChecked :
    coverageCheck (innerAD leaf2645Box) leaf2645InnerLog = true := by
  rfl'

private theorem leaf2645InnerLogValid :
    leaf2645InnerLog.Valid 8 (innerAD leaf2645Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2645CoverageChecked

private noncomputable def leaf2645InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2645InputLogOnePlusV_eq :
    leaf2645InputLogOnePlusV = outerEnclosure 24
      (leaf2645Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2645RoundedFacts : LeafRoundedFacts 8
    leaf2645Certificate.logOnePlusV leaf2645InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2645InputLogOnePlusV_eq }

private noncomputable def leaf2645Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2645InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2645LowerChecked :
    lowerCheck 24 leaf2645Box leaf2645Inputs = true := by
  rfl'

private theorem leaf2645CoversExact : CoversExact 8
    leaf2645Box leaf2645Certificate leaf2645InnerLog leaf2645Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2645RoundedFacts (by rfl)

private theorem leaf2645FlatSound : Sound leaf2645Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2645CertificateValid
    leaf2645InnerLogValid leaf2645CoversExact leaf2645LowerChecked

private noncomputable def leaf2646Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2646Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433964544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1694362083/1073741824) }, upper := { exponent := 0, mantissa := (1633/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870886399/274867929088) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2646InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2646LocalValidity :
    LeafFacts leaf2646Box leaf2646Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2646Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433964544) }) = true
      norm_num [leaf2646Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2646CertificateValid :
    WideCertificateValid leaf2646Box leaf2646Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi184ValidityFacts
    leaf2646LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2646CoverageChecked :
    coverageCheck (innerAD leaf2646Box) leaf2646InnerLog = true := by
  rfl'

private theorem leaf2646InnerLogValid :
    leaf2646InnerLog.Valid 8 (innerAD leaf2646Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2646CoverageChecked

private noncomputable def leaf2646InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2646InputLogOnePlusV_eq :
    leaf2646InputLogOnePlusV = outerEnclosure 24
      (leaf2646Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2646RoundedFacts : LeafRoundedFacts 8
    leaf2646Certificate.logOnePlusV leaf2646InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2646InputLogOnePlusV_eq }

private noncomputable def leaf2646Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi184InputQChi innerPair50Input
    leaf2646InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2646LowerChecked :
    lowerCheck 24 leaf2646Box leaf2646Inputs = true := by
  rfl'

private theorem leaf2646CoversExact : CoversExact 8
    leaf2646Box leaf2646Certificate leaf2646InnerLog leaf2646Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi184RoundedFacts
    innerPair50RoundedFacts leaf2646RoundedFacts (by rfl)

private theorem leaf2646FlatSound : Sound leaf2646Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2646CertificateValid
    leaf2646InnerLogValid leaf2646CoversExact leaf2646LowerChecked

private noncomputable def leaf2647Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2647Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811303936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1701242947/1073741824) }, upper := { exponent := 0, mantissa := (26231/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623611221/91622607872) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2647InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2647LocalValidity :
    LeafFacts leaf2647Box leaf2647Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2647Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811303936) }) = true
      norm_num [leaf2647Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2647CertificateValid :
    WideCertificateValid leaf2647Box leaf2647Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi185ValidityFacts
    leaf2647LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2647CoverageChecked :
    coverageCheck (innerAD leaf2647Box) leaf2647InnerLog = true := by
  rfl'

private theorem leaf2647InnerLogValid :
    leaf2647InnerLog.Valid 8 (innerAD leaf2647Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2647CoverageChecked

private noncomputable def leaf2647InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2647InputLogOnePlusV_eq :
    leaf2647InputLogOnePlusV = outerEnclosure 24
      (leaf2647Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2647RoundedFacts : LeafRoundedFacts 8
    leaf2647Certificate.logOnePlusV leaf2647InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2647InputLogOnePlusV_eq }

private noncomputable def leaf2647Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2647InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2647LowerChecked :
    lowerCheck 24 leaf2647Box leaf2647Inputs = true := by
  rfl'

private theorem leaf2647CoversExact : CoversExact 8
    leaf2647Box leaf2647Certificate leaf2647InnerLog leaf2647Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2647RoundedFacts (by rfl)

private theorem leaf2647FlatSound : Sound leaf2647Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2647CertificateValid
    leaf2647InnerLogValid leaf2647CoversExact leaf2647LowerChecked

private noncomputable def leaf2648Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2648Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433889792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1703995289/1073741824) }, upper := { exponent := 0, mantissa := (13137/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870811647/274867779584) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2648InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2648LocalValidity :
    LeafFacts leaf2648Box leaf2648Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2648Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433889792) }) = true
      norm_num [leaf2648Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2648CertificateValid :
    WideCertificateValid leaf2648Box leaf2648Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi185ValidityFacts
    leaf2648LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2648CoverageChecked :
    coverageCheck (innerAD leaf2648Box) leaf2648InnerLog = true := by
  rfl'

private theorem leaf2648InnerLogValid :
    leaf2648InnerLog.Valid 8 (innerAD leaf2648Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2648CoverageChecked

private noncomputable def leaf2648InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2648InputLogOnePlusV_eq :
    leaf2648InputLogOnePlusV = outerEnclosure 24
      (leaf2648Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2648RoundedFacts : LeafRoundedFacts 8
    leaf2648Certificate.logOnePlusV leaf2648InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2648InputLogOnePlusV_eq }

private noncomputable def leaf2648Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2648InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2648LowerChecked :
    lowerCheck 24 leaf2648Box leaf2648Inputs = true := by
  rfl'

private theorem leaf2648CoversExact : CoversExact 8
    leaf2648Box leaf2648Certificate leaf2648InnerLog leaf2648Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2648RoundedFacts (by rfl)

private theorem leaf2648FlatSound : Sound leaf2648Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2648CertificateValid
    leaf2648InnerLogValid leaf2648CoversExact leaf2648LowerChecked

private noncomputable def leaf2649Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2649Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486758912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1716184241/1073741824) }, upper := { exponent := 0, mantissa := (6615/4096) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974143283/54973517824) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2649InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2649LocalValidity :
    LeafFacts leaf2649Box leaf2649Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2649Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486758912) }) = true
      norm_num [leaf2649Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2649CertificateValid :
    WideCertificateValid leaf2649Box leaf2649Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi186ValidityFacts
    leaf2649LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2649CoverageChecked :
    coverageCheck (innerAD leaf2649Box) leaf2649InnerLog = true := by
  rfl'

private theorem leaf2649InnerLogValid :
    leaf2649InnerLog.Valid 8 (innerAD leaf2649Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2649CoverageChecked

private noncomputable def leaf2649InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2649InputLogOnePlusV_eq :
    leaf2649InputLogOnePlusV = outerEnclosure 24
      (leaf2649Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2649RoundedFacts : LeafRoundedFacts 8
    leaf2649Certificate.logOnePlusV leaf2649InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2649InputLogOnePlusV_eq }

private noncomputable def leaf2649Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2649InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2649LowerChecked :
    lowerCheck 24 leaf2649Box leaf2649Inputs = true := by
  rfl'

private theorem leaf2649CoversExact : CoversExact 8
    leaf2649Box leaf2649Certificate leaf2649InnerLog leaf2649Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2649RoundedFacts (by rfl)

private theorem leaf2649FlatSound : Sound leaf2649Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2649CertificateValid
    leaf2649InnerLogValid leaf2649CoversExact leaf2649LowerChecked

private noncomputable def leaf2650Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2650Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811257344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1719002115/1073741824) }, upper := { exponent := 0, mantissa := (3313/2048) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623564629/91622514688) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2650InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2650LocalValidity :
    LeafFacts leaf2650Box leaf2650Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2650Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811257344) }) = true
      norm_num [leaf2650Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2650CertificateValid :
    WideCertificateValid leaf2650Box leaf2650Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi186ValidityFacts
    leaf2650LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2650CoverageChecked :
    coverageCheck (innerAD leaf2650Box) leaf2650InnerLog = true := by
  rfl'

private theorem leaf2650InnerLogValid :
    leaf2650InnerLog.Valid 8 (innerAD leaf2650Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2650CoverageChecked

private noncomputable def leaf2650InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2650InputLogOnePlusV_eq :
    leaf2650InputLogOnePlusV = outerEnclosure 24
      (leaf2650Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2650RoundedFacts : LeafRoundedFacts 8
    leaf2650Certificate.logOnePlusV leaf2650InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2650InputLogOnePlusV_eq }

private noncomputable def leaf2650Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2650InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2650LowerChecked :
    lowerCheck 24 leaf2650Box leaf2650Inputs = true := by
  rfl'

private theorem leaf2650CoversExact : CoversExact 8
    leaf2650Box leaf2650Certificate leaf2650InnerLog leaf2650Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2650RoundedFacts (by rfl)

private theorem leaf2650FlatSound : Sound leaf2650Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2650CertificateValid
    leaf2650InnerLogValid leaf2650CoversExact leaf2650LowerChecked

private noncomputable def leaf2651Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2651Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433867776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1706747631/1073741824) }, upper := { exponent := 0, mantissa := (26317/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870789631/274867735552) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2651InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2651LocalValidity :
    LeafFacts leaf2651Box leaf2651Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2651Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433867776) }) = true
      norm_num [leaf2651Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2651CertificateValid :
    WideCertificateValid leaf2651Box leaf2651Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi185ValidityFacts
    leaf2651LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2651CoverageChecked :
    coverageCheck (innerAD leaf2651Box) leaf2651InnerLog = true := by
  rfl'

private theorem leaf2651InnerLogValid :
    leaf2651InnerLog.Valid 8 (innerAD leaf2651Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2651CoverageChecked

private noncomputable def leaf2651InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2651InputLogOnePlusV_eq :
    leaf2651InputLogOnePlusV = outerEnclosure 24
      (leaf2651Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2651RoundedFacts : LeafRoundedFacts 8
    leaf2651Certificate.logOnePlusV leaf2651InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2651InputLogOnePlusV_eq }

private noncomputable def leaf2651Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2651InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2651LowerChecked :
    lowerCheck 24 leaf2651Box leaf2651Inputs = true := by
  rfl'

private theorem leaf2651CoversExact : CoversExact 8
    leaf2651Box leaf2651Certificate leaf2651InnerLog leaf2651Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2651RoundedFacts (by rfl)

private theorem leaf2651FlatSound : Sound leaf2651Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2651CertificateValid
    leaf2651InnerLogValid leaf2651CoversExact leaf2651LowerChecked

private noncomputable def leaf2652Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2652Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162256384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1709499973/1073741824) }, upper := { exponent := 0, mantissa := (3295/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324717841/18324512768) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2652InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2652LocalValidity :
    LeafFacts leaf2652Box leaf2652Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2652Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162256384) }) = true
      norm_num [leaf2652Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2652CertificateValid :
    WideCertificateValid leaf2652Box leaf2652Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi185ValidityFacts
    leaf2652LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2652CoverageChecked :
    coverageCheck (innerAD leaf2652Box) leaf2652InnerLog = true := by
  rfl'

private theorem leaf2652InnerLogValid :
    leaf2652InnerLog.Valid 8 (innerAD leaf2652Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2652CoverageChecked

private noncomputable def leaf2652InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2652InputLogOnePlusV_eq :
    leaf2652InputLogOnePlusV = outerEnclosure 24
      (leaf2652Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2652RoundedFacts : LeafRoundedFacts 8
    leaf2652Certificate.logOnePlusV leaf2652InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2652InputLogOnePlusV_eq }

private noncomputable def leaf2652Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi185InputQChi innerPair50Input
    leaf2652InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2652LowerChecked :
    lowerCheck 24 leaf2652Box leaf2652Inputs = true := by
  rfl'

private theorem leaf2652CoversExact : CoversExact 8
    leaf2652Box leaf2652Certificate leaf2652InnerLog leaf2652Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi185RoundedFacts
    innerPair50RoundedFacts leaf2652RoundedFacts (by rfl)

private theorem leaf2652FlatSound : Sound leaf2652Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2652CertificateValid
    leaf2652InnerLogValid leaf2652CoversExact leaf2652LowerChecked

private noncomputable def leaf2653Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2653Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433749504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1721819989/1073741824) }, upper := { exponent := 0, mantissa := (6637/4096) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870671359/274867499008) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2653InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2653LocalValidity :
    LeafFacts leaf2653Box leaf2653Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2653Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433749504) }) = true
      norm_num [leaf2653Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2653CertificateValid :
    WideCertificateValid leaf2653Box leaf2653Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi186ValidityFacts
    leaf2653LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2653CoverageChecked :
    coverageCheck (innerAD leaf2653Box) leaf2653InnerLog = true := by
  rfl'

private theorem leaf2653InnerLogValid :
    leaf2653InnerLog.Valid 8 (innerAD leaf2653Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2653CoverageChecked

private noncomputable def leaf2653InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2653InputLogOnePlusV_eq :
    leaf2653InputLogOnePlusV = outerEnclosure 24
      (leaf2653Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2653RoundedFacts : LeafRoundedFacts 8
    leaf2653Certificate.logOnePlusV leaf2653InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2653InputLogOnePlusV_eq }

private noncomputable def leaf2653Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2653InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2653LowerChecked :
    lowerCheck 24 leaf2653Box leaf2653Inputs = true := by
  rfl'

private theorem leaf2653CoversExact : CoversExact 8
    leaf2653Box leaf2653Certificate leaf2653InnerLog leaf2653Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2653RoundedFacts (by rfl)

private theorem leaf2653FlatSound : Sound leaf2653Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2653CertificateValid
    leaf2653InnerLogValid leaf2653CoversExact leaf2653LowerChecked

private noncomputable def leaf2654Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2654Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433726976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1724637863/1073741824) }, upper := { exponent := 0, mantissa := (831/512) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870648831/274867453952) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2654InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2654LocalValidity :
    LeafFacts leaf2654Box leaf2654Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2654Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433726976) }) = true
      norm_num [leaf2654Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2654CertificateValid :
    WideCertificateValid leaf2654Box leaf2654Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi186ValidityFacts
    leaf2654LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2654CoverageChecked :
    coverageCheck (innerAD leaf2654Box) leaf2654InnerLog = true := by
  rfl'

private theorem leaf2654InnerLogValid :
    leaf2654InnerLog.Valid 8 (innerAD leaf2654Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2654CoverageChecked

private noncomputable def leaf2654InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2654InputLogOnePlusV_eq :
    leaf2654InputLogOnePlusV = outerEnclosure 24
      (leaf2654Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2654RoundedFacts : LeafRoundedFacts 8
    leaf2654Certificate.logOnePlusV leaf2654InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2654InputLogOnePlusV_eq }

private noncomputable def leaf2654Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi186InputQChi innerPair50Input
    leaf2654InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2654LowerChecked :
    lowerCheck 24 leaf2654Box leaf2654Inputs = true := by
  rfl'

private theorem leaf2654CoversExact : CoversExact 8
    leaf2654Box leaf2654Certificate leaf2654InnerLog leaf2654Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi186RoundedFacts
    innerPair50RoundedFacts leaf2654RoundedFacts (by rfl)

private theorem leaf2654FlatSound : Sound leaf2654Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2654CertificateValid
    leaf2654InnerLogValid leaf2654CoversExact leaf2654LowerChecked

private noncomputable def leaf2655Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2655Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433769472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1719591911/1073741824) }, upper := { exponent := 0, mantissa := (26509/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870691327/274867538944) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2655InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2655LocalValidity :
    LeafFacts leaf2655Box leaf2655Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2655Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433769472) }) = true
      norm_num [leaf2655Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2655CertificateValid :
    WideCertificateValid leaf2655Box leaf2655Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi133ValidityFacts
    leaf2655LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2655CoverageChecked :
    coverageCheck (innerAD leaf2655Box) leaf2655InnerLog = true := by
  rfl'

private theorem leaf2655InnerLogValid :
    leaf2655InnerLog.Valid 8 (innerAD leaf2655Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2655CoverageChecked

private noncomputable def leaf2655InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2655InputLogOnePlusV_eq :
    leaf2655InputLogOnePlusV = outerEnclosure 24
      (leaf2655Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2655RoundedFacts : LeafRoundedFacts 8
    leaf2655Certificate.logOnePlusV leaf2655InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2655InputLogOnePlusV_eq }

private noncomputable def leaf2655Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2655InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2655LowerChecked :
    lowerCheck 24 leaf2655Box leaf2655Inputs = true := by
  rfl'

private theorem leaf2655CoversExact : CoversExact 8
    leaf2655Box leaf2655Certificate leaf2655InnerLog leaf2655Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2655RoundedFacts (by rfl)

private theorem leaf2655FlatSound : Sound leaf2655Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2655CertificateValid
    leaf2655InnerLogValid leaf2655CoversExact leaf2655LowerChecked

private noncomputable def leaf2656Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2656Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433746432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1722475317/1073741824) }, upper := { exponent := 0, mantissa := (13277/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870668287/274867492864) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2656InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2656LocalValidity :
    LeafFacts leaf2656Box leaf2656Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2656Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433746432) }) = true
      norm_num [leaf2656Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2656CertificateValid :
    WideCertificateValid leaf2656Box leaf2656Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi133ValidityFacts
    leaf2656LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2656CoverageChecked :
    coverageCheck (innerAD leaf2656Box) leaf2656InnerLog = true := by
  rfl'

private theorem leaf2656InnerLogValid :
    leaf2656InnerLog.Valid 8 (innerAD leaf2656Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2656CoverageChecked

private noncomputable def leaf2656InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2656InputLogOnePlusV_eq :
    leaf2656InputLogOnePlusV = outerEnclosure 24
      (leaf2656Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2656RoundedFacts : LeafRoundedFacts 8
    leaf2656Certificate.logOnePlusV leaf2656InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2656InputLogOnePlusV_eq }

private noncomputable def leaf2656Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2656InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2656LowerChecked :
    lowerCheck 24 leaf2656Box leaf2656Inputs = true := by
  rfl'

private theorem leaf2656CoversExact : CoversExact 8
    leaf2656Box leaf2656Certificate leaf2656InnerLog leaf2656Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2656RoundedFacts (by rfl)

private theorem leaf2656FlatSound : Sound leaf2656Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2656CertificateValid
    leaf2656InnerLogValid leaf2656CoversExact leaf2656LowerChecked

private noncomputable def leaf2657Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2657Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433654272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1734271077/1073741824) }, upper := { exponent := 0, mantissa := (13367/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870576127/274867308544) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2657InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2657LocalValidity :
    LeafFacts leaf2657Box leaf2657Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2657Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433654272) }) = true
      norm_num [leaf2657Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2657CertificateValid :
    WideCertificateValid leaf2657Box leaf2657Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi134ValidityFacts
    leaf2657LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2657CoverageChecked :
    coverageCheck (innerAD leaf2657Box) leaf2657InnerLog = true := by
  rfl'

private theorem leaf2657InnerLogValid :
    leaf2657InnerLog.Valid 8 (innerAD leaf2657Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2657CoverageChecked

private noncomputable def leaf2657InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2657InputLogOnePlusV_eq :
    leaf2657InputLogOnePlusV = outerEnclosure 24
      (leaf2657Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2657RoundedFacts : LeafRoundedFacts 8
    leaf2657Certificate.logOnePlusV leaf2657InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2657InputLogOnePlusV_eq }

private noncomputable def leaf2657Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi134InputQChi innerPair51Input
    leaf2657InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2657LowerChecked :
    lowerCheck 24 leaf2657Box leaf2657Inputs = true := by
  rfl'

private theorem leaf2657CoversExact : CoversExact 8
    leaf2657Box leaf2657Certificate leaf2657InnerLog leaf2657Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi134RoundedFacts
    innerPair51RoundedFacts leaf2657RoundedFacts (by rfl)

private theorem leaf2657FlatSound : Sound leaf2657Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2657CertificateValid
    leaf2657InnerLogValid leaf2657CoversExact leaf2657LowerChecked

private noncomputable def leaf2658Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2658Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162242048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1737220015/1073741824) }, upper := { exponent := 0, mantissa := (6695/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324703505/18324484096) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2658InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2658LocalValidity :
    LeafFacts leaf2658Box leaf2658Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2658Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162242048) }) = true
      norm_num [leaf2658Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2658CertificateValid :
    WideCertificateValid leaf2658Box leaf2658Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi134ValidityFacts
    leaf2658LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2658CoverageChecked :
    coverageCheck (innerAD leaf2658Box) leaf2658InnerLog = true := by
  rfl'

private theorem leaf2658InnerLogValid :
    leaf2658InnerLog.Valid 8 (innerAD leaf2658Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2658CoverageChecked

private noncomputable def leaf2658InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2658InputLogOnePlusV_eq :
    leaf2658InputLogOnePlusV = outerEnclosure 24
      (leaf2658Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2658RoundedFacts : LeafRoundedFacts 8
    leaf2658Certificate.logOnePlusV leaf2658InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2658InputLogOnePlusV_eq }

private noncomputable def leaf2658Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi134InputQChi innerPair51Input
    leaf2658InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2658LowerChecked :
    lowerCheck 24 leaf2658Box leaf2658Inputs = true := by
  rfl'

private theorem leaf2658CoversExact : CoversExact 8
    leaf2658Box leaf2658Certificate leaf2658InnerLog leaf2658Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi134RoundedFacts
    innerPair51RoundedFacts leaf2658RoundedFacts (by rfl)

private theorem leaf2658FlatSound : Sound leaf2658Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2658CertificateValid
    leaf2658InnerLogValid leaf2658CoversExact leaf2658LowerChecked

private noncomputable def leaf2659Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2659Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433723392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1725358723/1073741824) }, upper := { exponent := 0, mantissa := (26599/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870645247/274867446784) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2659InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2659LocalValidity :
    LeafFacts leaf2659Box leaf2659Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2659Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433723392) }) = true
      norm_num [leaf2659Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2659CertificateValid :
    WideCertificateValid leaf2659Box leaf2659Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi133ValidityFacts
    leaf2659LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2659CoverageChecked :
    coverageCheck (innerAD leaf2659Box) leaf2659InnerLog = true := by
  rfl'

private theorem leaf2659InnerLogValid :
    leaf2659InnerLog.Valid 8 (innerAD leaf2659Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2659CoverageChecked

private noncomputable def leaf2659InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2659InputLogOnePlusV_eq :
    leaf2659InputLogOnePlusV = outerEnclosure 24
      (leaf2659Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2659RoundedFacts : LeafRoundedFacts 8
    leaf2659Certificate.logOnePlusV leaf2659InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2659InputLogOnePlusV_eq }

private noncomputable def leaf2659Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi133InputQChi innerPair50Input
    leaf2659InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2659LowerChecked :
    lowerCheck 24 leaf2659Box leaf2659Inputs = true := by
  rfl'

private theorem leaf2659CoversExact : CoversExact 8
    leaf2659Box leaf2659Certificate leaf2659InnerLog leaf2659Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi133RoundedFacts
    innerPair50RoundedFacts leaf2659RoundedFacts (by rfl)

private theorem leaf2659FlatSound : Sound leaf2659Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2659CertificateValid
    leaf2659InnerLogValid leaf2659CoversExact leaf2659LowerChecked

private noncomputable def leaf2660Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2660Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433700352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1728242129/1073741824) }, upper := { exponent := 0, mantissa := (6661/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870622207/274867400704) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2660InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2660LocalValidity :
    LeafFacts leaf2660Box leaf2660Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2660Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433700352) }) = true
      norm_num [leaf2660Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2660CertificateValid :
    WideCertificateValid leaf2660Box leaf2660Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi133ValidityFacts
    leaf2660LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2660CoverageChecked :
    coverageCheck (innerAD leaf2660Box) leaf2660InnerLog = true := by
  rfl'

private theorem leaf2660InnerLogValid :
    leaf2660InnerLog.Valid 8 (innerAD leaf2660Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2660CoverageChecked

private noncomputable def leaf2660InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2660InputLogOnePlusV_eq :
    leaf2660InputLogOnePlusV = outerEnclosure 24
      (leaf2660Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2660RoundedFacts : LeafRoundedFacts 8
    leaf2660Certificate.logOnePlusV leaf2660InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2660InputLogOnePlusV_eq }

private noncomputable def leaf2660Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi133InputQChi innerPair51Input
    leaf2660InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2660LowerChecked :
    lowerCheck 24 leaf2660Box leaf2660Inputs = true := by
  rfl'

private theorem leaf2660CoversExact : CoversExact 8
    leaf2660Box leaf2660Certificate leaf2660InnerLog leaf2660Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi133RoundedFacts
    innerPair51RoundedFacts leaf2660RoundedFacts (by rfl)

private theorem leaf2660FlatSound : Sound leaf2660Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2660CertificateValid
    leaf2660InnerLogValid leaf2660CoversExact leaf2660LowerChecked

private noncomputable def leaf2661Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2661Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433607168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1740168953/1073741824) }, upper := { exponent := 0, mantissa := (13413/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870529023/274867214336) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2661InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2661LocalValidity :
    LeafFacts leaf2661Box leaf2661Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2661Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433607168) }) = true
      norm_num [leaf2661Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2661CertificateValid :
    WideCertificateValid leaf2661Box leaf2661Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi134ValidityFacts
    leaf2661LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2661CoverageChecked :
    coverageCheck (innerAD leaf2661Box) leaf2661InnerLog = true := by
  rfl'

private theorem leaf2661InnerLogValid :
    leaf2661InnerLog.Valid 8 (innerAD leaf2661Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2661CoverageChecked

private noncomputable def leaf2661InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2661InputLogOnePlusV_eq :
    leaf2661InputLogOnePlusV = outerEnclosure 24
      (leaf2661Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2661RoundedFacts : LeafRoundedFacts 8
    leaf2661Certificate.logOnePlusV leaf2661InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2661InputLogOnePlusV_eq }

private noncomputable def leaf2661Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi134InputQChi innerPair51Input
    leaf2661InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2661LowerChecked :
    lowerCheck 24 leaf2661Box leaf2661Inputs = true := by
  rfl'

private theorem leaf2661CoversExact : CoversExact 8
    leaf2661Box leaf2661Certificate leaf2661InnerLog leaf2661Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi134RoundedFacts
    innerPair51RoundedFacts leaf2661RoundedFacts (by rfl)

private theorem leaf2661FlatSound : Sound leaf2661Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2661CertificateValid
    leaf2661InnerLogValid leaf2661CoversExact leaf2661LowerChecked

private noncomputable def leaf2662Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2662Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084328448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1743117891/1073741824) }, upper := { exponent := 0, mantissa := (3359/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168853263/16168656896) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2662InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2662LocalValidity :
    LeafFacts leaf2662Box leaf2662Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2662Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084328448) }) = true
      norm_num [leaf2662Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2662CertificateValid :
    WideCertificateValid leaf2662Box leaf2662Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi134ValidityFacts
    leaf2662LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2662CoverageChecked :
    coverageCheck (innerAD leaf2662Box) leaf2662InnerLog = true := by
  rfl'

private theorem leaf2662InnerLogValid :
    leaf2662InnerLog.Valid 8 (innerAD leaf2662Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2662CoverageChecked

private noncomputable def leaf2662InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2662InputLogOnePlusV_eq :
    leaf2662InputLogOnePlusV = outerEnclosure 24
      (leaf2662Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2662RoundedFacts : LeafRoundedFacts 8
    leaf2662Certificate.logOnePlusV leaf2662InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2662InputLogOnePlusV_eq }

private noncomputable def leaf2662Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi134InputQChi innerPair51Input
    leaf2662InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2662LowerChecked :
    lowerCheck 24 leaf2662Box leaf2662Inputs = true := by
  rfl'

private theorem leaf2662CoversExact : CoversExact 8
    leaf2662Box leaf2662Certificate leaf2662InnerLog leaf2662Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi134RoundedFacts
    innerPair51RoundedFacts leaf2662RoundedFacts (by rfl)

private theorem leaf2662FlatSound : Sound leaf2662Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2662CertificateValid
    leaf2662InnerLogValid leaf2662CoversExact leaf2662LowerChecked

private noncomputable def leaf2663Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2663Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433539072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1748950243/1073741824) }, upper := { exponent := 0, mantissa := (26959/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870460927/274867078144) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2663InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2663LocalValidity :
    LeafFacts leaf2663Box leaf2663Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2663Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433539072) }) = true
      norm_num [leaf2663Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2663CertificateValid :
    WideCertificateValid leaf2663Box leaf2663Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi135ValidityFacts
    leaf2663LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2663CoverageChecked :
    coverageCheck (innerAD leaf2663Box) leaf2663InnerLog = true := by
  rfl'

private theorem leaf2663InnerLogValid :
    leaf2663InnerLog.Valid 8 (innerAD leaf2663Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2663CoverageChecked

private noncomputable def leaf2663InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2663InputLogOnePlusV_eq :
    leaf2663InputLogOnePlusV = outerEnclosure 24
      (leaf2663Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2663RoundedFacts : LeafRoundedFacts 8
    leaf2663Certificate.logOnePlusV leaf2663InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2663InputLogOnePlusV_eq }

private noncomputable def leaf2663Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2663InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2663LowerChecked :
    lowerCheck 24 leaf2663Box leaf2663Inputs = true := by
  rfl'

private theorem leaf2663CoversExact : CoversExact 8
    leaf2663Box leaf2663Certificate leaf2663InnerLog leaf2663Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2663RoundedFacts (by rfl)

private theorem leaf2663FlatSound : Sound leaf2663Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2663CertificateValid
    leaf2663InnerLogValid leaf2663CoversExact leaf2663LowerChecked

private noncomputable def leaf2664Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2664Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196128256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1751964713/1073741824) }, upper := { exponent := 0, mantissa := (13503/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392335741/6392256512) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2664InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2664LocalValidity :
    LeafFacts leaf2664Box leaf2664Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2664Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196128256) }) = true
      norm_num [leaf2664Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2664CertificateValid :
    WideCertificateValid leaf2664Box leaf2664Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi135ValidityFacts
    leaf2664LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2664CoverageChecked :
    coverageCheck (innerAD leaf2664Box) leaf2664InnerLog = true := by
  rfl'

private theorem leaf2664InnerLogValid :
    leaf2664InnerLog.Valid 8 (innerAD leaf2664Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2664CoverageChecked

private noncomputable def leaf2664InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2664InputLogOnePlusV_eq :
    leaf2664InputLogOnePlusV = outerEnclosure 24
      (leaf2664Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2664RoundedFacts : LeafRoundedFacts 8
    leaf2664Certificate.logOnePlusV leaf2664InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2664InputLogOnePlusV_eq }

private noncomputable def leaf2664Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2664InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2664LowerChecked :
    lowerCheck 24 leaf2664Box leaf2664Inputs = true := by
  rfl'

private theorem leaf2664CoversExact : CoversExact 8
    leaf2664Box leaf2664Certificate leaf2664InnerLog leaf2664Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2664RoundedFacts (by rfl)

private theorem leaf2664FlatSound : Sound leaf2664Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2664CertificateValid
    leaf2664InnerLogValid leaf2664CoversExact leaf2664LowerChecked

private noncomputable def leaf2665Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2665Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433423872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1763629409/1073741824) }, upper := { exponent := 0, mantissa := (1699/1024) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870345727/274866847744) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf2665InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2665LocalValidity :
    LeafFacts leaf2665Box leaf2665Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2665Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433423872) }) = true
      norm_num [leaf2665Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2665CertificateValid :
    WideCertificateValid leaf2665Box leaf2665Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi136ValidityFacts
    leaf2665LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2665CoverageChecked :
    coverageCheck (innerAD leaf2665Box) leaf2665InnerLog = true := by
  rfl'

private theorem leaf2665InnerLogValid :
    leaf2665InnerLog.Valid 8 (innerAD leaf2665Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2665CoverageChecked

private noncomputable def leaf2665InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2665InputLogOnePlusV_eq :
    leaf2665InputLogOnePlusV = outerEnclosure 24
      (leaf2665Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2665RoundedFacts : LeafRoundedFacts 8
    leaf2665Certificate.logOnePlusV leaf2665InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2665InputLogOnePlusV_eq }

private noncomputable def leaf2665Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2665InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2665LowerChecked :
    lowerCheck 24 leaf2665Box leaf2665Inputs = true := by
  rfl'

private theorem leaf2665CoversExact : CoversExact 8
    leaf2665Box leaf2665Certificate leaf2665InnerLog leaf2665Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2665RoundedFacts (by rfl)

private theorem leaf2665FlatSound : Sound leaf2665Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2665CertificateValid
    leaf2665InnerLogValid leaf2665CoversExact leaf2665LowerChecked

private noncomputable def leaf2666Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2666Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433399296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1766709411/1073741824) }, upper := { exponent := 0, mantissa := (851/512) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870321151/274866798592) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf2666InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2666LocalValidity :
    LeafFacts leaf2666Box leaf2666Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2666Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433399296) }) = true
      norm_num [leaf2666Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2666CertificateValid :
    WideCertificateValid leaf2666Box leaf2666Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi136ValidityFacts
    leaf2666LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2666CoverageChecked :
    coverageCheck (innerAD leaf2666Box) leaf2666InnerLog = true := by
  rfl'

private theorem leaf2666InnerLogValid :
    leaf2666InnerLog.Valid 8 (innerAD leaf2666Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2666CoverageChecked

private noncomputable def leaf2666InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2666InputLogOnePlusV_eq :
    leaf2666InputLogOnePlusV = outerEnclosure 24
      (leaf2666Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2666RoundedFacts : LeafRoundedFacts 8
    leaf2666Certificate.logOnePlusV leaf2666InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2666InputLogOnePlusV_eq }

private noncomputable def leaf2666Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2666InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2666LowerChecked :
    lowerCheck 24 leaf2666Box leaf2666Inputs = true := by
  rfl'

private theorem leaf2666CoversExact : CoversExact 8
    leaf2666Box leaf2666Certificate leaf2666InnerLog leaf2666Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2666RoundedFacts (by rfl)

private theorem leaf2666FlatSound : Sound leaf2666Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2666CertificateValid
    leaf2666InnerLogValid leaf2666CoversExact leaf2666LowerChecked

private noncomputable def leaf2667Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2667Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811163648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1754979183/1073741824) }, upper := { exponent := 0, mantissa := (27053/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623470933/91622327296) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2667InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2667LocalValidity :
    LeafFacts leaf2667Box leaf2667Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2667Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811163648) }) = true
      norm_num [leaf2667Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2667CertificateValid :
    WideCertificateValid leaf2667Box leaf2667Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi135ValidityFacts
    leaf2667LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2667CoverageChecked :
    coverageCheck (innerAD leaf2667Box) leaf2667InnerLog = true := by
  rfl'

private theorem leaf2667InnerLogValid :
    leaf2667InnerLog.Valid 8 (innerAD leaf2667Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2667CoverageChecked

private noncomputable def leaf2667InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2667InputLogOnePlusV_eq :
    leaf2667InputLogOnePlusV = outerEnclosure 24
      (leaf2667Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2667RoundedFacts : LeafRoundedFacts 8
    leaf2667Certificate.logOnePlusV leaf2667InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2667InputLogOnePlusV_eq }

private noncomputable def leaf2667Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2667InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2667LowerChecked :
    lowerCheck 24 leaf2667Box leaf2667Inputs = true := by
  rfl'

private theorem leaf2667CoversExact : CoversExact 8
    leaf2667Box leaf2667Certificate leaf2667InnerLog leaf2667Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2667RoundedFacts (by rfl)

private theorem leaf2667FlatSound : Sound leaf2667Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2667CertificateValid
    leaf2667InnerLogValid leaf2667CoversExact leaf2667LowerChecked

private noncomputable def leaf2668Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2668Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486693376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1757993653/1073741824) }, upper := { exponent := 0, mantissa := (6775/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974077747/54973386752) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2668InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2668LocalValidity :
    LeafFacts leaf2668Box leaf2668Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2668Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486693376) }) = true
      norm_num [leaf2668Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2668CertificateValid :
    WideCertificateValid leaf2668Box leaf2668Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi135ValidityFacts
    leaf2668LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2668CoverageChecked :
    coverageCheck (innerAD leaf2668Box) leaf2668InnerLog = true := by
  rfl'

private theorem leaf2668InnerLogValid :
    leaf2668InnerLog.Valid 8 (innerAD leaf2668Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2668CoverageChecked

private noncomputable def leaf2668InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2668InputLogOnePlusV_eq :
    leaf2668InputLogOnePlusV = outerEnclosure 24
      (leaf2668Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2668RoundedFacts : LeafRoundedFacts 8
    leaf2668Certificate.logOnePlusV leaf2668InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2668InputLogOnePlusV_eq }

private noncomputable def leaf2668Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2668InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2668LowerChecked :
    lowerCheck 24 leaf2668Box leaf2668Inputs = true := by
  rfl'

private theorem leaf2668CoversExact : CoversExact 8
    leaf2668Box leaf2668Certificate leaf2668InnerLog leaf2668Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2668RoundedFacts (by rfl)

private theorem leaf2668FlatSound : Sound leaf2668Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2668CertificateValid
    leaf2668InnerLogValid leaf2668CoversExact leaf2668LowerChecked

private noncomputable def leaf2669Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2669Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1616904963/1616863232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1769789413/1073741824) }, upper := { exponent := 0, mantissa := (1705/1024) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3233768195/3233726464) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf2669InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2669LocalValidity :
    LeafFacts leaf2669Box leaf2669Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2669Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1616904963/1616863232) }) = true
      norm_num [leaf2669Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2669CertificateValid :
    WideCertificateValid leaf2669Box leaf2669Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi136ValidityFacts
    leaf2669LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2669CoverageChecked :
    coverageCheck (innerAD leaf2669Box) leaf2669InnerLog = true := by
  rfl'

private theorem leaf2669InnerLogValid :
    leaf2669InnerLog.Valid 8 (innerAD leaf2669Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2669CoverageChecked

private noncomputable def leaf2669InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2669InputLogOnePlusV_eq :
    leaf2669InputLogOnePlusV = outerEnclosure 24
      (leaf2669Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2669RoundedFacts : LeafRoundedFacts 8
    leaf2669Certificate.logOnePlusV leaf2669InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2669InputLogOnePlusV_eq }

private noncomputable def leaf2669Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2669InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2669LowerChecked :
    lowerCheck 24 leaf2669Box leaf2669Inputs = true := by
  rfl'

private theorem leaf2669CoversExact : CoversExact 8
    leaf2669Box leaf2669Certificate leaf2669InnerLog leaf2669Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2669RoundedFacts (by rfl)

private theorem leaf2669FlatSound : Sound leaf2669Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2669CertificateValid
    leaf2669InnerLogValid leaf2669CoversExact leaf2669LowerChecked

private noncomputable def leaf2670Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2670Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433350144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1772869415/1073741824) }, upper := { exponent := 0, mantissa := (427/256) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870271999/274866700288) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf2670InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2670LocalValidity :
    LeafFacts leaf2670Box leaf2670Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2670Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433350144) }) = true
      norm_num [leaf2670Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2670CertificateValid :
    WideCertificateValid leaf2670Box leaf2670Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi136ValidityFacts
    leaf2670LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2670CoverageChecked :
    coverageCheck (innerAD leaf2670Box) leaf2670InnerLog = true := by
  rfl'

private theorem leaf2670InnerLogValid :
    leaf2670InnerLog.Valid 8 (innerAD leaf2670Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2670CoverageChecked

private noncomputable def leaf2670InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2670InputLogOnePlusV_eq :
    leaf2670InputLogOnePlusV = outerEnclosure 24
      (leaf2670Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2670RoundedFacts : LeafRoundedFacts 8
    leaf2670Certificate.logOnePlusV leaf2670InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2670InputLogOnePlusV_eq }

private noncomputable def leaf2670Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2670InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2670LowerChecked :
    lowerCheck 24 leaf2670Box leaf2670Inputs = true := by
  rfl'

private theorem leaf2670CoversExact : CoversExact 8
    leaf2670Box leaf2670Certificate leaf2670InnerLog leaf2670Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2670RoundedFacts (by rfl)

private theorem leaf2670FlatSound : Sound leaf2670Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2670CertificateValid
    leaf2670InnerLogValid leaf2670CoversExact leaf2670LowerChecked

private noncomputable def leaf2671Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2671Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433677312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1731125535/1073741824) }, upper := { exponent := 0, mantissa := (26689/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870599167/274867354624) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2671InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2671LocalValidity :
    LeafFacts leaf2671Box leaf2671Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2671Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433677312) }) = true
      norm_num [leaf2671Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2671CertificateValid :
    WideCertificateValid leaf2671Box leaf2671Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi133ValidityFacts
    leaf2671LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2671CoverageChecked :
    coverageCheck (innerAD leaf2671Box) leaf2671InnerLog = true := by
  rfl'

private theorem leaf2671InnerLogValid :
    leaf2671InnerLog.Valid 8 (innerAD leaf2671Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2671CoverageChecked

private noncomputable def leaf2671InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2671InputLogOnePlusV_eq :
    leaf2671InputLogOnePlusV = outerEnclosure 24
      (leaf2671Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2671RoundedFacts : LeafRoundedFacts 8
    leaf2671Certificate.logOnePlusV leaf2671InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2671InputLogOnePlusV_eq }

private noncomputable def leaf2671Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi133InputQChi innerPair51Input
    leaf2671InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2671LowerChecked :
    lowerCheck 24 leaf2671Box leaf2671Inputs = true := by
  rfl'

private theorem leaf2671CoversExact : CoversExact 8
    leaf2671Box leaf2671Certificate leaf2671InnerLog leaf2671Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi133RoundedFacts
    innerPair51RoundedFacts leaf2671RoundedFacts (by rfl)

private theorem leaf2671FlatSound : Sound leaf2671Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2671CertificateValid
    leaf2671InnerLogValid leaf2671CoversExact leaf2671LowerChecked

private noncomputable def leaf2672Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2672Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433654272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1734008941/1073741824) }, upper := { exponent := 0, mantissa := (13367/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870576127/274867308544) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2672InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2672LocalValidity :
    LeafFacts leaf2672Box leaf2672Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2672Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433654272) }) = true
      norm_num [leaf2672Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2672CertificateValid :
    WideCertificateValid leaf2672Box leaf2672Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi133ValidityFacts
    leaf2672LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2672CoverageChecked :
    coverageCheck (innerAD leaf2672Box) leaf2672InnerLog = true := by
  rfl'

private theorem leaf2672InnerLogValid :
    leaf2672InnerLog.Valid 8 (innerAD leaf2672Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2672CoverageChecked

private noncomputable def leaf2672InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2672InputLogOnePlusV_eq :
    leaf2672InputLogOnePlusV = outerEnclosure 24
      (leaf2672Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2672RoundedFacts : LeafRoundedFacts 8
    leaf2672Certificate.logOnePlusV leaf2672InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2672InputLogOnePlusV_eq }

private noncomputable def leaf2672Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi133InputQChi innerPair51Input
    leaf2672InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2672LowerChecked :
    lowerCheck 24 leaf2672Box leaf2672Inputs = true := by
  rfl'

private theorem leaf2672CoversExact : CoversExact 8
    leaf2672Box leaf2672Certificate leaf2672InnerLog leaf2672Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi133RoundedFacts
    innerPair51RoundedFacts leaf2672RoundedFacts (by rfl)

private theorem leaf2672FlatSound : Sound leaf2672Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2672CertificateValid
    leaf2672InnerLogValid leaf2672CoversExact leaf2672LowerChecked

private noncomputable def leaf2673Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2673Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811186688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1746066829/1073741824) }, upper := { exponent := 0, mantissa := (13459/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623493973/91622373376) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2673InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2673LocalValidity :
    LeafFacts leaf2673Box leaf2673Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2673Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811186688) }) = true
      norm_num [leaf2673Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2673CertificateValid :
    WideCertificateValid leaf2673Box leaf2673Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi134ValidityFacts
    leaf2673LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2673CoverageChecked :
    coverageCheck (innerAD leaf2673Box) leaf2673InnerLog = true := by
  rfl'

private theorem leaf2673InnerLogValid :
    leaf2673InnerLog.Valid 8 (innerAD leaf2673Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2673CoverageChecked

private noncomputable def leaf2673InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2673InputLogOnePlusV_eq :
    leaf2673InputLogOnePlusV = outerEnclosure 24
      (leaf2673Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2673RoundedFacts : LeafRoundedFacts 8
    leaf2673Certificate.logOnePlusV leaf2673InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2673InputLogOnePlusV_eq }

private noncomputable def leaf2673Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2673InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2673LowerChecked :
    lowerCheck 24 leaf2673Box leaf2673Inputs = true := by
  rfl'

private theorem leaf2673CoversExact : CoversExact 8
    leaf2673Box leaf2673Certificate leaf2673InnerLog leaf2673Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2673RoundedFacts (by rfl)

private theorem leaf2673FlatSound : Sound leaf2673Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2673CertificateValid
    leaf2673InnerLogValid leaf2673CoversExact leaf2673LowerChecked

private noncomputable def leaf2674Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2674Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433536512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1749015767/1073741824) }, upper := { exponent := 0, mantissa := (6741/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870458367/274867073024) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2674InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2674LocalValidity :
    LeafFacts leaf2674Box leaf2674Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2674Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433536512) }) = true
      norm_num [leaf2674Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2674CertificateValid :
    WideCertificateValid leaf2674Box leaf2674Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi134ValidityFacts
    leaf2674LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2674CoverageChecked :
    coverageCheck (innerAD leaf2674Box) leaf2674InnerLog = true := by
  rfl'

private theorem leaf2674InnerLogValid :
    leaf2674InnerLog.Valid 8 (innerAD leaf2674Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2674CoverageChecked

private noncomputable def leaf2674InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2674InputLogOnePlusV_eq :
    leaf2674InputLogOnePlusV = outerEnclosure 24
      (leaf2674Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2674RoundedFacts : LeafRoundedFacts 8
    leaf2674Certificate.logOnePlusV leaf2674InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2674InputLogOnePlusV_eq }

private noncomputable def leaf2674Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2674InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2674LowerChecked :
    lowerCheck 24 leaf2674Box leaf2674Inputs = true := by
  rfl'

private theorem leaf2674CoversExact : CoversExact 8
    leaf2674Box leaf2674Certificate leaf2674InnerLog leaf2674Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2674RoundedFacts (by rfl)

private theorem leaf2674FlatSound : Sound leaf2674Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2674CertificateValid
    leaf2674InnerLogValid leaf2674CoversExact leaf2674LowerChecked

private noncomputable def leaf2675Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2675Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433631232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1736892347/1073741824) }, upper := { exponent := 0, mantissa := (26779/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870553087/274867262464) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2675InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2675LocalValidity :
    LeafFacts leaf2675Box leaf2675Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2675Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433631232) }) = true
      norm_num [leaf2675Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2675CertificateValid :
    WideCertificateValid leaf2675Box leaf2675Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi133ValidityFacts
    leaf2675LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2675CoverageChecked :
    coverageCheck (innerAD leaf2675Box) leaf2675InnerLog = true := by
  rfl'

private theorem leaf2675InnerLogValid :
    leaf2675InnerLog.Valid 8 (innerAD leaf2675Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2675CoverageChecked

private noncomputable def leaf2675InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2675InputLogOnePlusV_eq :
    leaf2675InputLogOnePlusV = outerEnclosure 24
      (leaf2675Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2675RoundedFacts : LeafRoundedFacts 8
    leaf2675Certificate.logOnePlusV leaf2675InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2675InputLogOnePlusV_eq }

private noncomputable def leaf2675Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi133InputQChi innerPair51Input
    leaf2675InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2675LowerChecked :
    lowerCheck 24 leaf2675Box leaf2675Inputs = true := by
  rfl'

private theorem leaf2675CoversExact : CoversExact 8
    leaf2675Box leaf2675Certificate leaf2675InnerLog leaf2675Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi133RoundedFacts
    innerPair51RoundedFacts leaf2675RoundedFacts (by rfl)

private theorem leaf2675FlatSound : Sound leaf2675Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2675CertificateValid
    leaf2675InnerLogValid leaf2675CoversExact leaf2675LowerChecked

private noncomputable def leaf2676Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2676Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433608192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1739775753/1073741824) }, upper := { exponent := 0, mantissa := (3353/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870530047/274867216384) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2676InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf2676LocalValidity :
    LeafFacts leaf2676Box leaf2676Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2676Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433608192) }) = true
      norm_num [leaf2676Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2676CertificateValid :
    WideCertificateValid leaf2676Box leaf2676Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi133ValidityFacts
    leaf2676LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2676CoverageChecked :
    coverageCheck (innerAD leaf2676Box) leaf2676InnerLog = true := by
  rfl'

private theorem leaf2676InnerLogValid :
    leaf2676InnerLog.Valid 8 (innerAD leaf2676Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf2676CoverageChecked

private noncomputable def leaf2676InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2676InputLogOnePlusV_eq :
    leaf2676InputLogOnePlusV = outerEnclosure 24
      (leaf2676Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2676RoundedFacts : LeafRoundedFacts 8
    leaf2676Certificate.logOnePlusV leaf2676InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2676InputLogOnePlusV_eq }

private noncomputable def leaf2676Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi133InputQChi innerPair51Input
    leaf2676InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2676LowerChecked :
    lowerCheck 24 leaf2676Box leaf2676Inputs = true := by
  rfl'

private theorem leaf2676CoversExact : CoversExact 8
    leaf2676Box leaf2676Certificate leaf2676InnerLog leaf2676Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi133RoundedFacts
    innerPair51RoundedFacts leaf2676RoundedFacts (by rfl)

private theorem leaf2676FlatSound : Sound leaf2676Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2676CertificateValid
    leaf2676InnerLogValid leaf2676CoversExact leaf2676LowerChecked

private noncomputable def leaf2677Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2677Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486702592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1751964705/1073741824) }, upper := { exponent := 0, mantissa := (13505/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974086963/54973405184) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2677InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2677LocalValidity :
    LeafFacts leaf2677Box leaf2677Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2677Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486702592) }) = true
      norm_num [leaf2677Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2677CertificateValid :
    WideCertificateValid leaf2677Box leaf2677Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi134ValidityFacts
    leaf2677LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2677CoverageChecked :
    coverageCheck (innerAD leaf2677Box) leaf2677InnerLog = true := by
  rfl'

private theorem leaf2677InnerLogValid :
    leaf2677InnerLog.Valid 8 (innerAD leaf2677Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2677CoverageChecked

private noncomputable def leaf2677InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2677InputLogOnePlusV_eq :
    leaf2677InputLogOnePlusV = outerEnclosure 24
      (leaf2677Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2677RoundedFacts : LeafRoundedFacts 8
    leaf2677Certificate.logOnePlusV leaf2677InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2677InputLogOnePlusV_eq }

private noncomputable def leaf2677Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2677InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2677LowerChecked :
    lowerCheck 24 leaf2677Box leaf2677Inputs = true := by
  rfl'

private theorem leaf2677CoversExact : CoversExact 8
    leaf2677Box leaf2677Certificate leaf2677InnerLog leaf2677Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2677RoundedFacts (by rfl)

private theorem leaf2677FlatSound : Sound leaf2677Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2677CertificateValid
    leaf2677InnerLogValid leaf2677CoversExact leaf2677LowerChecked

private noncomputable def leaf2678Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2678Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270387712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1754913643/1073741824) }, upper := { exponent := 0, mantissa := (1691/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541156807/30540775424) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2678InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2678LocalValidity :
    LeafFacts leaf2678Box leaf2678Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2678Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270387712) }) = true
      norm_num [leaf2678Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2678CertificateValid :
    WideCertificateValid leaf2678Box leaf2678Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi134ValidityFacts
    leaf2678LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2678CoverageChecked :
    coverageCheck (innerAD leaf2678Box) leaf2678InnerLog = true := by
  rfl'

private theorem leaf2678InnerLogValid :
    leaf2678InnerLog.Valid 8 (innerAD leaf2678Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2678CoverageChecked

private noncomputable def leaf2678InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2678InputLogOnePlusV_eq :
    leaf2678InputLogOnePlusV = outerEnclosure 24
      (leaf2678Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2678RoundedFacts : LeafRoundedFacts 8
    leaf2678Certificate.logOnePlusV leaf2678InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2678InputLogOnePlusV_eq }

private noncomputable def leaf2678Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi134InputQChi innerPair56Input
    leaf2678InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2678LowerChecked :
    lowerCheck 24 leaf2678Box leaf2678Inputs = true := by
  rfl'

private theorem leaf2678CoversExact : CoversExact 8
    leaf2678Box leaf2678Certificate leaf2678InnerLog leaf2678Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi134RoundedFacts
    innerPair56RoundedFacts leaf2678RoundedFacts (by rfl)

private theorem leaf2678FlatSound : Sound leaf2678Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2678CertificateValid
    leaf2678InnerLogValid leaf2678CoversExact leaf2678LowerChecked

private noncomputable def leaf2679Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2679Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433442816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1761008123/1073741824) }, upper := { exponent := 0, mantissa := (27147/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870364671/274866885632) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2679InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2679LocalValidity :
    LeafFacts leaf2679Box leaf2679Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2679Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433442816) }) = true
      norm_num [leaf2679Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2679CertificateValid :
    WideCertificateValid leaf2679Box leaf2679Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi135ValidityFacts
    leaf2679LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2679CoverageChecked :
    coverageCheck (innerAD leaf2679Box) leaf2679InnerLog = true := by
  rfl'

private theorem leaf2679InnerLogValid :
    leaf2679InnerLog.Valid 8 (innerAD leaf2679Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2679CoverageChecked

private noncomputable def leaf2679InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2679InputLogOnePlusV_eq :
    leaf2679InputLogOnePlusV = outerEnclosure 24
      (leaf2679Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2679RoundedFacts : LeafRoundedFacts 8
    leaf2679Certificate.logOnePlusV leaf2679InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2679InputLogOnePlusV_eq }

private noncomputable def leaf2679Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2679InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2679LowerChecked :
    lowerCheck 24 leaf2679Box leaf2679Inputs = true := by
  rfl'

private theorem leaf2679CoversExact : CoversExact 8
    leaf2679Box leaf2679Certificate leaf2679InnerLog leaf2679Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2679RoundedFacts (by rfl)

private theorem leaf2679FlatSound : Sound leaf2679Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2679CertificateValid
    leaf2679InnerLogValid leaf2679CoversExact leaf2679LowerChecked

private noncomputable def leaf2680Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2680Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811139584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1764022593/1073741824) }, upper := { exponent := 0, mantissa := (13597/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623446869/91622279168) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2680InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2680LocalValidity :
    LeafFacts leaf2680Box leaf2680Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2680Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811139584) }) = true
      norm_num [leaf2680Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2680CertificateValid :
    WideCertificateValid leaf2680Box leaf2680Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi135ValidityFacts
    leaf2680LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2680CoverageChecked :
    coverageCheck (innerAD leaf2680Box) leaf2680InnerLog = true := by
  rfl'

private theorem leaf2680InnerLogValid :
    leaf2680InnerLog.Valid 8 (innerAD leaf2680Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2680CoverageChecked

private noncomputable def leaf2680InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2680InputLogOnePlusV_eq :
    leaf2680InputLogOnePlusV = outerEnclosure 24
      (leaf2680Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2680RoundedFacts : LeafRoundedFacts 8
    leaf2680Certificate.logOnePlusV leaf2680InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2680InputLogOnePlusV_eq }

private noncomputable def leaf2680Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2680InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2680LowerChecked :
    lowerCheck 24 leaf2680Box leaf2680Inputs = true := by
  rfl'

private theorem leaf2680CoversExact : CoversExact 8
    leaf2680Box leaf2680Certificate leaf2680InnerLog leaf2680Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2680RoundedFacts (by rfl)

private theorem leaf2680FlatSound : Sound leaf2680Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2680CertificateValid
    leaf2680InnerLogValid leaf2680CoversExact leaf2680LowerChecked

private noncomputable def leaf2681Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2681Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433325568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1775949417/1073741824) }, upper := { exponent := 0, mantissa := (1711/1024) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870247423/274866651136) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf2681InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2681LocalValidity :
    LeafFacts leaf2681Box leaf2681Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2681Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433325568) }) = true
      norm_num [leaf2681Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2681CertificateValid :
    WideCertificateValid leaf2681Box leaf2681Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi136ValidityFacts
    leaf2681LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2681CoverageChecked :
    coverageCheck (innerAD leaf2681Box) leaf2681InnerLog = true := by
  rfl'

private theorem leaf2681InnerLogValid :
    leaf2681InnerLog.Valid 8 (innerAD leaf2681Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2681CoverageChecked

private noncomputable def leaf2681InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2681InputLogOnePlusV_eq :
    leaf2681InputLogOnePlusV = outerEnclosure 24
      (leaf2681Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2681RoundedFacts : LeafRoundedFacts 8
    leaf2681Certificate.logOnePlusV leaf2681InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2681InputLogOnePlusV_eq }

private noncomputable def leaf2681Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2681InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2681LowerChecked :
    lowerCheck 24 leaf2681Box leaf2681Inputs = true := by
  rfl'

private theorem leaf2681CoversExact : CoversExact 8
    leaf2681Box leaf2681Certificate leaf2681InnerLog leaf2681Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2681RoundedFacts (by rfl)

private theorem leaf2681FlatSound : Sound leaf2681Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2681CertificateValid
    leaf2681InnerLogValid leaf2681CoversExact leaf2681LowerChecked

private noncomputable def leaf2682Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2682Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433300992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1779029419/1073741824) }, upper := { exponent := 0, mantissa := (857/512) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870222847/274866601984) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf2682InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2682LocalValidity :
    LeafFacts leaf2682Box leaf2682Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2682Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433300992) }) = true
      norm_num [leaf2682Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2682CertificateValid :
    WideCertificateValid leaf2682Box leaf2682Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi136ValidityFacts
    leaf2682LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2682CoverageChecked :
    coverageCheck (innerAD leaf2682Box) leaf2682InnerLog = true := by
  rfl'

private theorem leaf2682InnerLogValid :
    leaf2682InnerLog.Valid 8 (innerAD leaf2682Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2682CoverageChecked

private noncomputable def leaf2682InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2682InputLogOnePlusV_eq :
    leaf2682InputLogOnePlusV = outerEnclosure 24
      (leaf2682Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2682RoundedFacts : LeafRoundedFacts 8
    leaf2682Certificate.logOnePlusV leaf2682InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2682InputLogOnePlusV_eq }

private noncomputable def leaf2682Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2682InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2682LowerChecked :
    lowerCheck 24 leaf2682Box leaf2682Inputs = true := by
  rfl'

private theorem leaf2682CoversExact : CoversExact 8
    leaf2682Box leaf2682Certificate leaf2682InnerLog leaf2682Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2682RoundedFacts (by rfl)

private theorem leaf2682FlatSound : Sound leaf2682Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2682CertificateValid
    leaf2682InnerLogValid leaf2682CoversExact leaf2682LowerChecked

private noncomputable def leaf2683Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2683Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433394688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1767037063/1073741824) }, upper := { exponent := 0, mantissa := (27241/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870316543/274866789376) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2683InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2683LocalValidity :
    LeafFacts leaf2683Box leaf2683Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2683Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433394688) }) = true
      norm_num [leaf2683Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2683CertificateValid :
    WideCertificateValid leaf2683Box leaf2683Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi135ValidityFacts
    leaf2683LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2683CoverageChecked :
    coverageCheck (innerAD leaf2683Box) leaf2683InnerLog = true := by
  rfl'

private theorem leaf2683InnerLogValid :
    leaf2683InnerLog.Valid 8 (innerAD leaf2683Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2683CoverageChecked

private noncomputable def leaf2683InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2683InputLogOnePlusV_eq :
    leaf2683InputLogOnePlusV = outerEnclosure 24
      (leaf2683Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2683RoundedFacts : LeafRoundedFacts 8
    leaf2683Certificate.logOnePlusV leaf2683InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2683InputLogOnePlusV_eq }

private noncomputable def leaf2683Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2683InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2683LowerChecked :
    lowerCheck 24 leaf2683Box leaf2683Inputs = true := by
  rfl'

private theorem leaf2683CoversExact : CoversExact 8
    leaf2683Box leaf2683Certificate leaf2683InnerLog leaf2683Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2683RoundedFacts (by rfl)

private theorem leaf2683FlatSound : Sound leaf2683Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2683CertificateValid
    leaf2683InnerLogValid leaf2683CoversExact leaf2683LowerChecked

private noncomputable def leaf2684Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2684Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433370624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1770051533/1073741824) }, upper := { exponent := 0, mantissa := (3411/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870292479/274866741248) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2684InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2684LocalValidity :
    LeafFacts leaf2684Box leaf2684Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2684Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433370624) }) = true
      norm_num [leaf2684Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2684CertificateValid :
    WideCertificateValid leaf2684Box leaf2684Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi135ValidityFacts
    leaf2684LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2684CoverageChecked :
    coverageCheck (innerAD leaf2684Box) leaf2684InnerLog = true := by
  rfl'

private theorem leaf2684InnerLogValid :
    leaf2684InnerLog.Valid 8 (innerAD leaf2684Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2684CoverageChecked

private noncomputable def leaf2684InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2684InputLogOnePlusV_eq :
    leaf2684InputLogOnePlusV = outerEnclosure 24
      (leaf2684Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2684RoundedFacts : LeafRoundedFacts 8
    leaf2684Certificate.logOnePlusV leaf2684InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2684InputLogOnePlusV_eq }

private noncomputable def leaf2684Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi135InputQChi innerPair56Input
    leaf2684InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2684LowerChecked :
    lowerCheck 24 leaf2684Box leaf2684Inputs = true := by
  rfl'

private theorem leaf2684CoversExact : CoversExact 8
    leaf2684Box leaf2684Certificate leaf2684InnerLog leaf2684Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi135RoundedFacts
    innerPair56RoundedFacts leaf2684RoundedFacts (by rfl)

private theorem leaf2684FlatSound : Sound leaf2684Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2684CertificateValid
    leaf2684InnerLogValid leaf2684CoversExact leaf2684LowerChecked

private noncomputable def leaf2685Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2685Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433276416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1782109421/1073741824) }, upper := { exponent := 0, mantissa := (1717/1024) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870198271/274866552832) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf2685InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2685LocalValidity :
    LeafFacts leaf2685Box leaf2685Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2685Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433276416) }) = true
      norm_num [leaf2685Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2685CertificateValid :
    WideCertificateValid leaf2685Box leaf2685Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi136ValidityFacts
    leaf2685LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2685CoverageChecked :
    coverageCheck (innerAD leaf2685Box) leaf2685InnerLog = true := by
  rfl'

private theorem leaf2685InnerLogValid :
    leaf2685InnerLog.Valid 8 (innerAD leaf2685Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2685CoverageChecked

private noncomputable def leaf2685InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2685InputLogOnePlusV_eq :
    leaf2685InputLogOnePlusV = outerEnclosure 24
      (leaf2685Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2685RoundedFacts : LeafRoundedFacts 8
    leaf2685Certificate.logOnePlusV leaf2685InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2685InputLogOnePlusV_eq }

private noncomputable def leaf2685Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2685InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2685LowerChecked :
    lowerCheck 24 leaf2685Box leaf2685Inputs = true := by
  rfl'

private theorem leaf2685CoversExact : CoversExact 8
    leaf2685Box leaf2685Certificate leaf2685InnerLog leaf2685Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2685RoundedFacts (by rfl)

private theorem leaf2685FlatSound : Sound leaf2685Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2685CertificateValid
    leaf2685InnerLogValid leaf2685CoversExact leaf2685LowerChecked

private noncomputable def leaf2686Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2686Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486650368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1785189423/1073741824) }, upper := { exponent := 0, mantissa := (215/128) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974034739/54973300736) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf2686InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2686LocalValidity :
    LeafFacts leaf2686Box leaf2686Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2686Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486650368) }) = true
      norm_num [leaf2686Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2686CertificateValid :
    WideCertificateValid leaf2686Box leaf2686Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi136ValidityFacts
    leaf2686LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2686CoverageChecked :
    coverageCheck (innerAD leaf2686Box) leaf2686InnerLog = true := by
  rfl'

private theorem leaf2686InnerLogValid :
    leaf2686InnerLog.Valid 8 (innerAD leaf2686Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2686CoverageChecked

private noncomputable def leaf2686InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2686InputLogOnePlusV_eq :
    leaf2686InputLogOnePlusV = outerEnclosure 24
      (leaf2686Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2686RoundedFacts : LeafRoundedFacts 8
    leaf2686Certificate.logOnePlusV leaf2686InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2686InputLogOnePlusV_eq }

private noncomputable def leaf2686Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi136InputQChi innerPair56Input
    leaf2686InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2686LowerChecked :
    lowerCheck 24 leaf2686Box leaf2686Inputs = true := by
  rfl'

private theorem leaf2686CoversExact : CoversExact 8
    leaf2686Box leaf2686Certificate leaf2686InnerLog leaf2686Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi136RoundedFacts
    innerPair56RoundedFacts leaf2686RoundedFacts (by rfl)

private theorem leaf2686FlatSound : Sound leaf2686Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2686CertificateValid
    leaf2686InnerLogValid leaf2686CoversExact leaf2686LowerChecked

private noncomputable def component56Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node0_sound : Sound component56Node0Box :=
  sound_of_literal_split component56Node0Box leaf2623Box leaf2624Box
    .k (225/64) (by rfl) (by rfl)
    leaf2623FlatSound leaf2624FlatSound

private noncomputable def component56Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node1_sound : Sound component56Node1Box :=
  sound_of_literal_split component56Node1Box leaf2625Box leaf2626Box
    .k (225/64) (by rfl) (by rfl)
    leaf2625FlatSound leaf2626FlatSound

private noncomputable def component56Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node2_sound : Sound component56Node2Box :=
  sound_of_literal_split component56Node2Box component56Node0Box component56Node1Box
    .chi (41/256) (by rfl) (by rfl)
    component56Node0_sound component56Node1_sound

private noncomputable def component56Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node3_sound : Sound component56Node3Box :=
  sound_of_literal_split component56Node3Box leaf2627Box leaf2628Box
    .k (227/64) (by rfl) (by rfl)
    leaf2627FlatSound leaf2628FlatSound

private noncomputable def component56Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node4_sound : Sound component56Node4Box :=
  sound_of_literal_split component56Node4Box leaf2629Box leaf2630Box
    .k (227/64) (by rfl) (by rfl)
    leaf2629FlatSound leaf2630FlatSound

private noncomputable def component56Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node5_sound : Sound component56Node5Box :=
  sound_of_literal_split component56Node5Box component56Node3Box component56Node4Box
    .chi (41/256) (by rfl) (by rfl)
    component56Node3_sound component56Node4_sound

private noncomputable def component56Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node6_sound : Sound component56Node6Box :=
  sound_of_literal_split component56Node6Box component56Node2Box component56Node5Box
    .k (113/32) (by rfl) (by rfl)
    component56Node2_sound component56Node5_sound

private noncomputable def component56Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node7_sound : Sound component56Node7Box :=
  sound_of_literal_split component56Node7Box leaf2631Box leaf2632Box
    .k (225/64) (by rfl) (by rfl)
    leaf2631FlatSound leaf2632FlatSound

private noncomputable def component56Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node8_sound : Sound component56Node8Box :=
  sound_of_literal_split component56Node8Box leaf2633Box leaf2634Box
    .k (225/64) (by rfl) (by rfl)
    leaf2633FlatSound leaf2634FlatSound

private noncomputable def component56Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node9_sound : Sound component56Node9Box :=
  sound_of_literal_split component56Node9Box component56Node7Box component56Node8Box
    .chi (43/256) (by rfl) (by rfl)
    component56Node7_sound component56Node8_sound

private noncomputable def component56Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node10_sound : Sound component56Node10Box :=
  sound_of_literal_split component56Node10Box leaf2635Box leaf2636Box
    .k (227/64) (by rfl) (by rfl)
    leaf2635FlatSound leaf2636FlatSound

private noncomputable def component56Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node11_sound : Sound component56Node11Box :=
  sound_of_literal_split component56Node11Box leaf2637Box leaf2638Box
    .k (227/64) (by rfl) (by rfl)
    leaf2637FlatSound leaf2638FlatSound

private noncomputable def component56Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node12_sound : Sound component56Node12Box :=
  sound_of_literal_split component56Node12Box component56Node10Box component56Node11Box
    .chi (43/256) (by rfl) (by rfl)
    component56Node10_sound component56Node11_sound

private noncomputable def component56Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node13_sound : Sound component56Node13Box :=
  sound_of_literal_split component56Node13Box component56Node9Box component56Node12Box
    .k (113/32) (by rfl) (by rfl)
    component56Node9_sound component56Node12_sound

private noncomputable def component56Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node14_sound : Sound component56Node14Box :=
  sound_of_literal_split component56Node14Box component56Node6Box component56Node13Box
    .chi (21/128) (by rfl) (by rfl)
    component56Node6_sound component56Node13_sound

private noncomputable def component56Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node15_sound : Sound component56Node15Box :=
  sound_of_literal_split component56Node15Box leaf2639Box leaf2640Box
    .k (229/64) (by rfl) (by rfl)
    leaf2639FlatSound leaf2640FlatSound

private noncomputable def component56Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node16_sound : Sound component56Node16Box :=
  sound_of_literal_split component56Node16Box leaf2641Box leaf2642Box
    .k (229/64) (by rfl) (by rfl)
    leaf2641FlatSound leaf2642FlatSound

private noncomputable def component56Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node17_sound : Sound component56Node17Box :=
  sound_of_literal_split component56Node17Box component56Node15Box component56Node16Box
    .chi (41/256) (by rfl) (by rfl)
    component56Node15_sound component56Node16_sound

private noncomputable def component56Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (5/32), chiHi := (41/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node18_sound : Sound component56Node18Box :=
  sound_of_literal_split component56Node18Box leaf2643Box leaf2644Box
    .k (231/64) (by rfl) (by rfl)
    leaf2643FlatSound leaf2644FlatSound

private noncomputable def component56Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (41/256), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node19_sound : Sound component56Node19Box :=
  sound_of_literal_split component56Node19Box leaf2645Box leaf2646Box
    .k (231/64) (by rfl) (by rfl)
    leaf2645FlatSound leaf2646FlatSound

private noncomputable def component56Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node20_sound : Sound component56Node20Box :=
  sound_of_literal_split component56Node20Box component56Node18Box component56Node19Box
    .chi (41/256) (by rfl) (by rfl)
    component56Node18_sound component56Node19_sound

private noncomputable def component56Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node21_sound : Sound component56Node21Box :=
  sound_of_literal_split component56Node21Box component56Node17Box component56Node20Box
    .k (115/32) (by rfl) (by rfl)
    component56Node17_sound component56Node20_sound

private noncomputable def component56Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node22_sound : Sound component56Node22Box :=
  sound_of_literal_split component56Node22Box leaf2647Box leaf2648Box
    .k (229/64) (by rfl) (by rfl)
    leaf2647FlatSound leaf2648FlatSound

private noncomputable def component56Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node23_sound : Sound component56Node23Box :=
  sound_of_literal_split component56Node23Box leaf2649Box leaf2650Box
    .k (229/64) (by rfl) (by rfl)
    leaf2649FlatSound leaf2650FlatSound

private noncomputable def component56Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node24_sound : Sound component56Node24Box :=
  sound_of_literal_split component56Node24Box component56Node22Box component56Node23Box
    .chi (43/256) (by rfl) (by rfl)
    component56Node22_sound component56Node23_sound

private noncomputable def component56Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (21/128), chiHi := (43/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node25_sound : Sound component56Node25Box :=
  sound_of_literal_split component56Node25Box leaf2651Box leaf2652Box
    .k (231/64) (by rfl) (by rfl)
    leaf2651FlatSound leaf2652FlatSound

private noncomputable def component56Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (43/256), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node26_sound : Sound component56Node26Box :=
  sound_of_literal_split component56Node26Box leaf2653Box leaf2654Box
    .k (231/64) (by rfl) (by rfl)
    leaf2653FlatSound leaf2654FlatSound

private noncomputable def component56Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node27_sound : Sound component56Node27Box :=
  sound_of_literal_split component56Node27Box component56Node25Box component56Node26Box
    .chi (43/256) (by rfl) (by rfl)
    component56Node25_sound component56Node26_sound

private noncomputable def component56Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node28_sound : Sound component56Node28Box :=
  sound_of_literal_split component56Node28Box component56Node24Box component56Node27Box
    .k (115/32) (by rfl) (by rfl)
    component56Node24_sound component56Node27_sound

private noncomputable def component56Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node29_sound : Sound component56Node29Box :=
  sound_of_literal_split component56Node29Box component56Node21Box component56Node28Box
    .chi (21/128) (by rfl) (by rfl)
    component56Node21_sound component56Node28_sound

private noncomputable def component56Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component56Node30_sound : Sound component56Node30Box :=
  sound_of_literal_split component56Node30Box component56Node14Box component56Node29Box
    .k (57/16) (by rfl) (by rfl)
    component56Node14_sound component56Node29_sound

private noncomputable def component56Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node31_sound : Sound component56Node31Box :=
  sound_of_literal_split component56Node31Box leaf2655Box leaf2656Box
    .k (225/64) (by rfl) (by rfl)
    leaf2655FlatSound leaf2656FlatSound

private noncomputable def component56Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node32_sound : Sound component56Node32Box :=
  sound_of_literal_split component56Node32Box leaf2657Box leaf2658Box
    .k (225/64) (by rfl) (by rfl)
    leaf2657FlatSound leaf2658FlatSound

private noncomputable def component56Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node33_sound : Sound component56Node33Box :=
  sound_of_literal_split component56Node33Box component56Node31Box component56Node32Box
    .chi (45/256) (by rfl) (by rfl)
    component56Node31_sound component56Node32_sound

private noncomputable def component56Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node34_sound : Sound component56Node34Box :=
  sound_of_literal_split component56Node34Box leaf2659Box leaf2660Box
    .k (227/64) (by rfl) (by rfl)
    leaf2659FlatSound leaf2660FlatSound

private noncomputable def component56Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node35_sound : Sound component56Node35Box :=
  sound_of_literal_split component56Node35Box leaf2661Box leaf2662Box
    .k (227/64) (by rfl) (by rfl)
    leaf2661FlatSound leaf2662FlatSound

private noncomputable def component56Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node36_sound : Sound component56Node36Box :=
  sound_of_literal_split component56Node36Box component56Node34Box component56Node35Box
    .chi (45/256) (by rfl) (by rfl)
    component56Node34_sound component56Node35_sound

private noncomputable def component56Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node37_sound : Sound component56Node37Box :=
  sound_of_literal_split component56Node37Box component56Node33Box component56Node36Box
    .k (113/32) (by rfl) (by rfl)
    component56Node33_sound component56Node36_sound

private noncomputable def component56Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node38_sound : Sound component56Node38Box :=
  sound_of_literal_split component56Node38Box leaf2663Box leaf2664Box
    .k (225/64) (by rfl) (by rfl)
    leaf2663FlatSound leaf2664FlatSound

private noncomputable def component56Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node39_sound : Sound component56Node39Box :=
  sound_of_literal_split component56Node39Box leaf2665Box leaf2666Box
    .k (225/64) (by rfl) (by rfl)
    leaf2665FlatSound leaf2666FlatSound

private noncomputable def component56Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node40_sound : Sound component56Node40Box :=
  sound_of_literal_split component56Node40Box component56Node38Box component56Node39Box
    .chi (47/256) (by rfl) (by rfl)
    component56Node38_sound component56Node39_sound

private noncomputable def component56Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node41_sound : Sound component56Node41Box :=
  sound_of_literal_split component56Node41Box leaf2667Box leaf2668Box
    .k (227/64) (by rfl) (by rfl)
    leaf2667FlatSound leaf2668FlatSound

private noncomputable def component56Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node42_sound : Sound component56Node42Box :=
  sound_of_literal_split component56Node42Box leaf2669Box leaf2670Box
    .k (227/64) (by rfl) (by rfl)
    leaf2669FlatSound leaf2670FlatSound

private noncomputable def component56Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node43_sound : Sound component56Node43Box :=
  sound_of_literal_split component56Node43Box component56Node41Box component56Node42Box
    .chi (47/256) (by rfl) (by rfl)
    component56Node41_sound component56Node42_sound

private noncomputable def component56Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node44_sound : Sound component56Node44Box :=
  sound_of_literal_split component56Node44Box component56Node40Box component56Node43Box
    .k (113/32) (by rfl) (by rfl)
    component56Node40_sound component56Node43_sound

private noncomputable def component56Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node45_sound : Sound component56Node45Box :=
  sound_of_literal_split component56Node45Box component56Node37Box component56Node44Box
    .chi (23/128) (by rfl) (by rfl)
    component56Node37_sound component56Node44_sound

private noncomputable def component56Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node46_sound : Sound component56Node46Box :=
  sound_of_literal_split component56Node46Box leaf2671Box leaf2672Box
    .k (229/64) (by rfl) (by rfl)
    leaf2671FlatSound leaf2672FlatSound

private noncomputable def component56Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node47_sound : Sound component56Node47Box :=
  sound_of_literal_split component56Node47Box leaf2673Box leaf2674Box
    .k (229/64) (by rfl) (by rfl)
    leaf2673FlatSound leaf2674FlatSound

private noncomputable def component56Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node48_sound : Sound component56Node48Box :=
  sound_of_literal_split component56Node48Box component56Node46Box component56Node47Box
    .chi (45/256) (by rfl) (by rfl)
    component56Node46_sound component56Node47_sound

private noncomputable def component56Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (11/64), chiHi := (45/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node49_sound : Sound component56Node49Box :=
  sound_of_literal_split component56Node49Box leaf2675Box leaf2676Box
    .k (231/64) (by rfl) (by rfl)
    leaf2675FlatSound leaf2676FlatSound

private noncomputable def component56Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (45/256), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node50_sound : Sound component56Node50Box :=
  sound_of_literal_split component56Node50Box leaf2677Box leaf2678Box
    .k (231/64) (by rfl) (by rfl)
    leaf2677FlatSound leaf2678FlatSound

private noncomputable def component56Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node51_sound : Sound component56Node51Box :=
  sound_of_literal_split component56Node51Box component56Node49Box component56Node50Box
    .chi (45/256) (by rfl) (by rfl)
    component56Node49_sound component56Node50_sound

private noncomputable def component56Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component56Node52_sound : Sound component56Node52Box :=
  sound_of_literal_split component56Node52Box component56Node48Box component56Node51Box
    .k (115/32) (by rfl) (by rfl)
    component56Node48_sound component56Node51_sound

private noncomputable def component56Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node53_sound : Sound component56Node53Box :=
  sound_of_literal_split component56Node53Box leaf2679Box leaf2680Box
    .k (229/64) (by rfl) (by rfl)
    leaf2679FlatSound leaf2680FlatSound

private noncomputable def component56Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node54_sound : Sound component56Node54Box :=
  sound_of_literal_split component56Node54Box leaf2681Box leaf2682Box
    .k (229/64) (by rfl) (by rfl)
    leaf2681FlatSound leaf2682FlatSound

private noncomputable def component56Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node55_sound : Sound component56Node55Box :=
  sound_of_literal_split component56Node55Box component56Node53Box component56Node54Box
    .chi (47/256) (by rfl) (by rfl)
    component56Node53_sound component56Node54_sound

private noncomputable def component56Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (23/128), chiHi := (47/256) }

set_option maxRecDepth 1000000 in
private theorem component56Node56_sound : Sound component56Node56Box :=
  sound_of_literal_split component56Node56Box leaf2683Box leaf2684Box
    .k (231/64) (by rfl) (by rfl)
    leaf2683FlatSound leaf2684FlatSound

private noncomputable def component56Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (47/256), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node57_sound : Sound component56Node57Box :=
  sound_of_literal_split component56Node57Box leaf2685Box leaf2686Box
    .k (231/64) (by rfl) (by rfl)
    leaf2685FlatSound leaf2686FlatSound

private noncomputable def component56Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node58_sound : Sound component56Node58Box :=
  sound_of_literal_split component56Node58Box component56Node56Box component56Node57Box
    .chi (47/256) (by rfl) (by rfl)
    component56Node56_sound component56Node57_sound

private noncomputable def component56Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node59_sound : Sound component56Node59Box :=
  sound_of_literal_split component56Node59Box component56Node55Box component56Node58Box
    .k (115/32) (by rfl) (by rfl)
    component56Node55_sound component56Node58_sound

private noncomputable def component56Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node60_sound : Sound component56Node60Box :=
  sound_of_literal_split component56Node60Box component56Node52Box component56Node59Box
    .chi (23/128) (by rfl) (by rfl)
    component56Node52_sound component56Node59_sound

private noncomputable def component56Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component56Node61_sound : Sound component56Node61Box :=
  sound_of_literal_split component56Node61Box component56Node45Box component56Node60Box
    .k (57/16) (by rfl) (by rfl)
    component56Node45_sound component56Node60_sound

noncomputable def component56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component56_sound : Sound component56Box :=
  sound_of_literal_split component56Box component56Node30Box component56Node61Box
    .chi (11/64) (by rfl) (by rfl)
    component56Node30_sound component56Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
