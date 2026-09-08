import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
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

private noncomputable def leaf2352Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2352Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742355/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811169792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1753144303/1073741824) }, upper := { exponent := 0, mantissa := (27017/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623477077/91622339584) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2352InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2352LocalValidity :
    LeafFacts leaf2352Box leaf2352Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2352Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811169792) }) = true
      norm_num [leaf2352Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2352CertificateValid :
    WideCertificateValid leaf2352Box leaf2352Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi187ValidityFacts
    leaf2352LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2352CoverageChecked :
    coverageCheck (innerAD leaf2352Box) leaf2352InnerLog = true := by
  rfl'

private theorem leaf2352InnerLogValid :
    leaf2352InnerLog.Valid 8 (innerAD leaf2352Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2352CoverageChecked

private noncomputable def leaf2352InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2352InputLogOnePlusV_eq :
    leaf2352InputLogOnePlusV = outerEnclosure 24
      (leaf2352Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2352RoundedFacts : LeafRoundedFacts 8
    leaf2352Certificate.logOnePlusV leaf2352InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2352InputLogOnePlusV_eq }

private noncomputable def leaf2352Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2352InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2352LowerChecked :
    lowerCheck 24 leaf2352Box leaf2352Inputs = true := by
  rfl'

private theorem leaf2352CoversExact : CoversExact 8
    leaf2352Box leaf2352Certificate leaf2352InnerLog leaf2352Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2352RoundedFacts (by rfl)

private theorem leaf2352FlatSound : Sound leaf2352Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2352CertificateValid
    leaf2352InnerLogValid leaf2352CoversExact leaf2352LowerChecked

private noncomputable def leaf2353Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2353Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433484288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1756289837/1073741824) }, upper := { exponent := 0, mantissa := (13533/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870406143/274866968576) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2353InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2353LocalValidity :
    LeafFacts leaf2353Box leaf2353Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2353Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433484288) }) = true
      norm_num [leaf2353Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2353CertificateValid :
    WideCertificateValid leaf2353Box leaf2353Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi187ValidityFacts
    leaf2353LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2353CoverageChecked :
    coverageCheck (innerAD leaf2353Box) leaf2353InnerLog = true := by
  rfl'

private theorem leaf2353InnerLogValid :
    leaf2353InnerLog.Valid 8 (innerAD leaf2353Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2353CoverageChecked

private noncomputable def leaf2353InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2353InputLogOnePlusV_eq :
    leaf2353InputLogOnePlusV = outerEnclosure 24
      (leaf2353Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2353RoundedFacts : LeafRoundedFacts 8
    leaf2353Certificate.logOnePlusV leaf2353InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2353InputLogOnePlusV_eq }

private noncomputable def leaf2353Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2353InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2353LowerChecked :
    lowerCheck 24 leaf2353Box leaf2353Inputs = true := by
  rfl'

private theorem leaf2353CoversExact : CoversExact 8
    leaf2353Box leaf2353Certificate leaf2353InnerLog leaf2353Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2353RoundedFacts (by rfl)

private theorem leaf2353FlatSound : Sound leaf2353Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2353CertificateValid
    leaf2353InnerLogValid leaf2353CoversExact leaf2353LowerChecked

private noncomputable def leaf2354Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2354Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742357/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433398272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1767299213/1073741824) }, upper := { exponent := 0, mantissa := (13617/8192) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870320127/274866796544) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2354InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2354LocalValidity :
    LeafFacts leaf2354Box leaf2354Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2354Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433398272) }) = true
      norm_num [leaf2354Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2354CertificateValid :
    WideCertificateValid leaf2354Box leaf2354Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi188ValidityFacts
    leaf2354LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2354CoverageChecked :
    coverageCheck (innerAD leaf2354Box) leaf2354InnerLog = true := by
  rfl'

private theorem leaf2354InnerLogValid :
    leaf2354InnerLog.Valid 8 (innerAD leaf2354Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2354CoverageChecked

private noncomputable def leaf2354InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2354InputLogOnePlusV_eq :
    leaf2354InputLogOnePlusV = outerEnclosure 24
      (leaf2354Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2354RoundedFacts : LeafRoundedFacts 8
    leaf2354Certificate.logOnePlusV leaf2354InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2354InputLogOnePlusV_eq }

private noncomputable def leaf2354Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2354InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2354LowerChecked :
    lowerCheck 24 leaf2354Box leaf2354Inputs = true := by
  rfl'

private theorem leaf2354CoversExact : CoversExact 8
    leaf2354Box leaf2354Certificate leaf2354InnerLog leaf2354Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2354RoundedFacts (by rfl)

private theorem leaf2354FlatSound : Sound leaf2354Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2354CertificateValid
    leaf2354InnerLogValid leaf2354CoversExact leaf2354LowerChecked

private noncomputable def leaf2355Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2355Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811124224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1770510279/1073741824) }, upper := { exponent := 0, mantissa := (6821/4096) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623431509/91622248448) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2355InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2355LocalValidity :
    LeafFacts leaf2355Box leaf2355Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2355Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811124224) }) = true
      norm_num [leaf2355Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2355CertificateValid :
    WideCertificateValid leaf2355Box leaf2355Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi188ValidityFacts
    leaf2355LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2355CoverageChecked :
    coverageCheck (innerAD leaf2355Box) leaf2355InnerLog = true := by
  rfl'

private theorem leaf2355InnerLogValid :
    leaf2355InnerLog.Valid 8 (innerAD leaf2355Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2355CoverageChecked

private noncomputable def leaf2355InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2355InputLogOnePlusV_eq :
    leaf2355InputLogOnePlusV = outerEnclosure 24
      (leaf2355Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2355RoundedFacts : LeafRoundedFacts 8
    leaf2355Certificate.logOnePlusV leaf2355InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2355InputLogOnePlusV_eq }

private noncomputable def leaf2355Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2355InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2355LowerChecked :
    lowerCheck 24 leaf2355Box leaf2355Inputs = true := by
  rfl'

private theorem leaf2355CoversExact : CoversExact 8
    leaf2355Box leaf2355Certificate leaf2355InnerLog leaf2355Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2355RoundedFacts (by rfl)

private theorem leaf2355FlatSound : Sound leaf2355Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2355CertificateValid
    leaf2355InnerLogValid leaf2355CoversExact leaf2355LowerChecked

private noncomputable def leaf2356Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2356Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486691840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1759435371/1073741824) }, upper := { exponent := 0, mantissa := (27115/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974076211/54973383680) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2356InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2356LocalValidity :
    LeafFacts leaf2356Box leaf2356Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2356Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486691840) }) = true
      norm_num [leaf2356Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2356CertificateValid :
    WideCertificateValid leaf2356Box leaf2356Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi187ValidityFacts
    leaf2356LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2356CoverageChecked :
    coverageCheck (innerAD leaf2356Box) leaf2356InnerLog = true := by
  rfl'

private theorem leaf2356InnerLogValid :
    leaf2356InnerLog.Valid 8 (innerAD leaf2356Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2356CoverageChecked

private noncomputable def leaf2356InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2356InputLogOnePlusV_eq :
    leaf2356InputLogOnePlusV = outerEnclosure 24
      (leaf2356Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2356RoundedFacts : LeafRoundedFacts 8
    leaf2356Certificate.logOnePlusV leaf2356InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2356InputLogOnePlusV_eq }

private noncomputable def leaf2356Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2356InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2356LowerChecked :
    lowerCheck 24 leaf2356Box leaf2356Inputs = true := by
  rfl'

private theorem leaf2356CoversExact : CoversExact 8
    leaf2356Box leaf2356Certificate leaf2356InnerLog leaf2356Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2356RoundedFacts (by rfl)

private theorem leaf2356FlatSound : Sound leaf2356Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2356CertificateValid
    leaf2356InnerLogValid leaf2356CoversExact leaf2356LowerChecked

private noncomputable def leaf2357Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2357Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270381568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1762580905/1073741824) }, upper := { exponent := 0, mantissa := (6791/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541150663/30540763136) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2357InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2357LocalValidity :
    LeafFacts leaf2357Box leaf2357Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2357Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270381568) }) = true
      norm_num [leaf2357Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2357CertificateValid :
    WideCertificateValid leaf2357Box leaf2357Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi187ValidityFacts
    leaf2357LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2357CoverageChecked :
    coverageCheck (innerAD leaf2357Box) leaf2357InnerLog = true := by
  rfl'

private theorem leaf2357InnerLogValid :
    leaf2357InnerLog.Valid 8 (innerAD leaf2357Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2357CoverageChecked

private noncomputable def leaf2357InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2357InputLogOnePlusV_eq :
    leaf2357InputLogOnePlusV = outerEnclosure 24
      (leaf2357Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2357RoundedFacts : LeafRoundedFacts 8
    leaf2357Certificate.logOnePlusV leaf2357InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2357InputLogOnePlusV_eq }

private noncomputable def leaf2357Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2357InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2357LowerChecked :
    lowerCheck 24 leaf2357Box leaf2357Inputs = true := by
  rfl'

private theorem leaf2357CoversExact : CoversExact 8
    leaf2357Box leaf2357Certificate leaf2357InnerLog leaf2357Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2357RoundedFacts (by rfl)

private theorem leaf2357FlatSound : Sound leaf2357Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2357CertificateValid
    leaf2357InnerLogValid leaf2357CoversExact leaf2357LowerChecked

private noncomputable def leaf2358Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2358Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433347072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1773721345/1073741824) }, upper := { exponent := 0, mantissa := (13667/8192) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870268927/274866694144) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2358InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2358LocalValidity :
    LeafFacts leaf2358Box leaf2358Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2358Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433347072) }) = true
      norm_num [leaf2358Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2358CertificateValid :
    WideCertificateValid leaf2358Box leaf2358Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi188ValidityFacts
    leaf2358LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2358CoverageChecked :
    coverageCheck (innerAD leaf2358Box) leaf2358InnerLog = true := by
  rfl'

private theorem leaf2358InnerLogValid :
    leaf2358InnerLog.Valid 8 (innerAD leaf2358Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2358CoverageChecked

private noncomputable def leaf2358InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2358InputLogOnePlusV_eq :
    leaf2358InputLogOnePlusV = outerEnclosure 24
      (leaf2358Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2358RoundedFacts : LeafRoundedFacts 8
    leaf2358Certificate.logOnePlusV leaf2358InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2358InputLogOnePlusV_eq }

private noncomputable def leaf2358Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2358InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2358LowerChecked :
    lowerCheck 24 leaf2358Box leaf2358Inputs = true := by
  rfl'

private theorem leaf2358CoversExact : CoversExact 8
    leaf2358Box leaf2358Certificate leaf2358InnerLog leaf2358Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2358RoundedFacts (by rfl)

private theorem leaf2358FlatSound : Sound leaf2358Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2358CertificateValid
    leaf2358InnerLogValid leaf2358CoversExact leaf2358LowerChecked

private noncomputable def leaf2359Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2359Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433321472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1776932411/1073741824) }, upper := { exponent := 0, mantissa := (3423/2048) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870243327/274866642944) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2359InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2359LocalValidity :
    LeafFacts leaf2359Box leaf2359Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2359Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433321472) }) = true
      norm_num [leaf2359Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2359CertificateValid :
    WideCertificateValid leaf2359Box leaf2359Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi188ValidityFacts
    leaf2359LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2359CoverageChecked :
    coverageCheck (innerAD leaf2359Box) leaf2359InnerLog = true := by
  rfl'

private theorem leaf2359InnerLogValid :
    leaf2359InnerLog.Valid 8 (innerAD leaf2359Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2359CoverageChecked

private noncomputable def leaf2359InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2359InputLogOnePlusV_eq :
    leaf2359InputLogOnePlusV = outerEnclosure 24
      (leaf2359Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2359RoundedFacts : LeafRoundedFacts 8
    leaf2359Certificate.logOnePlusV leaf2359InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2359InputLogOnePlusV_eq }

private noncomputable def leaf2359Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2359InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2359LowerChecked :
    lowerCheck 24 leaf2359Box leaf2359Inputs = true := by
  rfl'

private theorem leaf2359CoversExact : CoversExact 8
    leaf2359Box leaf2359Certificate leaf2359InnerLog leaf2359Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2359RoundedFacts (by rfl)

private theorem leaf2359FlatSound : Sound leaf2359Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2359CertificateValid
    leaf2359InnerLogValid leaf2359CoversExact leaf2359LowerChecked

private noncomputable def leaf2360Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2360Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742359/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433287168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1781454123/1073741824) }, upper := { exponent := 0, mantissa := (27451/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870209023/274866574336) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2360InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2360LocalValidity :
    LeafFacts leaf2360Box leaf2360Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2360Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433287168) }) = true
      norm_num [leaf2360Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2360CertificateValid :
    WideCertificateValid leaf2360Box leaf2360Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi193ValidityFacts
    leaf2360LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2360CoverageChecked :
    coverageCheck (innerAD leaf2360Box) leaf2360InnerLog = true := by
  rfl'

private theorem leaf2360InnerLogValid :
    leaf2360InnerLog.Valid 8 (innerAD leaf2360Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2360CoverageChecked

private noncomputable def leaf2360InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2360InputLogOnePlusV_eq :
    leaf2360InputLogOnePlusV = outerEnclosure 24
      (leaf2360Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2360RoundedFacts : LeafRoundedFacts 8
    leaf2360Certificate.logOnePlusV leaf2360InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2360InputLogOnePlusV_eq }

private noncomputable def leaf2360Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi193InputQChi innerPair56Input
    leaf2360InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2360LowerChecked :
    lowerCheck 24 leaf2360Box leaf2360Inputs = true := by
  rfl'

private theorem leaf2360CoversExact : CoversExact 8
    leaf2360Box leaf2360Certificate leaf2360InnerLog leaf2360Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi193RoundedFacts
    innerPair56RoundedFacts leaf2360RoundedFacts (by rfl)

private theorem leaf2360FlatSound : Sound leaf2360Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2360CertificateValid
    leaf2360InnerLogValid leaf2360CoversExact leaf2360LowerChecked

private noncomputable def leaf2361Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2361Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (5090256365/5090117632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1795609033/1073741824) }, upper := { exponent := 0, mantissa := (6917/4096) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10180373997/10180235264) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2361InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2361LocalValidity :
    LeafFacts leaf2361Box leaf2361Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2361Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5090256365/5090117632) }) = true
      norm_num [leaf2361Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2361CertificateValid :
    WideCertificateValid leaf2361Box leaf2361Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi194ValidityFacts
    leaf2361LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2361CoverageChecked :
    coverageCheck (innerAD leaf2361Box) leaf2361InnerLog = true := by
  rfl'

private theorem leaf2361InnerLogValid :
    leaf2361InnerLog.Valid 8 (innerAD leaf2361Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2361CoverageChecked

private noncomputable def leaf2361InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2361InputLogOnePlusV_eq :
    leaf2361InputLogOnePlusV = outerEnclosure 24
      (leaf2361Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2361RoundedFacts : LeafRoundedFacts 8
    leaf2361Certificate.logOnePlusV leaf2361InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2361InputLogOnePlusV_eq }

private noncomputable def leaf2361Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi194InputQChi innerPair57Input
    leaf2361InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2361LowerChecked :
    lowerCheck 24 leaf2361Box leaf2361Inputs = true := by
  rfl'

private theorem leaf2361CoversExact : CoversExact 8
    leaf2361Box leaf2361Certificate leaf2361InnerLog leaf2361Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi194RoundedFacts
    innerPair57RoundedFacts leaf2361RoundedFacts (by rfl)

private theorem leaf2361FlatSound : Sound leaf2361Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2361CertificateValid
    leaf2361InnerLogValid leaf2361CoversExact leaf2361LowerChecked

private noncomputable def leaf2362Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2362Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742361/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433261056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1784730721/1073741824) }, upper := { exponent := 0, mantissa := (13751/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870182911/274866522112) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2362InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2362LocalValidity :
    LeafFacts leaf2362Box leaf2362Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2362Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433261056) }) = true
      norm_num [leaf2362Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2362CertificateValid :
    WideCertificateValid leaf2362Box leaf2362Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi193ValidityFacts
    leaf2362LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2362CoverageChecked :
    coverageCheck (innerAD leaf2362Box) leaf2362InnerLog = true := by
  rfl'

private theorem leaf2362InnerLogValid :
    leaf2362InnerLog.Valid 8 (innerAD leaf2362Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2362CoverageChecked

private noncomputable def leaf2362InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2362InputLogOnePlusV_eq :
    leaf2362InputLogOnePlusV = outerEnclosure 24
      (leaf2362Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2362RoundedFacts : LeafRoundedFacts 8
    leaf2362Certificate.logOnePlusV leaf2362InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2362InputLogOnePlusV_eq }

private noncomputable def leaf2362Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi193InputQChi innerPair56Input
    leaf2362InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2362LowerChecked :
    lowerCheck 24 leaf2362Box leaf2362Inputs = true := by
  rfl'

private theorem leaf2362CoversExact : CoversExact 8
    leaf2362Box leaf2362Certificate leaf2362InnerLog leaf2362Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi193RoundedFacts
    innerPair56RoundedFacts leaf2362RoundedFacts (by rfl)

private theorem leaf2362FlatSound : Sound leaf2362Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2362CertificateValid
    leaf2362InnerLogValid leaf2362CoversExact leaf2362LowerChecked

private noncomputable def leaf2363Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2363Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486629888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1798951163/1073741824) }, upper := { exponent := 0, mantissa := (3465/2048) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974014259/54973259776) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2363InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2363LocalValidity :
    LeafFacts leaf2363Box leaf2363Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2363Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486629888) }) = true
      norm_num [leaf2363Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2363CertificateValid :
    WideCertificateValid leaf2363Box leaf2363Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi194ValidityFacts
    leaf2363LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2363CoverageChecked :
    coverageCheck (innerAD leaf2363Box) leaf2363InnerLog = true := by
  rfl'

private theorem leaf2363InnerLogValid :
    leaf2363InnerLog.Valid 8 (innerAD leaf2363Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2363CoverageChecked

private noncomputable def leaf2363InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2363InputLogOnePlusV_eq :
    leaf2363InputLogOnePlusV = outerEnclosure 24
      (leaf2363Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2363RoundedFacts : LeafRoundedFacts 8
    leaf2363Certificate.logOnePlusV leaf2363InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2363InputLogOnePlusV_eq }

private noncomputable def leaf2363Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi194InputQChi innerPair57Input
    leaf2363InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2363LowerChecked :
    lowerCheck 24 leaf2363Box leaf2363Inputs = true := by
  rfl'

private theorem leaf2363CoversExact : CoversExact 8
    leaf2363Box leaf2363Certificate leaf2363InnerLog leaf2363Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi194RoundedFacts
    innerPair57RoundedFacts leaf2363RoundedFacts (by rfl)

private theorem leaf2363FlatSound : Sound leaf2363Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2363CertificateValid
    leaf2363InnerLogValid leaf2363CoversExact leaf2363LowerChecked

private noncomputable def leaf2364Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2364Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433234944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1788007319/1073741824) }, upper := { exponent := 0, mantissa := (27553/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870156799/274866469888) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2364InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2364LocalValidity :
    LeafFacts leaf2364Box leaf2364Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2364Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433234944) }) = true
      norm_num [leaf2364Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2364CertificateValid :
    WideCertificateValid leaf2364Box leaf2364Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi193ValidityFacts
    leaf2364LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2364CoverageChecked :
    coverageCheck (innerAD leaf2364Box) leaf2364InnerLog = true := by
  rfl'

private theorem leaf2364InnerLogValid :
    leaf2364InnerLog.Valid 8 (innerAD leaf2364Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2364CoverageChecked

private noncomputable def leaf2364InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2364InputLogOnePlusV_eq :
    leaf2364InputLogOnePlusV = outerEnclosure 24
      (leaf2364Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2364RoundedFacts : LeafRoundedFacts 8
    leaf2364Certificate.logOnePlusV leaf2364InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2364InputLogOnePlusV_eq }

private noncomputable def leaf2364Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi193InputQChi innerPair56Input
    leaf2364InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2364LowerChecked :
    lowerCheck 24 leaf2364Box leaf2364Inputs = true := by
  rfl'

private theorem leaf2364CoversExact : CoversExact 8
    leaf2364Box leaf2364Certificate leaf2364InnerLog leaf2364Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi193RoundedFacts
    innerPair56RoundedFacts leaf2364RoundedFacts (by rfl)

private theorem leaf2364FlatSound : Sound leaf2364Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2364CertificateValid
    leaf2364InnerLogValid leaf2364CoversExact leaf2364LowerChecked

private noncomputable def leaf2365Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2365Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433122816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1802293293/1073741824) }, upper := { exponent := 0, mantissa := (6943/4096) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870044671/274866245632) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2365InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2365LocalValidity :
    LeafFacts leaf2365Box leaf2365Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2365Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433122816) }) = true
      norm_num [leaf2365Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2365CertificateValid :
    WideCertificateValid leaf2365Box leaf2365Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi194ValidityFacts
    leaf2365LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2365CoverageChecked :
    coverageCheck (innerAD leaf2365Box) leaf2365InnerLog = true := by
  rfl'

private theorem leaf2365InnerLogValid :
    leaf2365InnerLog.Valid 8 (innerAD leaf2365Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2365CoverageChecked

private noncomputable def leaf2365InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2365InputLogOnePlusV_eq :
    leaf2365InputLogOnePlusV = outerEnclosure 24
      (leaf2365Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2365RoundedFacts : LeafRoundedFacts 8
    leaf2365Certificate.logOnePlusV leaf2365InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2365InputLogOnePlusV_eq }

private noncomputable def leaf2365Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi194InputQChi innerPair57Input
    leaf2365InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2365LowerChecked :
    lowerCheck 24 leaf2365Box leaf2365Inputs = true := by
  rfl'

private theorem leaf2365CoversExact : CoversExact 8
    leaf2365Box leaf2365Certificate leaf2365InnerLog leaf2365Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi194RoundedFacts
    innerPair57RoundedFacts leaf2365RoundedFacts (by rfl)

private theorem leaf2365FlatSound : Sound leaf2365Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2365CertificateValid
    leaf2365InnerLogValid leaf2365CoversExact leaf2365LowerChecked

private noncomputable def leaf2366Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2366Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433208832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1791283917/1073741824) }, upper := { exponent := 0, mantissa := (6901/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870130687/274866417664) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2366InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2366LocalValidity :
    LeafFacts leaf2366Box leaf2366Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2366Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433208832) }) = true
      norm_num [leaf2366Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2366CertificateValid :
    WideCertificateValid leaf2366Box leaf2366Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi193ValidityFacts
    leaf2366LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2366CoverageChecked :
    coverageCheck (innerAD leaf2366Box) leaf2366InnerLog = true := by
  rfl'

private theorem leaf2366InnerLogValid :
    leaf2366InnerLog.Valid 8 (innerAD leaf2366Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2366CoverageChecked

private noncomputable def leaf2366InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2366InputLogOnePlusV_eq :
    leaf2366InputLogOnePlusV = outerEnclosure 24
      (leaf2366Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2366RoundedFacts : LeafRoundedFacts 8
    leaf2366Certificate.logOnePlusV leaf2366InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2366InputLogOnePlusV_eq }

private noncomputable def leaf2366Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi193InputQChi innerPair56Input
    leaf2366InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2366LowerChecked :
    lowerCheck 24 leaf2366Box leaf2366Inputs = true := by
  rfl'

private theorem leaf2366CoversExact : CoversExact 8
    leaf2366Box leaf2366Certificate leaf2366InnerLog leaf2366Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi193RoundedFacts
    innerPair56RoundedFacts leaf2366RoundedFacts (by rfl)

private theorem leaf2366FlatSound : Sound leaf2366Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2366CertificateValid
    leaf2366InnerLogValid leaf2366CoversExact leaf2366LowerChecked

private noncomputable def leaf2367Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2367Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (2694841605/2694766592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1805635423/1073741824) }, upper := { exponent := 0, mantissa := (1739/1024) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5389608197/5389533184) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2367InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2367LocalValidity :
    LeafFacts leaf2367Box leaf2367Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2367Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2694841605/2694766592) }) = true
      norm_num [leaf2367Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2367CertificateValid :
    WideCertificateValid leaf2367Box leaf2367Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi194ValidityFacts
    leaf2367LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2367CoverageChecked :
    coverageCheck (innerAD leaf2367Box) leaf2367InnerLog = true := by
  rfl'

private theorem leaf2367InnerLogValid :
    leaf2367InnerLog.Valid 8 (innerAD leaf2367Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2367CoverageChecked

private noncomputable def leaf2367InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2367InputLogOnePlusV_eq :
    leaf2367InputLogOnePlusV = outerEnclosure 24
      (leaf2367Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2367RoundedFacts : LeafRoundedFacts 8
    leaf2367Certificate.logOnePlusV leaf2367InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2367InputLogOnePlusV_eq }

private noncomputable def leaf2367Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi194InputQChi innerPair57Input
    leaf2367InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2367LowerChecked :
    lowerCheck 24 leaf2367Box leaf2367Inputs = true := by
  rfl'

private theorem leaf2367CoversExact : CoversExact 8
    leaf2367Box leaf2367Certificate leaf2367InnerLog leaf2367Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi194RoundedFacts
    innerPair57RoundedFacts leaf2367RoundedFacts (by rfl)

private theorem leaf2367FlatSound : Sound leaf2367Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2367CertificateValid
    leaf2367InnerLogValid leaf2367CoversExact leaf2367LowerChecked

private noncomputable def leaf2368Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2368Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433409024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1765726439/1073741824) }, upper := { exponent := 0, mantissa := (27213/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870330879/274866818048) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2368InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2368LocalValidity :
    LeafFacts leaf2368Box leaf2368Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2368Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433409024) }) = true
      norm_num [leaf2368Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2368CertificateValid :
    WideCertificateValid leaf2368Box leaf2368Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi187ValidityFacts
    leaf2368LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2368CoverageChecked :
    coverageCheck (innerAD leaf2368Box) leaf2368InnerLog = true := by
  rfl'

private theorem leaf2368InnerLogValid :
    leaf2368InnerLog.Valid 8 (innerAD leaf2368Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2368CoverageChecked

private noncomputable def leaf2368InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2368InputLogOnePlusV_eq :
    leaf2368InputLogOnePlusV = outerEnclosure 24
      (leaf2368Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2368RoundedFacts : LeafRoundedFacts 8
    leaf2368Certificate.logOnePlusV leaf2368InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2368InputLogOnePlusV_eq }

private noncomputable def leaf2368Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2368InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2368LowerChecked :
    lowerCheck 24 leaf2368Box leaf2368Inputs = true := by
  rfl'

private theorem leaf2368CoversExact : CoversExact 8
    leaf2368Box leaf2368Certificate leaf2368InnerLog leaf2368Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2368RoundedFacts (by rfl)

private theorem leaf2368FlatSound : Sound leaf2368Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2368CertificateValid
    leaf2368InnerLogValid leaf2368CoversExact leaf2368LowerChecked

private noncomputable def leaf2369Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2369Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433383936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1768871973/1073741824) }, upper := { exponent := 0, mantissa := (13631/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870305791/274866767872) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2369InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2369LocalValidity :
    LeafFacts leaf2369Box leaf2369Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2369Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433383936) }) = true
      norm_num [leaf2369Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2369CertificateValid :
    WideCertificateValid leaf2369Box leaf2369Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi187ValidityFacts
    leaf2369LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2369CoverageChecked :
    coverageCheck (innerAD leaf2369Box) leaf2369InnerLog = true := by
  rfl'

private theorem leaf2369InnerLogValid :
    leaf2369InnerLog.Valid 8 (innerAD leaf2369Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2369CoverageChecked

private noncomputable def leaf2369InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2369InputLogOnePlusV_eq :
    leaf2369InputLogOnePlusV = outerEnclosure 24
      (leaf2369Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2369RoundedFacts : LeafRoundedFacts 8
    leaf2369Certificate.logOnePlusV leaf2369InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2369InputLogOnePlusV_eq }

private noncomputable def leaf2369Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2369InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2369LowerChecked :
    lowerCheck 24 leaf2369Box leaf2369Inputs = true := by
  rfl'

private theorem leaf2369CoversExact : CoversExact 8
    leaf2369Box leaf2369Certificate leaf2369InnerLog leaf2369Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2369RoundedFacts (by rfl)

private theorem leaf2369FlatSound : Sound leaf2369Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2369CertificateValid
    leaf2369InnerLogValid leaf2369CoversExact leaf2369LowerChecked

private noncomputable def leaf2370Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2370Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270366208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1780143477/1073741824) }, upper := { exponent := 0, mantissa := (13717/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541135303/30540732416) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2370InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2370LocalValidity :
    LeafFacts leaf2370Box leaf2370Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2370Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270366208) }) = true
      norm_num [leaf2370Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2370CertificateValid :
    WideCertificateValid leaf2370Box leaf2370Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi188ValidityFacts
    leaf2370LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2370CoverageChecked :
    coverageCheck (innerAD leaf2370Box) leaf2370InnerLog = true := by
  rfl'

private theorem leaf2370InnerLogValid :
    leaf2370InnerLog.Valid 8 (innerAD leaf2370Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2370CoverageChecked

private noncomputable def leaf2370InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2370InputLogOnePlusV_eq :
    leaf2370InputLogOnePlusV = outerEnclosure 24
      (leaf2370Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2370RoundedFacts : LeafRoundedFacts 8
    leaf2370Certificate.logOnePlusV leaf2370InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2370InputLogOnePlusV_eq }

private noncomputable def leaf2370Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2370InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2370LowerChecked :
    lowerCheck 24 leaf2370Box leaf2370Inputs = true := by
  rfl'

private theorem leaf2370CoversExact : CoversExact 8
    leaf2370Box leaf2370Certificate leaf2370InnerLog leaf2370Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2370RoundedFacts (by rfl)

private theorem leaf2370FlatSound : Sound leaf2370Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2370CertificateValid
    leaf2370InnerLogValid leaf2370CoversExact leaf2370LowerChecked

private noncomputable def leaf2371Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2371Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084310016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1783354543/1073741824) }, upper := { exponent := 0, mantissa := (6871/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168834831/16168620032) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2371InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2371LocalValidity :
    LeafFacts leaf2371Box leaf2371Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2371Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084310016) }) = true
      norm_num [leaf2371Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2371CertificateValid :
    WideCertificateValid leaf2371Box leaf2371Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi188ValidityFacts
    leaf2371LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2371CoverageChecked :
    coverageCheck (innerAD leaf2371Box) leaf2371InnerLog = true := by
  rfl'

private theorem leaf2371InnerLogValid :
    leaf2371InnerLog.Valid 8 (innerAD leaf2371Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2371CoverageChecked

private noncomputable def leaf2371InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2371InputLogOnePlusV_eq :
    leaf2371InputLogOnePlusV = outerEnclosure 24
      (leaf2371Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2371RoundedFacts : LeafRoundedFacts 8
    leaf2371Certificate.logOnePlusV leaf2371InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2371InputLogOnePlusV_eq }

private noncomputable def leaf2371Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2371InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2371LowerChecked :
    lowerCheck 24 leaf2371Box leaf2371Inputs = true := by
  rfl'

private theorem leaf2371CoversExact : CoversExact 8
    leaf2371Box leaf2371Certificate leaf2371InnerLog leaf2371Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2371RoundedFacts (by rfl)

private theorem leaf2371FlatSound : Sound leaf2371Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2371CertificateValid
    leaf2371InnerLogValid leaf2371CoversExact leaf2371LowerChecked

private noncomputable def leaf2372Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2372Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45811119616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1772017507/1073741824) }, upper := { exponent := 0, mantissa := (27311/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623426901/91622239232) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2372InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2372LocalValidity :
    LeafFacts leaf2372Box leaf2372Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2372Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45811119616) }) = true
      norm_num [leaf2372Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2372CertificateValid :
    WideCertificateValid leaf2372Box leaf2372Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi187ValidityFacts
    leaf2372LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2372CoverageChecked :
    coverageCheck (innerAD leaf2372Box) leaf2372InnerLog = true := by
  rfl'

private theorem leaf2372InnerLogValid :
    leaf2372InnerLog.Valid 8 (innerAD leaf2372Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2372CoverageChecked

private noncomputable def leaf2372InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2372InputLogOnePlusV_eq :
    leaf2372InputLogOnePlusV = outerEnclosure 24
      (leaf2372Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2372RoundedFacts : LeafRoundedFacts 8
    leaf2372Certificate.logOnePlusV leaf2372InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2372InputLogOnePlusV_eq }

private noncomputable def leaf2372Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2372InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2372LowerChecked :
    lowerCheck 24 leaf2372Box leaf2372Inputs = true := by
  rfl'

private theorem leaf2372CoversExact : CoversExact 8
    leaf2372Box leaf2372Certificate leaf2372InnerLog leaf2372Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2372RoundedFacts (by rfl)

private theorem leaf2372FlatSound : Sound leaf2372Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2372CertificateValid
    leaf2372InnerLogValid leaf2372CoversExact leaf2372LowerChecked

private noncomputable def leaf2373Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf2373Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486666752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1775163041/1073741824) }, upper := { exponent := 0, mantissa := (855/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974051123/54973333504) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2373InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2373LocalValidity :
    LeafFacts leaf2373Box leaf2373Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2373Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486666752) }) = true
      norm_num [leaf2373Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2373CertificateValid :
    WideCertificateValid leaf2373Box leaf2373Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi187ValidityFacts
    leaf2373LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2373CoverageChecked :
    coverageCheck (innerAD leaf2373Box) leaf2373InnerLog = true := by
  rfl'

private theorem leaf2373InnerLogValid :
    leaf2373InnerLog.Valid 8 (innerAD leaf2373Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2373CoverageChecked

private noncomputable def leaf2373InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2373InputLogOnePlusV_eq :
    leaf2373InputLogOnePlusV = outerEnclosure 24
      (leaf2373Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2373RoundedFacts : LeafRoundedFacts 8
    leaf2373Certificate.logOnePlusV leaf2373InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2373InputLogOnePlusV_eq }

private noncomputable def leaf2373Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi187InputQChi innerPair56Input
    leaf2373InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2373LowerChecked :
    lowerCheck 24 leaf2373Box leaf2373Inputs = true := by
  rfl'

private theorem leaf2373CoversExact : CoversExact 8
    leaf2373Box leaf2373Certificate leaf2373InnerLog leaf2373Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi187RoundedFacts
    innerPair56RoundedFacts leaf2373RoundedFacts (by rfl)

private theorem leaf2373FlatSound : Sound leaf2373Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2373CertificateValid
    leaf2373InnerLogValid leaf2373CoversExact leaf2373LowerChecked

private noncomputable def leaf2374Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2374Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433244672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1786565609/1073741824) }, upper := { exponent := 0, mantissa := (13767/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870166527/274866489344) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2374InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2374LocalValidity :
    LeafFacts leaf2374Box leaf2374Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2374Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433244672) }) = true
      norm_num [leaf2374Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2374CertificateValid :
    WideCertificateValid leaf2374Box leaf2374Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi188ValidityFacts
    leaf2374LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2374CoverageChecked :
    coverageCheck (innerAD leaf2374Box) leaf2374InnerLog = true := by
  rfl'

private theorem leaf2374InnerLogValid :
    leaf2374InnerLog.Valid 8 (innerAD leaf2374Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2374CoverageChecked

private noncomputable def leaf2374InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2374InputLogOnePlusV_eq :
    leaf2374InputLogOnePlusV = outerEnclosure 24
      (leaf2374Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2374RoundedFacts : LeafRoundedFacts 8
    leaf2374Certificate.logOnePlusV leaf2374InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2374InputLogOnePlusV_eq }

private noncomputable def leaf2374Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2374InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2374LowerChecked :
    lowerCheck 24 leaf2374Box leaf2374Inputs = true := by
  rfl'

private theorem leaf2374CoversExact : CoversExact 8
    leaf2374Box leaf2374Certificate leaf2374InnerLog leaf2374Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2374RoundedFacts (by rfl)

private theorem leaf2374FlatSound : Sound leaf2374Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2374CertificateValid
    leaf2374InnerLogValid leaf2374CoversExact leaf2374LowerChecked

private noncomputable def leaf2375Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf2375Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811073024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1789776675/1073741824) }, upper := { exponent := 0, mantissa := (431/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623380309/91622146048) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2375InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf2375LocalValidity :
    LeafFacts leaf2375Box leaf2375Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2375Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811073024) }) = true
      norm_num [leaf2375Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2375CertificateValid :
    WideCertificateValid leaf2375Box leaf2375Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi188ValidityFacts
    leaf2375LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2375CoverageChecked :
    coverageCheck (innerAD leaf2375Box) leaf2375InnerLog = true := by
  rfl'

private theorem leaf2375InnerLogValid :
    leaf2375InnerLog.Valid 8 (innerAD leaf2375Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf2375CoverageChecked

private noncomputable def leaf2375InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2375InputLogOnePlusV_eq :
    leaf2375InputLogOnePlusV = outerEnclosure 24
      (leaf2375Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2375RoundedFacts : LeafRoundedFacts 8
    leaf2375Certificate.logOnePlusV leaf2375InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2375InputLogOnePlusV_eq }

private noncomputable def leaf2375Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi188InputQChi innerPair56Input
    leaf2375InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2375LowerChecked :
    lowerCheck 24 leaf2375Box leaf2375Inputs = true := by
  rfl'

private theorem leaf2375CoversExact : CoversExact 8
    leaf2375Box leaf2375Certificate leaf2375InnerLog leaf2375Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi188RoundedFacts
    innerPair56RoundedFacts leaf2375RoundedFacts (by rfl)

private theorem leaf2375FlatSound : Sound leaf2375Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2375CertificateValid
    leaf2375InnerLogValid leaf2375CoversExact leaf2375LowerChecked

private noncomputable def leaf2376Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2376Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486636544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1794560515/1073741824) }, upper := { exponent := 0, mantissa := (27655/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54974020915/54973273088) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2376InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2376LocalValidity :
    LeafFacts leaf2376Box leaf2376Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2376Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486636544) }) = true
      norm_num [leaf2376Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2376CertificateValid :
    WideCertificateValid leaf2376Box leaf2376Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi193ValidityFacts
    leaf2376LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2376CoverageChecked :
    coverageCheck (innerAD leaf2376Box) leaf2376InnerLog = true := by
  rfl'

private theorem leaf2376InnerLogValid :
    leaf2376InnerLog.Valid 8 (innerAD leaf2376Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2376CoverageChecked

private noncomputable def leaf2376InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2376InputLogOnePlusV_eq :
    leaf2376InputLogOnePlusV = outerEnclosure 24
      (leaf2376Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2376RoundedFacts : LeafRoundedFacts 8
    leaf2376Certificate.logOnePlusV leaf2376InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2376InputLogOnePlusV_eq }

private noncomputable def leaf2376Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi193InputQChi innerPair57Input
    leaf2376InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2376LowerChecked :
    lowerCheck 24 leaf2376Box leaf2376Inputs = true := by
  rfl'

private theorem leaf2376CoversExact : CoversExact 8
    leaf2376Box leaf2376Certificate leaf2376InnerLog leaf2376Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi193RoundedFacts
    innerPair57RoundedFacts leaf2376RoundedFacts (by rfl)

private theorem leaf2376FlatSound : Sound leaf2376Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2376CertificateValid
    leaf2376InnerLogValid leaf2376CoversExact leaf2376LowerChecked

private noncomputable def leaf2377Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2377Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433069568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1808977553/1073741824) }, upper := { exponent := 0, mantissa := (6969/4096) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869991423/274866139136) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2377InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2377LocalValidity :
    LeafFacts leaf2377Box leaf2377Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2377Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433069568) }) = true
      norm_num [leaf2377Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2377CertificateValid :
    WideCertificateValid leaf2377Box leaf2377Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi194ValidityFacts
    leaf2377LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2377CoverageChecked :
    coverageCheck (innerAD leaf2377Box) leaf2377InnerLog = true := by
  rfl'

private theorem leaf2377InnerLogValid :
    leaf2377InnerLog.Valid 8 (innerAD leaf2377Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2377CoverageChecked

private noncomputable def leaf2377InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2377InputLogOnePlusV_eq :
    leaf2377InputLogOnePlusV = outerEnclosure 24
      (leaf2377Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2377RoundedFacts : LeafRoundedFacts 8
    leaf2377Certificate.logOnePlusV leaf2377InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2377InputLogOnePlusV_eq }

private noncomputable def leaf2377Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi194InputQChi innerPair57Input
    leaf2377InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2377LowerChecked :
    lowerCheck 24 leaf2377Box leaf2377Inputs = true := by
  rfl'

private theorem leaf2377CoversExact : CoversExact 8
    leaf2377Box leaf2377Certificate leaf2377InnerLog leaf2377Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi194RoundedFacts
    innerPair57RoundedFacts leaf2377RoundedFacts (by rfl)

private theorem leaf2377FlatSound : Sound leaf2377Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2377CertificateValid
    leaf2377InnerLogValid leaf2377CoversExact leaf2377LowerChecked

private noncomputable def leaf2378Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2378Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433156608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1797837113/1073741824) }, upper := { exponent := 0, mantissa := (13853/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870078463/274866313216) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2378InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2378LocalValidity :
    LeafFacts leaf2378Box leaf2378Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2378Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433156608) }) = true
      norm_num [leaf2378Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2378CertificateValid :
    WideCertificateValid leaf2378Box leaf2378Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi193ValidityFacts
    leaf2378LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2378CoverageChecked :
    coverageCheck (innerAD leaf2378Box) leaf2378InnerLog = true := by
  rfl'

private theorem leaf2378InnerLogValid :
    leaf2378InnerLog.Valid 8 (innerAD leaf2378Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2378CoverageChecked

private noncomputable def leaf2378InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2378InputLogOnePlusV_eq :
    leaf2378InputLogOnePlusV = outerEnclosure 24
      (leaf2378Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2378RoundedFacts : LeafRoundedFacts 8
    leaf2378Certificate.logOnePlusV leaf2378InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2378InputLogOnePlusV_eq }

private noncomputable def leaf2378Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi193InputQChi innerPair57Input
    leaf2378InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2378LowerChecked :
    lowerCheck 24 leaf2378Box leaf2378Inputs = true := by
  rfl'

private theorem leaf2378CoversExact : CoversExact 8
    leaf2378Box leaf2378Certificate leaf2378InnerLog leaf2378Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi193RoundedFacts
    innerPair57RoundedFacts leaf2378RoundedFacts (by rfl)

private theorem leaf2378FlatSound : Sound leaf2378Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2378CertificateValid
    leaf2378InnerLogValid leaf2378CoversExact leaf2378LowerChecked

private noncomputable def leaf2379Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2379Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433042944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1812319683/1073741824) }, upper := { exponent := 0, mantissa := (3491/2048) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869964799/274866085888) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2379InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2379LocalValidity :
    LeafFacts leaf2379Box leaf2379Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2379Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433042944) }) = true
      norm_num [leaf2379Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2379CertificateValid :
    WideCertificateValid leaf2379Box leaf2379Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi194ValidityFacts
    leaf2379LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2379CoverageChecked :
    coverageCheck (innerAD leaf2379Box) leaf2379InnerLog = true := by
  rfl'

private theorem leaf2379InnerLogValid :
    leaf2379InnerLog.Valid 8 (innerAD leaf2379Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2379CoverageChecked

private noncomputable def leaf2379InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2379InputLogOnePlusV_eq :
    leaf2379InputLogOnePlusV = outerEnclosure 24
      (leaf2379Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2379RoundedFacts : LeafRoundedFacts 8
    leaf2379Certificate.logOnePlusV leaf2379InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2379InputLogOnePlusV_eq }

private noncomputable def leaf2379Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi194InputQChi innerPair64Input
    leaf2379InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2379LowerChecked :
    lowerCheck 24 leaf2379Box leaf2379Inputs = true := by
  rfl'

private theorem leaf2379CoversExact : CoversExact 8
    leaf2379Box leaf2379Certificate leaf2379InnerLog leaf2379Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf2379RoundedFacts (by rfl)

private theorem leaf2379FlatSound : Sound leaf2379Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2379CertificateValid
    leaf2379InnerLogValid leaf2379CoversExact leaf2379LowerChecked

private noncomputable def leaf2380Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2380Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433130496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1801113711/1073741824) }, upper := { exponent := 0, mantissa := (27757/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870052351/274866260992) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2380InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2380LocalValidity :
    LeafFacts leaf2380Box leaf2380Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2380Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433130496) }) = true
      norm_num [leaf2380Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2380CertificateValid :
    WideCertificateValid leaf2380Box leaf2380Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi193ValidityFacts
    leaf2380LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2380CoverageChecked :
    coverageCheck (innerAD leaf2380Box) leaf2380InnerLog = true := by
  rfl'

private theorem leaf2380InnerLogValid :
    leaf2380InnerLog.Valid 8 (innerAD leaf2380Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2380CoverageChecked

private noncomputable def leaf2380InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf2380InputLogOnePlusV_eq :
    leaf2380InputLogOnePlusV = outerEnclosure 24
      (leaf2380Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2380RoundedFacts : LeafRoundedFacts 8
    leaf2380Certificate.logOnePlusV leaf2380InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2380InputLogOnePlusV_eq }

private noncomputable def leaf2380Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi193InputQChi innerPair57Input
    leaf2380InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2380LowerChecked :
    lowerCheck 24 leaf2380Box leaf2380Inputs = true := by
  rfl'

private theorem leaf2380CoversExact : CoversExact 8
    leaf2380Box leaf2380Certificate leaf2380InnerLog leaf2380Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi193RoundedFacts
    innerPair57RoundedFacts leaf2380RoundedFacts (by rfl)

private theorem leaf2380FlatSound : Sound leaf2380Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2380CertificateValid
    leaf2380InnerLogValid leaf2380CoversExact leaf2380LowerChecked

private noncomputable def leaf2381Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2381Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162201088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1815661813/1073741824) }, upper := { exponent := 0, mantissa := (6995/4096) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324662545/18324402176) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2381InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2381LocalValidity :
    LeafFacts leaf2381Box leaf2381Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2381Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162201088) }) = true
      norm_num [leaf2381Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2381CertificateValid :
    WideCertificateValid leaf2381Box leaf2381Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi194ValidityFacts
    leaf2381LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2381CoverageChecked :
    coverageCheck (innerAD leaf2381Box) leaf2381InnerLog = true := by
  rfl'

private theorem leaf2381InnerLogValid :
    leaf2381InnerLog.Valid 8 (innerAD leaf2381Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2381CoverageChecked

private noncomputable def leaf2381InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2381InputLogOnePlusV_eq :
    leaf2381InputLogOnePlusV = outerEnclosure 24
      (leaf2381Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2381RoundedFacts : LeafRoundedFacts 8
    leaf2381Certificate.logOnePlusV leaf2381InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2381InputLogOnePlusV_eq }

private noncomputable def leaf2381Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi194InputQChi innerPair64Input
    leaf2381InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2381LowerChecked :
    lowerCheck 24 leaf2381Box leaf2381Inputs = true := by
  rfl'

private theorem leaf2381CoversExact : CoversExact 8
    leaf2381Box leaf2381Certificate leaf2381InnerLog leaf2381Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf2381RoundedFacts (by rfl)

private theorem leaf2381FlatSound : Sound leaf2381Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2381CertificateValid
    leaf2381InnerLogValid leaf2381CoversExact leaf2381LowerChecked

private noncomputable def leaf2382Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf2382Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433104384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1804390309/1073741824) }, upper := { exponent := 0, mantissa := (869/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870026239/274866208768) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2382InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2382LocalValidity :
    LeafFacts leaf2382Box leaf2382Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2382Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433104384) }) = true
      norm_num [leaf2382Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2382CertificateValid :
    WideCertificateValid leaf2382Box leaf2382Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi193ValidityFacts
    leaf2382LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2382CoverageChecked :
    coverageCheck (innerAD leaf2382Box) leaf2382InnerLog = true := by
  rfl'

private theorem leaf2382InnerLogValid :
    leaf2382InnerLog.Valid 8 (innerAD leaf2382Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2382CoverageChecked

private noncomputable def leaf2382InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2382InputLogOnePlusV_eq :
    leaf2382InputLogOnePlusV = outerEnclosure 24
      (leaf2382Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2382RoundedFacts : LeafRoundedFacts 8
    leaf2382Certificate.logOnePlusV leaf2382InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2382InputLogOnePlusV_eq }

private noncomputable def leaf2382Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi193InputQChi innerPair57Input
    leaf2382InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2382LowerChecked :
    lowerCheck 24 leaf2382Box leaf2382Inputs = true := by
  rfl'

private theorem leaf2382CoversExact : CoversExact 8
    leaf2382Box leaf2382Certificate leaf2382InnerLog leaf2382Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi193RoundedFacts
    innerPair57RoundedFacts leaf2382RoundedFacts (by rfl)

private theorem leaf2382FlatSound : Sound leaf2382Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2382CertificateValid
    leaf2382InnerLogValid leaf2382CoversExact leaf2382LowerChecked

private noncomputable def leaf2383Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf2383Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432989696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1819003943/1073741824) }, upper := { exponent := 0, mantissa := (219/128) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869911551/274865979392) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2383InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2383LocalValidity :
    LeafFacts leaf2383Box leaf2383Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2383Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432989696) }) = true
      norm_num [leaf2383Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2383CertificateValid :
    WideCertificateValid leaf2383Box leaf2383Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi194ValidityFacts
    leaf2383LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2383CoverageChecked :
    coverageCheck (innerAD leaf2383Box) leaf2383InnerLog = true := by
  rfl'

private theorem leaf2383InnerLogValid :
    leaf2383InnerLog.Valid 8 (innerAD leaf2383Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2383CoverageChecked

private noncomputable def leaf2383InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2383InputLogOnePlusV_eq :
    leaf2383InputLogOnePlusV = outerEnclosure 24
      (leaf2383Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2383RoundedFacts : LeafRoundedFacts 8
    leaf2383Certificate.logOnePlusV leaf2383InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2383InputLogOnePlusV_eq }

private noncomputable def leaf2383Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi194InputQChi innerPair64Input
    leaf2383InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2383LowerChecked :
    lowerCheck 24 leaf2383Box leaf2383Inputs = true := by
  rfl'

private theorem leaf2383CoversExact : CoversExact 8
    leaf2383Box leaf2383Certificate leaf2383InnerLog leaf2383Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi194RoundedFacts
    innerPair64RoundedFacts leaf2383RoundedFacts (by rfl)

private theorem leaf2383FlatSound : Sound leaf2383Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2383CertificateValid
    leaf2383InnerLogValid leaf2383CoversExact leaf2383LowerChecked

private noncomputable def leaf2384Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2384Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742363/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486612992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1809763943/1073741824) }, upper := { exponent := 0, mantissa := (27885/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973997363/54973225984) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2384InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf2384LocalValidity :
    LeafFacts leaf2384Box leaf2384Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2384Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486612992) }) = true
      norm_num [leaf2384Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2384CertificateValid :
    WideCertificateValid leaf2384Box leaf2384Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi195ValidityFacts
    leaf2384LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2384CoverageChecked :
    coverageCheck (innerAD leaf2384Box) leaf2384InnerLog = true := by
  rfl'

private theorem leaf2384InnerLogValid :
    leaf2384InnerLog.Valid 8 (innerAD leaf2384Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf2384CoverageChecked

private noncomputable def leaf2384InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2384InputLogOnePlusV_eq :
    leaf2384InputLogOnePlusV = outerEnclosure 24
      (leaf2384Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2384RoundedFacts : LeafRoundedFacts 8
    leaf2384Certificate.logOnePlusV leaf2384InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2384InputLogOnePlusV_eq }

private noncomputable def leaf2384Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi195InputQChi innerPair57Input
    leaf2384InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2384LowerChecked :
    lowerCheck 24 leaf2384Box leaf2384Inputs = true := by
  rfl'

private theorem leaf2384CoversExact : CoversExact 8
    leaf2384Box leaf2384Certificate leaf2384InnerLog leaf2384Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi195RoundedFacts
    innerPair57RoundedFacts leaf2384RoundedFacts (by rfl)

private theorem leaf2384FlatSound : Sound leaf2384Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2384CertificateValid
    leaf2384InnerLogValid leaf2384CoversExact leaf2384LowerChecked

private noncomputable def leaf2385Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2385Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432953856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1823918853/1073741824) }, upper := { exponent := 0, mantissa := (14051/8192) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869875711/274865907712) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2385InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2385LocalValidity :
    LeafFacts leaf2385Box leaf2385Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2385Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432953856) }) = true
      norm_num [leaf2385Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2385CertificateValid :
    WideCertificateValid leaf2385Box leaf2385Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi196ValidityFacts
    leaf2385LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2385CoverageChecked :
    coverageCheck (innerAD leaf2385Box) leaf2385InnerLog = true := by
  rfl'

private theorem leaf2385InnerLogValid :
    leaf2385InnerLog.Valid 8 (innerAD leaf2385Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2385CoverageChecked

private noncomputable def leaf2385InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2385InputLogOnePlusV_eq :
    leaf2385InputLogOnePlusV = outerEnclosure 24
      (leaf2385Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2385RoundedFacts : LeafRoundedFacts 8
    leaf2385Certificate.logOnePlusV leaf2385InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2385InputLogOnePlusV_eq }

private noncomputable def leaf2385Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2385InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2385LowerChecked :
    lowerCheck 24 leaf2385Box leaf2385Inputs = true := by
  rfl'

private theorem leaf2385CoversExact : CoversExact 8
    leaf2385Box leaf2385Certificate leaf2385InnerLog leaf2385Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2385RoundedFacts (by rfl)

private theorem leaf2385FlatSound : Sound leaf2385Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2385CertificateValid
    leaf2385InnerLogValid leaf2385CoversExact leaf2385LowerChecked

private noncomputable def leaf2386Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2386Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742365/1073741824) }, vSqrt := { lower := (65529/65536), upper := (5090256365/5090112512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1813171605/1073741824) }, upper := { exponent := 0, mantissa := (13969/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10180368877/10180225024) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2386InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2386LocalValidity :
    LeafFacts leaf2386Box leaf2386Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2386Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5090256365/5090112512) }) = true
      norm_num [leaf2386Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2386CertificateValid :
    WideCertificateValid leaf2386Box leaf2386Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi195ValidityFacts
    leaf2386LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2386CoverageChecked :
    coverageCheck (innerAD leaf2386Box) leaf2386InnerLog = true := by
  rfl'

private theorem leaf2386InnerLogValid :
    leaf2386InnerLog.Valid 8 (innerAD leaf2386Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2386CoverageChecked

private noncomputable def leaf2386InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2386InputLogOnePlusV_eq :
    leaf2386InputLogOnePlusV = outerEnclosure 24
      (leaf2386Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2386RoundedFacts : LeafRoundedFacts 8
    leaf2386Certificate.logOnePlusV leaf2386InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2386InputLogOnePlusV_eq }

private noncomputable def leaf2386Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi195InputQChi innerPair64Input
    leaf2386InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2386LowerChecked :
    lowerCheck 24 leaf2386Box leaf2386Inputs = true := by
  rfl'

private theorem leaf2386CoversExact : CoversExact 8
    leaf2386Box leaf2386Certificate leaf2386InnerLog leaf2386Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf2386RoundedFacts (by rfl)

private theorem leaf2386FlatSound : Sound leaf2386Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2386CertificateValid
    leaf2386InnerLogValid leaf2386CoversExact leaf2386LowerChecked

private noncomputable def leaf2387Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2387Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432926208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1827392047/1073741824) }, upper := { exponent := 0, mantissa := (7039/4096) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869848063/274865852416) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2387InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2387LocalValidity :
    LeafFacts leaf2387Box leaf2387Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2387Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432926208) }) = true
      norm_num [leaf2387Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2387CertificateValid :
    WideCertificateValid leaf2387Box leaf2387Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi196ValidityFacts
    leaf2387LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2387CoverageChecked :
    coverageCheck (innerAD leaf2387Box) leaf2387InnerLog = true := by
  rfl'

private theorem leaf2387InnerLogValid :
    leaf2387InnerLog.Valid 8 (innerAD leaf2387Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2387CoverageChecked

private noncomputable def leaf2387InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2387InputLogOnePlusV_eq :
    leaf2387InputLogOnePlusV = outerEnclosure 24
      (leaf2387Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2387RoundedFacts : LeafRoundedFacts 8
    leaf2387Certificate.logOnePlusV leaf2387InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2387InputLogOnePlusV_eq }

private noncomputable def leaf2387Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2387InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2387LowerChecked :
    lowerCheck 24 leaf2387Box leaf2387Inputs = true := by
  rfl'

private theorem leaf2387CoversExact : CoversExact 8
    leaf2387Box leaf2387Certificate leaf2387InnerLog leaf2387Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2387RoundedFacts (by rfl)

private theorem leaf2387FlatSound : Sound leaf2387Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2387CertificateValid
    leaf2387InnerLogValid leaf2387CoversExact leaf2387LowerChecked

private noncomputable def leaf2388Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2388Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433010688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1816579267/1073741824) }, upper := { exponent := 0, mantissa := (27991/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869932543/274866021376) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2388InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2388LocalValidity :
    LeafFacts leaf2388Box leaf2388Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2388Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433010688) }) = true
      norm_num [leaf2388Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2388CertificateValid :
    WideCertificateValid leaf2388Box leaf2388Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi195ValidityFacts
    leaf2388LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2388CoverageChecked :
    coverageCheck (innerAD leaf2388Box) leaf2388InnerLog = true := by
  rfl'

private theorem leaf2388InnerLogValid :
    leaf2388InnerLog.Valid 8 (innerAD leaf2388Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2388CoverageChecked

private noncomputable def leaf2388InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2388InputLogOnePlusV_eq :
    leaf2388InputLogOnePlusV = outerEnclosure 24
      (leaf2388Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2388RoundedFacts : LeafRoundedFacts 8
    leaf2388Certificate.logOnePlusV leaf2388InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2388InputLogOnePlusV_eq }

private noncomputable def leaf2388Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi195InputQChi innerPair64Input
    leaf2388InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2388LowerChecked :
    lowerCheck 24 leaf2388Box leaf2388Inputs = true := by
  rfl'

private theorem leaf2388CoversExact : CoversExact 8
    leaf2388Box leaf2388Certificate leaf2388InnerLog leaf2388Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf2388RoundedFacts (by rfl)

private theorem leaf2388FlatSound : Sound leaf2388Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2388CertificateValid
    leaf2388InnerLogValid leaf2388CoversExact leaf2388LowerChecked

private noncomputable def leaf2389Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2389Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (65529/65536), upper := (639241497/639222784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1830865241/1073741824) }, upper := { exponent := 0, mantissa := (14105/8192) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1278464281/1278445568) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2389InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2389LocalValidity :
    LeafFacts leaf2389Box leaf2389Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2389Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (639241497/639222784) }) = true
      norm_num [leaf2389Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2389CertificateValid :
    WideCertificateValid leaf2389Box leaf2389Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi196ValidityFacts
    leaf2389LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2389CoverageChecked :
    coverageCheck (innerAD leaf2389Box) leaf2389InnerLog = true := by
  rfl'

private theorem leaf2389InnerLogValid :
    leaf2389InnerLog.Valid 8 (innerAD leaf2389Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2389CoverageChecked

private noncomputable def leaf2389InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2389InputLogOnePlusV_eq :
    leaf2389InputLogOnePlusV = outerEnclosure 24
      (leaf2389Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2389RoundedFacts : LeafRoundedFacts 8
    leaf2389Certificate.logOnePlusV leaf2389InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2389InputLogOnePlusV_eq }

private noncomputable def leaf2389Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2389InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2389LowerChecked :
    lowerCheck 24 leaf2389Box leaf2389Inputs = true := by
  rfl'

private theorem leaf2389CoversExact : CoversExact 8
    leaf2389Box leaf2389Certificate leaf2389InnerLog leaf2389Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2389RoundedFacts (by rfl)

private theorem leaf2389FlatSound : Sound leaf2389Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2389CertificateValid
    leaf2389InnerLogValid leaf2389CoversExact leaf2389LowerChecked

private noncomputable def leaf2390Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2390Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432983552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1819986929/1073741824) }, upper := { exponent := 0, mantissa := (7011/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869905407/274865967104) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2390InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2390LocalValidity :
    LeafFacts leaf2390Box leaf2390Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2390Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432983552) }) = true
      norm_num [leaf2390Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2390CertificateValid :
    WideCertificateValid leaf2390Box leaf2390Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi195ValidityFacts
    leaf2390LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2390CoverageChecked :
    coverageCheck (innerAD leaf2390Box) leaf2390InnerLog = true := by
  rfl'

private theorem leaf2390InnerLogValid :
    leaf2390InnerLog.Valid 8 (innerAD leaf2390Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2390CoverageChecked

private noncomputable def leaf2390InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2390InputLogOnePlusV_eq :
    leaf2390InputLogOnePlusV = outerEnclosure 24
      (leaf2390Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2390RoundedFacts : LeafRoundedFacts 8
    leaf2390Certificate.logOnePlusV leaf2390InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2390InputLogOnePlusV_eq }

private noncomputable def leaf2390Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi195InputQChi innerPair64Input
    leaf2390InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2390LowerChecked :
    lowerCheck 24 leaf2390Box leaf2390Inputs = true := by
  rfl'

private theorem leaf2390CoversExact : CoversExact 8
    leaf2390Box leaf2390Certificate leaf2390InnerLog leaf2390Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf2390RoundedFacts (by rfl)

private theorem leaf2390FlatSound : Sound leaf2390Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2390CertificateValid
    leaf2390InnerLogValid leaf2390CoversExact leaf2390LowerChecked

private noncomputable def leaf2391Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2391Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432870912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1834338435/1073741824) }, upper := { exponent := 0, mantissa := (3533/2048) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869792767/274865741824) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2391InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2391LocalValidity :
    LeafFacts leaf2391Box leaf2391Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2391Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432870912) }) = true
      norm_num [leaf2391Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2391CertificateValid :
    WideCertificateValid leaf2391Box leaf2391Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi196ValidityFacts
    leaf2391LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2391CoverageChecked :
    coverageCheck (innerAD leaf2391Box) leaf2391InnerLog = true := by
  rfl'

private theorem leaf2391InnerLogValid :
    leaf2391InnerLog.Valid 8 (innerAD leaf2391Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2391CoverageChecked

private noncomputable def leaf2391InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2391InputLogOnePlusV_eq :
    leaf2391InputLogOnePlusV = outerEnclosure 24
      (leaf2391Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2391RoundedFacts : LeafRoundedFacts 8
    leaf2391Certificate.logOnePlusV leaf2391InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2391InputLogOnePlusV_eq }

private noncomputable def leaf2391Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2391InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2391LowerChecked :
    lowerCheck 24 leaf2391Box leaf2391Inputs = true := by
  rfl'

private theorem leaf2391CoversExact : CoversExact 8
    leaf2391Box leaf2391Certificate leaf2391InnerLog leaf2391Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2391RoundedFacts (by rfl)

private theorem leaf2391FlatSound : Sound leaf2391Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2391CertificateValid
    leaf2391InnerLogValid leaf2391CoversExact leaf2391LowerChecked

private noncomputable def leaf2392Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2392Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742367/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810947584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1838073763/1073741824) }, upper := { exponent := 0, mantissa := (28319/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623254869/91621895168) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2392InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2392LocalValidity :
    LeafFacts leaf2392Box leaf2392Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2392Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810947584) }) = true
      norm_num [leaf2392Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2392CertificateValid :
    WideCertificateValid leaf2392Box leaf2392Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi197ValidityFacts
    leaf2392LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2392CoverageChecked :
    coverageCheck (innerAD leaf2392Box) leaf2392InnerLog = true := by
  rfl'

private theorem leaf2392InnerLogValid :
    leaf2392InnerLog.Valid 8 (innerAD leaf2392Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2392CoverageChecked

private noncomputable def leaf2392InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2392InputLogOnePlusV_eq :
    leaf2392InputLogOnePlusV = outerEnclosure 24
      (leaf2392Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2392RoundedFacts : LeafRoundedFacts 8
    leaf2392Certificate.logOnePlusV leaf2392InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2392InputLogOnePlusV_eq }

private noncomputable def leaf2392Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2392InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2392LowerChecked :
    lowerCheck 24 leaf2392Box leaf2392Inputs = true := by
  rfl'

private theorem leaf2392CoversExact : CoversExact 8
    leaf2392Box leaf2392Certificate leaf2392InnerLog leaf2392Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2392RoundedFacts (by rfl)

private theorem leaf2392FlatSound : Sound leaf2392Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2392CertificateValid
    leaf2392InnerLogValid leaf2392CoversExact leaf2392LowerChecked

private noncomputable def leaf2393Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2393Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432731648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1852228673/1073741824) }, upper := { exponent := 0, mantissa := (3567/2048) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869653503/274865463296) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2393InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2393LocalValidity :
    LeafFacts leaf2393Box leaf2393Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2393Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432731648) }) = true
      norm_num [leaf2393Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2393CertificateValid :
    WideCertificateValid leaf2393Box leaf2393Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi198ValidityFacts
    leaf2393LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2393CoverageChecked :
    coverageCheck (innerAD leaf2393Box) leaf2393InnerLog = true := by
  rfl'

private theorem leaf2393InnerLogValid :
    leaf2393InnerLog.Valid 8 (innerAD leaf2393Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2393CoverageChecked

private noncomputable def leaf2393InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2393InputLogOnePlusV_eq :
    leaf2393InputLogOnePlusV = outerEnclosure 24
      (leaf2393Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2393RoundedFacts : LeafRoundedFacts 8
    leaf2393Certificate.logOnePlusV leaf2393InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2393InputLogOnePlusV_eq }

private noncomputable def leaf2393Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi198InputQChi innerPair64Input
    leaf2393InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2393LowerChecked :
    lowerCheck 24 leaf2393Box leaf2393Inputs = true := by
  rfl'

private theorem leaf2393CoversExact : CoversExact 8
    leaf2393Box leaf2393Certificate leaf2393InnerLog leaf2393Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi198RoundedFacts
    innerPair64RoundedFacts leaf2393RoundedFacts (by rfl)

private theorem leaf2393FlatSound : Sound leaf2393Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2393CertificateValid
    leaf2393InnerLogValid leaf2393CoversExact leaf2393LowerChecked

private noncomputable def leaf2394Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2394Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742369/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432814592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1841612489/1073741824) }, upper := { exponent := 0, mantissa := (14187/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869736447/274865629184) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2394InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2394LocalValidity :
    LeafFacts leaf2394Box leaf2394Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2394Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432814592) }) = true
      norm_num [leaf2394Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2394CertificateValid :
    WideCertificateValid leaf2394Box leaf2394Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi197ValidityFacts
    leaf2394LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2394CoverageChecked :
    coverageCheck (innerAD leaf2394Box) leaf2394InnerLog = true := by
  rfl'

private theorem leaf2394InnerLogValid :
    leaf2394InnerLog.Valid 8 (innerAD leaf2394Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2394CoverageChecked

private noncomputable def leaf2394InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2394InputLogOnePlusV_eq :
    leaf2394InputLogOnePlusV = outerEnclosure 24
      (leaf2394Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2394RoundedFacts : LeafRoundedFacts 8
    leaf2394Certificate.logOnePlusV leaf2394InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2394InputLogOnePlusV_eq }

private noncomputable def leaf2394Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2394InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2394LowerChecked :
    lowerCheck 24 leaf2394Box leaf2394Inputs = true := by
  rfl'

private theorem leaf2394CoversExact : CoversExact 8
    leaf2394Box leaf2394Certificate leaf2394InnerLog leaf2394Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2394RoundedFacts (by rfl)

private theorem leaf2394FlatSound : Sound leaf2394Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2394CertificateValid
    leaf2394InnerLogValid leaf2394CoversExact leaf2394LowerChecked

private noncomputable def leaf2395Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2395Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810900992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1855832931/1073741824) }, upper := { exponent := 0, mantissa := (1787/1024) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623208277/91621801984) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2395InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2395LocalValidity :
    LeafFacts leaf2395Box leaf2395Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2395Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810900992) }) = true
      norm_num [leaf2395Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2395CertificateValid :
    WideCertificateValid leaf2395Box leaf2395Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi198ValidityFacts
    leaf2395LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2395CoverageChecked :
    coverageCheck (innerAD leaf2395Box) leaf2395InnerLog = true := by
  rfl'

private theorem leaf2395InnerLogValid :
    leaf2395InnerLog.Valid 8 (innerAD leaf2395Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2395CoverageChecked

private noncomputable def leaf2395InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2395InputLogOnePlusV_eq :
    leaf2395InputLogOnePlusV = outerEnclosure 24
      (leaf2395Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2395RoundedFacts : LeafRoundedFacts 8
    leaf2395Certificate.logOnePlusV leaf2395InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2395InputLogOnePlusV_eq }

private noncomputable def leaf2395Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi198InputQChi innerPair64Input
    leaf2395InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2395LowerChecked :
    lowerCheck 24 leaf2395Box leaf2395Inputs = true := by
  rfl'

private theorem leaf2395CoversExact : CoversExact 8
    leaf2395Box leaf2395Certificate leaf2395InnerLog leaf2395Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi198RoundedFacts
    innerPair64RoundedFacts leaf2395RoundedFacts (by rfl)

private theorem leaf2395FlatSound : Sound leaf2395Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2395CertificateValid
    leaf2395InnerLogValid leaf2395CoversExact leaf2395LowerChecked

private noncomputable def leaf2396Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2396Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432786432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1845151215/1073741824) }, upper := { exponent := 0, mantissa := (28429/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869708287/274865572864) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2396InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2396LocalValidity :
    LeafFacts leaf2396Box leaf2396Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2396Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432786432) }) = true
      norm_num [leaf2396Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2396CertificateValid :
    WideCertificateValid leaf2396Box leaf2396Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi197ValidityFacts
    leaf2396LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2396CoverageChecked :
    coverageCheck (innerAD leaf2396Box) leaf2396InnerLog = true := by
  rfl'

private theorem leaf2396InnerLogValid :
    leaf2396InnerLog.Valid 8 (innerAD leaf2396Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2396CoverageChecked

private noncomputable def leaf2396InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2396InputLogOnePlusV_eq :
    leaf2396InputLogOnePlusV = outerEnclosure 24
      (leaf2396Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2396RoundedFacts : LeafRoundedFacts 8
    leaf2396Certificate.logOnePlusV leaf2396InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2396InputLogOnePlusV_eq }

private noncomputable def leaf2396Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2396InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2396LowerChecked :
    lowerCheck 24 leaf2396Box leaf2396Inputs = true := by
  rfl'

private theorem leaf2396CoversExact : CoversExact 8
    leaf2396Box leaf2396Certificate leaf2396InnerLog leaf2396Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2396RoundedFacts (by rfl)

private theorem leaf2396FlatSound : Sound leaf2396Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2396CertificateValid
    leaf2396InnerLogValid leaf2396CoversExact leaf2396LowerChecked

private noncomputable def leaf2397Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2397Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432674304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1859437189/1073741824) }, upper := { exponent := 0, mantissa := (3581/2048) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869596159/274865348608) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2397InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2397LocalValidity :
    LeafFacts leaf2397Box leaf2397Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2397Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432674304) }) = true
      norm_num [leaf2397Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2397CertificateValid :
    WideCertificateValid leaf2397Box leaf2397Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi198ValidityFacts
    leaf2397LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2397CoverageChecked :
    coverageCheck (innerAD leaf2397Box) leaf2397InnerLog = true := by
  rfl'

private theorem leaf2397InnerLogValid :
    leaf2397InnerLog.Valid 8 (innerAD leaf2397Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2397CoverageChecked

private noncomputable def leaf2397InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2397InputLogOnePlusV_eq :
    leaf2397InputLogOnePlusV = outerEnclosure 24
      (leaf2397Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2397RoundedFacts : LeafRoundedFacts 8
    leaf2397Certificate.logOnePlusV leaf2397InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2397InputLogOnePlusV_eq }

private noncomputable def leaf2397Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi198InputQChi innerPair64Input
    leaf2397InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2397LowerChecked :
    lowerCheck 24 leaf2397Box leaf2397Inputs = true := by
  rfl'

private theorem leaf2397CoversExact : CoversExact 8
    leaf2397Box leaf2397Certificate leaf2397InnerLog leaf2397Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi198RoundedFacts
    innerPair64RoundedFacts leaf2397RoundedFacts (by rfl)

private theorem leaf2397FlatSound : Sound leaf2397Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2397CertificateValid
    leaf2397InnerLogValid leaf2397CoversExact leaf2397LowerChecked

private noncomputable def leaf2398Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2398Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810919424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1848689941/1073741824) }, upper := { exponent := 0, mantissa := (7121/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623226709/91621838848) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2398InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2398LocalValidity :
    LeafFacts leaf2398Box leaf2398Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2398Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810919424) }) = true
      norm_num [leaf2398Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2398CertificateValid :
    WideCertificateValid leaf2398Box leaf2398Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi197ValidityFacts
    leaf2398LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2398CoverageChecked :
    coverageCheck (innerAD leaf2398Box) leaf2398InnerLog = true := by
  rfl'

private theorem leaf2398InnerLogValid :
    leaf2398InnerLog.Valid 8 (innerAD leaf2398Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2398CoverageChecked

private noncomputable def leaf2398InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2398InputLogOnePlusV_eq :
    leaf2398InputLogOnePlusV = outerEnclosure 24
      (leaf2398Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2398RoundedFacts : LeafRoundedFacts 8
    leaf2398Certificate.logOnePlusV leaf2398InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2398InputLogOnePlusV_eq }

private noncomputable def leaf2398Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2398InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2398LowerChecked :
    lowerCheck 24 leaf2398Box leaf2398Inputs = true := by
  rfl'

private theorem leaf2398CoversExact : CoversExact 8
    leaf2398Box leaf2398Certificate leaf2398InnerLog leaf2398Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2398RoundedFacts (by rfl)

private theorem leaf2398FlatSound : Sound leaf2398Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2398CertificateValid
    leaf2398InnerLogValid leaf2398CoversExact leaf2398LowerChecked

private noncomputable def leaf2399Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2399Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (534774015/534757376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1863041447/1073741824) }, upper := { exponent := 0, mantissa := (897/512) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1069531391/1069514752) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2399InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2399LocalValidity :
    LeafFacts leaf2399Box leaf2399Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2399Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (534774015/534757376) }) = true
      norm_num [leaf2399Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2399CertificateValid :
    WideCertificateValid leaf2399Box leaf2399Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi198ValidityFacts
    leaf2399LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2399CoverageChecked :
    coverageCheck (innerAD leaf2399Box) leaf2399InnerLog = true := by
  rfl'

private theorem leaf2399InnerLogValid :
    leaf2399InnerLog.Valid 8 (innerAD leaf2399Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2399CoverageChecked

private noncomputable def leaf2399InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2399InputLogOnePlusV_eq :
    leaf2399InputLogOnePlusV = outerEnclosure 24
      (leaf2399Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2399RoundedFacts : LeafRoundedFacts 8
    leaf2399Certificate.logOnePlusV leaf2399InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2399InputLogOnePlusV_eq }

private noncomputable def leaf2399Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi198InputQChi innerPair66Input
    leaf2399InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2399LowerChecked :
    lowerCheck 24 leaf2399Box leaf2399Inputs = true := by
  rfl'

private theorem leaf2399CoversExact : CoversExact 8
    leaf2399Box leaf2399Certificate leaf2399InnerLog leaf2399Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi198RoundedFacts
    innerPair66RoundedFacts leaf2399RoundedFacts (by rfl)

private theorem leaf2399FlatSound : Sound leaf2399Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2399CertificateValid
    leaf2399InnerLogValid leaf2399CoversExact leaf2399LowerChecked

private noncomputable def leaf2400Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2400Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810985472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1823394591/1073741824) }, upper := { exponent := 0, mantissa := (28097/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623292757/91621970944) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2400InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2400LocalValidity :
    LeafFacts leaf2400Box leaf2400Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2400Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810985472) }) = true
      norm_num [leaf2400Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2400CertificateValid :
    WideCertificateValid leaf2400Box leaf2400Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi195ValidityFacts
    leaf2400LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2400CoverageChecked :
    coverageCheck (innerAD leaf2400Box) leaf2400InnerLog = true := by
  rfl'

private theorem leaf2400InnerLogValid :
    leaf2400InnerLog.Valid 8 (innerAD leaf2400Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2400CoverageChecked

private noncomputable def leaf2400InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2400InputLogOnePlusV_eq :
    leaf2400InputLogOnePlusV = outerEnclosure 24
      (leaf2400Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2400RoundedFacts : LeafRoundedFacts 8
    leaf2400Certificate.logOnePlusV leaf2400InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2400InputLogOnePlusV_eq }

private noncomputable def leaf2400Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi195InputQChi innerPair64Input
    leaf2400InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2400LowerChecked :
    lowerCheck 24 leaf2400Box leaf2400Inputs = true := by
  rfl'

private theorem leaf2400CoversExact : CoversExact 8
    leaf2400Box leaf2400Certificate leaf2400InnerLog leaf2400Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf2400RoundedFacts (by rfl)

private theorem leaf2400FlatSound : Sound leaf2400Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2400CertificateValid
    leaf2400InnerLogValid leaf2400CoversExact leaf2400LowerChecked

private noncomputable def leaf2401Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2401Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432843264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1837811629/1073741824) }, upper := { exponent := 0, mantissa := (14159/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869765119/274865686528) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2401InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2401LocalValidity :
    LeafFacts leaf2401Box leaf2401Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2401Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432843264) }) = true
      norm_num [leaf2401Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2401CertificateValid :
    WideCertificateValid leaf2401Box leaf2401Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi196ValidityFacts
    leaf2401LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2401CoverageChecked :
    coverageCheck (innerAD leaf2401Box) leaf2401InnerLog = true := by
  rfl'

private theorem leaf2401InnerLogValid :
    leaf2401InnerLog.Valid 8 (innerAD leaf2401Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2401CoverageChecked

private noncomputable def leaf2401InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2401InputLogOnePlusV_eq :
    leaf2401InputLogOnePlusV = outerEnclosure 24
      (leaf2401Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2401RoundedFacts : LeafRoundedFacts 8
    leaf2401Certificate.logOnePlusV leaf2401InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2401InputLogOnePlusV_eq }

private noncomputable def leaf2401Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2401InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2401LowerChecked :
    lowerCheck 24 leaf2401Box leaf2401Inputs = true := by
  rfl'

private theorem leaf2401CoversExact : CoversExact 8
    leaf2401Box leaf2401Certificate leaf2401InnerLog leaf2401Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2401RoundedFacts (by rfl)

private theorem leaf2401FlatSound : Sound leaf2401Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2401CertificateValid
    leaf2401InnerLogValid leaf2401CoversExact leaf2401LowerChecked

private noncomputable def leaf2402Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2402Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486585856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1826802253/1073741824) }, upper := { exponent := 0, mantissa := (14075/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973970227/54973171712) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2402InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2402LocalValidity :
    LeafFacts leaf2402Box leaf2402Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2402Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486585856) }) = true
      norm_num [leaf2402Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2402CertificateValid :
    WideCertificateValid leaf2402Box leaf2402Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi195ValidityFacts
    leaf2402LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2402CoverageChecked :
    coverageCheck (innerAD leaf2402Box) leaf2402InnerLog = true := by
  rfl'

private theorem leaf2402InnerLogValid :
    leaf2402InnerLog.Valid 8 (innerAD leaf2402Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2402CoverageChecked

private noncomputable def leaf2402InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2402InputLogOnePlusV_eq :
    leaf2402InputLogOnePlusV = outerEnclosure 24
      (leaf2402Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2402RoundedFacts : LeafRoundedFacts 8
    leaf2402Certificate.logOnePlusV leaf2402InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2402InputLogOnePlusV_eq }

private noncomputable def leaf2402Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi195InputQChi innerPair64Input
    leaf2402InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2402LowerChecked :
    lowerCheck 24 leaf2402Box leaf2402Inputs = true := by
  rfl'

private theorem leaf2402CoversExact : CoversExact 8
    leaf2402Box leaf2402Certificate leaf2402InnerLog leaf2402Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf2402RoundedFacts (by rfl)

private theorem leaf2402FlatSound : Sound leaf2402Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2402CertificateValid
    leaf2402InnerLogValid leaf2402CoversExact leaf2402LowerChecked

private noncomputable def leaf2403Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2403Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432815616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1841284823/1073741824) }, upper := { exponent := 0, mantissa := (7093/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869737471/274865631232) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2403InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2403LocalValidity :
    LeafFacts leaf2403Box leaf2403Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2403Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432815616) }) = true
      norm_num [leaf2403Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2403CertificateValid :
    WideCertificateValid leaf2403Box leaf2403Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi196ValidityFacts
    leaf2403LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2403CoverageChecked :
    coverageCheck (innerAD leaf2403Box) leaf2403InnerLog = true := by
  rfl'

private theorem leaf2403InnerLogValid :
    leaf2403InnerLog.Valid 8 (innerAD leaf2403Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2403CoverageChecked

private noncomputable def leaf2403InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2403InputLogOnePlusV_eq :
    leaf2403InputLogOnePlusV = outerEnclosure 24
      (leaf2403Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2403RoundedFacts : LeafRoundedFacts 8
    leaf2403Certificate.logOnePlusV leaf2403InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2403InputLogOnePlusV_eq }

private noncomputable def leaf2403Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2403InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2403LowerChecked :
    lowerCheck 24 leaf2403Box leaf2403Inputs = true := by
  rfl'

private theorem leaf2403CoversExact : CoversExact 8
    leaf2403Box leaf2403Certificate leaf2403InnerLog leaf2403Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2403RoundedFacts (by rfl)

private theorem leaf2403FlatSound : Sound leaf2403Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2403CertificateValid
    leaf2403InnerLogValid leaf2403CoversExact leaf2403LowerChecked

private noncomputable def leaf2404Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2404Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432902144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1830209915/1073741824) }, upper := { exponent := 0, mantissa := (28203/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869823999/274865804288) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2404InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2404LocalValidity :
    LeafFacts leaf2404Box leaf2404Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2404Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432902144) }) = true
      norm_num [leaf2404Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2404CertificateValid :
    WideCertificateValid leaf2404Box leaf2404Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi195ValidityFacts
    leaf2404LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2404CoverageChecked :
    coverageCheck (innerAD leaf2404Box) leaf2404InnerLog = true := by
  rfl'

private theorem leaf2404InnerLogValid :
    leaf2404InnerLog.Valid 8 (innerAD leaf2404Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2404CoverageChecked

private noncomputable def leaf2404InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2404InputLogOnePlusV_eq :
    leaf2404InputLogOnePlusV = outerEnclosure 24
      (leaf2404Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2404RoundedFacts : LeafRoundedFacts 8
    leaf2404Certificate.logOnePlusV leaf2404InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2404InputLogOnePlusV_eq }

private noncomputable def leaf2404Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi195InputQChi innerPair64Input
    leaf2404InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2404LowerChecked :
    lowerCheck 24 leaf2404Box leaf2404Inputs = true := by
  rfl'

private theorem leaf2404CoversExact : CoversExact 8
    leaf2404Box leaf2404Certificate leaf2404InnerLog leaf2404Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf2404RoundedFacts (by rfl)

private theorem leaf2404FlatSound : Sound leaf2404Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2404CertificateValid
    leaf2404InnerLogValid leaf2404CoversExact leaf2404LowerChecked

private noncomputable def leaf2405Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2405Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432787968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1844758017/1073741824) }, upper := { exponent := 0, mantissa := (14213/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869709823/274865575936) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2405InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2405LocalValidity :
    LeafFacts leaf2405Box leaf2405Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2405Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432787968) }) = true
      norm_num [leaf2405Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2405CertificateValid :
    WideCertificateValid leaf2405Box leaf2405Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi196ValidityFacts
    leaf2405LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2405CoverageChecked :
    coverageCheck (innerAD leaf2405Box) leaf2405InnerLog = true := by
  rfl'

private theorem leaf2405InnerLogValid :
    leaf2405InnerLog.Valid 8 (innerAD leaf2405Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2405CoverageChecked

private noncomputable def leaf2405InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2405InputLogOnePlusV_eq :
    leaf2405InputLogOnePlusV = outerEnclosure 24
      (leaf2405Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2405RoundedFacts : LeafRoundedFacts 8
    leaf2405Certificate.logOnePlusV leaf2405InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2405InputLogOnePlusV_eq }

private noncomputable def leaf2405Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2405InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2405LowerChecked :
    lowerCheck 24 leaf2405Box leaf2405Inputs = true := by
  rfl'

private theorem leaf2405CoversExact : CoversExact 8
    leaf2405Box leaf2405Certificate leaf2405InnerLog leaf2405Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2405RoundedFacts (by rfl)

private theorem leaf2405FlatSound : Sound leaf2405Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2405CertificateValid
    leaf2405InnerLogValid leaf2405CoversExact leaf2405LowerChecked

private noncomputable def leaf2406Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf2406Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810958336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1833617577/1073741824) }, upper := { exponent := 0, mantissa := (883/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623265621/91621916672) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2406InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2406LocalValidity :
    LeafFacts leaf2406Box leaf2406Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2406Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810958336) }) = true
      norm_num [leaf2406Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2406CertificateValid :
    WideCertificateValid leaf2406Box leaf2406Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi195ValidityFacts
    leaf2406LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2406CoverageChecked :
    coverageCheck (innerAD leaf2406Box) leaf2406InnerLog = true := by
  rfl'

private theorem leaf2406InnerLogValid :
    leaf2406InnerLog.Valid 8 (innerAD leaf2406Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2406CoverageChecked

private noncomputable def leaf2406InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2406InputLogOnePlusV_eq :
    leaf2406InputLogOnePlusV = outerEnclosure 24
      (leaf2406Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2406RoundedFacts : LeafRoundedFacts 8
    leaf2406Certificate.logOnePlusV leaf2406InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2406InputLogOnePlusV_eq }

private noncomputable def leaf2406Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi195InputQChi innerPair64Input
    leaf2406InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2406LowerChecked :
    lowerCheck 24 leaf2406Box leaf2406Inputs = true := by
  rfl'

private theorem leaf2406CoversExact : CoversExact 8
    leaf2406Box leaf2406Certificate leaf2406InnerLog leaf2406Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi195RoundedFacts
    innerPair64RoundedFacts leaf2406RoundedFacts (by rfl)

private theorem leaf2406FlatSound : Sound leaf2406Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2406CertificateValid
    leaf2406InnerLogValid leaf2406CoversExact leaf2406LowerChecked

private noncomputable def leaf2407Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf2407Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486552064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1848231211/1073741824) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973936435/54973104128) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2407InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2407LocalValidity :
    LeafFacts leaf2407Box leaf2407Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2407Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486552064) }) = true
      norm_num [leaf2407Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2407CertificateValid :
    WideCertificateValid leaf2407Box leaf2407Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi196ValidityFacts
    leaf2407LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2407CoverageChecked :
    coverageCheck (innerAD leaf2407Box) leaf2407InnerLog = true := by
  rfl'

private theorem leaf2407InnerLogValid :
    leaf2407InnerLog.Valid 8 (innerAD leaf2407Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2407CoverageChecked

private noncomputable def leaf2407InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2407InputLogOnePlusV_eq :
    leaf2407InputLogOnePlusV = outerEnclosure 24
      (leaf2407Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2407RoundedFacts : LeafRoundedFacts 8
    leaf2407Certificate.logOnePlusV leaf2407InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2407InputLogOnePlusV_eq }

private noncomputable def leaf2407Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi196InputQChi innerPair64Input
    leaf2407InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2407LowerChecked :
    lowerCheck 24 leaf2407Box leaf2407Inputs = true := by
  rfl'

private theorem leaf2407CoversExact : CoversExact 8
    leaf2407Box leaf2407Certificate leaf2407InnerLog leaf2407Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi196RoundedFacts
    innerPair64RoundedFacts leaf2407RoundedFacts (by rfl)

private theorem leaf2407FlatSound : Sound leaf2407Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2407CertificateValid
    leaf2407InnerLogValid leaf2407CoversExact leaf2407LowerChecked

private noncomputable def leaf2408Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2408Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432730112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1852228667/1073741824) }, upper := { exponent := 0, mantissa := (28539/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869651967/274865460224) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2408InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2408LocalValidity :
    LeafFacts leaf2408Box leaf2408Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2408Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432730112) }) = true
      norm_num [leaf2408Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2408CertificateValid :
    WideCertificateValid leaf2408Box leaf2408Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi197ValidityFacts
    leaf2408LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2408CoverageChecked :
    coverageCheck (innerAD leaf2408Box) leaf2408InnerLog = true := by
  rfl'

private theorem leaf2408InnerLogValid :
    leaf2408InnerLog.Valid 8 (innerAD leaf2408Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2408CoverageChecked

private noncomputable def leaf2408InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2408InputLogOnePlusV_eq :
    leaf2408InputLogOnePlusV = outerEnclosure 24
      (leaf2408Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2408RoundedFacts : LeafRoundedFacts 8
    leaf2408Certificate.logOnePlusV leaf2408InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2408InputLogOnePlusV_eq }

private noncomputable def leaf2408Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2408InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2408LowerChecked :
    lowerCheck 24 leaf2408Box leaf2408Inputs = true := by
  rfl'

private theorem leaf2408CoversExact : CoversExact 8
    leaf2408Box leaf2408Certificate leaf2408InnerLog leaf2408Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2408RoundedFacts (by rfl)

private theorem leaf2408FlatSound : Sound leaf2408Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2408CertificateValid
    leaf2408InnerLogValid leaf2408CoversExact leaf2408LowerChecked

private noncomputable def leaf2409Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2409Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162174464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1866645705/1073741824) }, upper := { exponent := 0, mantissa := (3595/2048) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324635921/18324348928) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2409InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2409LocalValidity :
    LeafFacts leaf2409Box leaf2409Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2409Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162174464) }) = true
      norm_num [leaf2409Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2409CertificateValid :
    WideCertificateValid leaf2409Box leaf2409Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi198ValidityFacts
    leaf2409LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2409CoverageChecked :
    coverageCheck (innerAD leaf2409Box) leaf2409InnerLog = true := by
  rfl'

private theorem leaf2409InnerLogValid :
    leaf2409InnerLog.Valid 8 (innerAD leaf2409Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2409CoverageChecked

private noncomputable def leaf2409InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf2409InputLogOnePlusV_eq :
    leaf2409InputLogOnePlusV = outerEnclosure 24
      (leaf2409Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2409RoundedFacts : LeafRoundedFacts 8
    leaf2409Certificate.logOnePlusV leaf2409InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2409InputLogOnePlusV_eq }

private noncomputable def leaf2409Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi198InputQChi innerPair66Input
    leaf2409InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2409LowerChecked :
    lowerCheck 24 leaf2409Box leaf2409Inputs = true := by
  rfl'

private theorem leaf2409CoversExact : CoversExact 8
    leaf2409Box leaf2409Certificate leaf2409InnerLog leaf2409Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi198RoundedFacts
    innerPair66RoundedFacts leaf2409RoundedFacts (by rfl)

private theorem leaf2409FlatSound : Sound leaf2409Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2409CertificateValid
    leaf2409InnerLogValid leaf2409CoversExact leaf2409LowerChecked

private noncomputable def leaf2410Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2410Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432701952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1855767393/1073741824) }, upper := { exponent := 0, mantissa := (14297/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869623807/274865403904) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2410InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2410LocalValidity :
    LeafFacts leaf2410Box leaf2410Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2410Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432701952) }) = true
      norm_num [leaf2410Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2410CertificateValid :
    WideCertificateValid leaf2410Box leaf2410Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi197ValidityFacts
    leaf2410LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2410CoverageChecked :
    coverageCheck (innerAD leaf2410Box) leaf2410InnerLog = true := by
  rfl'

private theorem leaf2410InnerLogValid :
    leaf2410InnerLog.Valid 8 (innerAD leaf2410Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2410CoverageChecked

private noncomputable def leaf2410InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2410InputLogOnePlusV_eq :
    leaf2410InputLogOnePlusV = outerEnclosure 24
      (leaf2410Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2410RoundedFacts : LeafRoundedFacts 8
    leaf2410Certificate.logOnePlusV leaf2410InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2410InputLogOnePlusV_eq }

private noncomputable def leaf2410Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2410InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2410LowerChecked :
    lowerCheck 24 leaf2410Box leaf2410Inputs = true := by
  rfl'

private theorem leaf2410CoversExact : CoversExact 8
    leaf2410Box leaf2410Certificate leaf2410InnerLog leaf2410Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2410RoundedFacts (by rfl)

private theorem leaf2410FlatSound : Sound leaf2410Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2410CertificateValid
    leaf2410InnerLogValid leaf2410CoversExact leaf2410LowerChecked

private noncomputable def leaf2411Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2411Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432588288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1870249963/1073741824) }, upper := { exponent := 0, mantissa := (1801/1024) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869510143/274865176576) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2411InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2411LocalValidity :
    LeafFacts leaf2411Box leaf2411Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2411Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432588288) }) = true
      norm_num [leaf2411Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2411CertificateValid :
    WideCertificateValid leaf2411Box leaf2411Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi198ValidityFacts
    leaf2411LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2411CoverageChecked :
    coverageCheck (innerAD leaf2411Box) leaf2411InnerLog = true := by
  rfl'

private theorem leaf2411InnerLogValid :
    leaf2411InnerLog.Valid 8 (innerAD leaf2411Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2411CoverageChecked

private noncomputable def leaf2411InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2411InputLogOnePlusV_eq :
    leaf2411InputLogOnePlusV = outerEnclosure 24
      (leaf2411Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2411RoundedFacts : LeafRoundedFacts 8
    leaf2411Certificate.logOnePlusV leaf2411InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2411InputLogOnePlusV_eq }

private noncomputable def leaf2411Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi198InputQChi innerPair66Input
    leaf2411InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2411LowerChecked :
    lowerCheck 24 leaf2411Box leaf2411Inputs = true := by
  rfl'

private theorem leaf2411CoversExact : CoversExact 8
    leaf2411Box leaf2411Certificate leaf2411InnerLog leaf2411Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi198RoundedFacts
    innerPair66RoundedFacts leaf2411RoundedFacts (by rfl)

private theorem leaf2411FlatSound : Sound leaf2411Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2411CertificateValid
    leaf2411InnerLogValid leaf2411CoversExact leaf2411LowerChecked

private noncomputable def leaf2412Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2412Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270297088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1859306119/1073741824) }, upper := { exponent := 0, mantissa := (28649/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541066183/30540594176) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2412InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf2412LocalValidity :
    LeafFacts leaf2412Box leaf2412Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2412Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270297088) }) = true
      norm_num [leaf2412Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2412CertificateValid :
    WideCertificateValid leaf2412Box leaf2412Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi197ValidityFacts
    leaf2412LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2412CoverageChecked :
    coverageCheck (innerAD leaf2412Box) leaf2412InnerLog = true := by
  rfl'

private theorem leaf2412InnerLogValid :
    leaf2412InnerLog.Valid 8 (innerAD leaf2412Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf2412CoverageChecked

private noncomputable def leaf2412InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2412InputLogOnePlusV_eq :
    leaf2412InputLogOnePlusV = outerEnclosure 24
      (leaf2412Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2412RoundedFacts : LeafRoundedFacts 8
    leaf2412Certificate.logOnePlusV leaf2412InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2412InputLogOnePlusV_eq }

private noncomputable def leaf2412Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi197InputQChi innerPair64Input
    leaf2412InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2412LowerChecked :
    lowerCheck 24 leaf2412Box leaf2412Inputs = true := by
  rfl'

private theorem leaf2412CoversExact : CoversExact 8
    leaf2412Box leaf2412Certificate leaf2412InnerLog leaf2412Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi197RoundedFacts
    innerPair64RoundedFacts leaf2412RoundedFacts (by rfl)

private theorem leaf2412FlatSound : Sound leaf2412Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2412CertificateValid
    leaf2412InnerLogValid leaf2412CoversExact leaf2412LowerChecked

private noncomputable def leaf2413Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf2413Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (8191/8192), upper := (534774015/534757376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1862844845/1073741824) }, upper := { exponent := 0, mantissa := (897/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1069531391/1069514752) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2413InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2413LocalValidity :
    LeafFacts leaf2413Box leaf2413Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2413Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (534774015/534757376) }) = true
      norm_num [leaf2413Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2413CertificateValid :
    WideCertificateValid leaf2413Box leaf2413Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi197ValidityFacts
    leaf2413LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2413CoverageChecked :
    coverageCheck (innerAD leaf2413Box) leaf2413InnerLog = true := by
  rfl'

private theorem leaf2413InnerLogValid :
    leaf2413InnerLog.Valid 8 (innerAD leaf2413Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2413CoverageChecked

private noncomputable def leaf2413InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2413InputLogOnePlusV_eq :
    leaf2413InputLogOnePlusV = outerEnclosure 24
      (leaf2413Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2413RoundedFacts : LeafRoundedFacts 8
    leaf2413Certificate.logOnePlusV leaf2413InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2413InputLogOnePlusV_eq }

private noncomputable def leaf2413Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi197InputQChi innerPair66Input
    leaf2413InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2413LowerChecked :
    lowerCheck 24 leaf2413Box leaf2413Inputs = true := by
  rfl'

private theorem leaf2413CoversExact : CoversExact 8
    leaf2413Box leaf2413Certificate leaf2413InnerLog leaf2413Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi197RoundedFacts
    innerPair66RoundedFacts leaf2413RoundedFacts (by rfl)

private theorem leaf2413FlatSound : Sound leaf2413Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2413CertificateValid
    leaf2413InnerLogValid leaf2413CoversExact leaf2413LowerChecked

private noncomputable def leaf2414Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2414Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432559616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1873854221/1073741824) }, upper := { exponent := 0, mantissa := (3609/2048) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869481471/274865119232) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2414InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2414LocalValidity :
    LeafFacts leaf2414Box leaf2414Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2414Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432559616) }) = true
      norm_num [leaf2414Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2414CertificateValid :
    WideCertificateValid leaf2414Box leaf2414Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi198ValidityFacts
    leaf2414LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2414CoverageChecked :
    coverageCheck (innerAD leaf2414Box) leaf2414InnerLog = true := by
  rfl'

private theorem leaf2414InnerLogValid :
    leaf2414InnerLog.Valid 8 (innerAD leaf2414Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2414CoverageChecked

private noncomputable def leaf2414InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2414InputLogOnePlusV_eq :
    leaf2414InputLogOnePlusV = outerEnclosure 24
      (leaf2414Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2414RoundedFacts : LeafRoundedFacts 8
    leaf2414Certificate.logOnePlusV leaf2414InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2414InputLogOnePlusV_eq }

private noncomputable def leaf2414Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi198InputQChi innerPair66Input
    leaf2414InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2414LowerChecked :
    lowerCheck 24 leaf2414Box leaf2414Inputs = true := by
  rfl'

private theorem leaf2414CoversExact : CoversExact 8
    leaf2414Box leaf2414Certificate leaf2414InnerLog leaf2414Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi198RoundedFacts
    innerPair66RoundedFacts leaf2414RoundedFacts (by rfl)

private theorem leaf2414FlatSound : Sound leaf2414Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2414CertificateValid
    leaf2414InnerLogValid leaf2414CoversExact leaf2414LowerChecked

private noncomputable def leaf2415Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf2415Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270281216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1877458479/1073741824) }, upper := { exponent := 0, mantissa := (113/64) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541050311/30540562432) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2415InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2415LocalValidity :
    LeafFacts leaf2415Box leaf2415Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2415Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270281216) }) = true
      norm_num [leaf2415Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2415CertificateValid :
    WideCertificateValid leaf2415Box leaf2415Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi198ValidityFacts
    leaf2415LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2415CoverageChecked :
    coverageCheck (innerAD leaf2415Box) leaf2415InnerLog = true := by
  rfl'

private theorem leaf2415InnerLogValid :
    leaf2415InnerLog.Valid 8 (innerAD leaf2415Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2415CoverageChecked

private noncomputable def leaf2415InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2415InputLogOnePlusV_eq :
    leaf2415InputLogOnePlusV = outerEnclosure 24
      (leaf2415Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2415RoundedFacts : LeafRoundedFacts 8
    leaf2415Certificate.logOnePlusV leaf2415InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2415InputLogOnePlusV_eq }

private noncomputable def leaf2415Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi198InputQChi innerPair66Input
    leaf2415InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2415LowerChecked :
    lowerCheck 24 leaf2415Box leaf2415Inputs = true := by
  rfl'

private theorem leaf2415CoversExact : CoversExact 8
    leaf2415Box leaf2415Certificate leaf2415InnerLog leaf2415Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi198RoundedFacts
    innerPair66RoundedFacts leaf2415RoundedFacts (by rfl)

private theorem leaf2415FlatSound : Sound leaf2415Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2415CertificateValid
    leaf2415InnerLogValid leaf2415CoversExact leaf2415LowerChecked

private noncomputable def component51Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component51Node0_sound : Sound component51Node0Box :=
  sound_of_literal_split component51Node0Box leaf2352Box leaf2353Box
    .k (217/64) (by rfl) (by rfl)
    leaf2352FlatSound leaf2353FlatSound

private noncomputable def component51Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node1_sound : Sound component51Node1Box :=
  sound_of_literal_split component51Node1Box leaf2354Box leaf2355Box
    .k (217/64) (by rfl) (by rfl)
    leaf2354FlatSound leaf2355FlatSound

private noncomputable def component51Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node2_sound : Sound component51Node2Box :=
  sound_of_literal_split component51Node2Box component51Node0Box component51Node1Box
    .chi (49/256) (by rfl) (by rfl)
    component51Node0_sound component51Node1_sound

private noncomputable def component51Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component51Node3_sound : Sound component51Node3Box :=
  sound_of_literal_split component51Node3Box leaf2356Box leaf2357Box
    .k (219/64) (by rfl) (by rfl)
    leaf2356FlatSound leaf2357FlatSound

private noncomputable def component51Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node4_sound : Sound component51Node4Box :=
  sound_of_literal_split component51Node4Box leaf2358Box leaf2359Box
    .k (219/64) (by rfl) (by rfl)
    leaf2358FlatSound leaf2359FlatSound

private noncomputable def component51Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node5_sound : Sound component51Node5Box :=
  sound_of_literal_split component51Node5Box component51Node3Box component51Node4Box
    .chi (49/256) (by rfl) (by rfl)
    component51Node3_sound component51Node4_sound

private noncomputable def component51Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node6_sound : Sound component51Node6Box :=
  sound_of_literal_split component51Node6Box component51Node2Box component51Node5Box
    .k (109/32) (by rfl) (by rfl)
    component51Node2_sound component51Node5_sound

private noncomputable def component51Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node7_sound : Sound component51Node7Box :=
  sound_of_literal_split component51Node7Box leaf2360Box leaf2361Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2360FlatSound leaf2361FlatSound

private noncomputable def component51Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node8_sound : Sound component51Node8Box :=
  sound_of_literal_split component51Node8Box leaf2362Box leaf2363Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2362FlatSound leaf2363FlatSound

private noncomputable def component51Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node9_sound : Sound component51Node9Box :=
  sound_of_literal_split component51Node9Box component51Node7Box component51Node8Box
    .k (217/64) (by rfl) (by rfl)
    component51Node7_sound component51Node8_sound

private noncomputable def component51Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node10_sound : Sound component51Node10Box :=
  sound_of_literal_split component51Node10Box leaf2364Box leaf2365Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2364FlatSound leaf2365FlatSound

private noncomputable def component51Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node11_sound : Sound component51Node11Box :=
  sound_of_literal_split component51Node11Box leaf2366Box leaf2367Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2366FlatSound leaf2367FlatSound

private noncomputable def component51Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node12_sound : Sound component51Node12Box :=
  sound_of_literal_split component51Node12Box component51Node10Box component51Node11Box
    .k (219/64) (by rfl) (by rfl)
    component51Node10_sound component51Node11_sound

private noncomputable def component51Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node13_sound : Sound component51Node13Box :=
  sound_of_literal_split component51Node13Box component51Node9Box component51Node12Box
    .k (109/32) (by rfl) (by rfl)
    component51Node9_sound component51Node12_sound

private noncomputable def component51Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node14_sound : Sound component51Node14Box :=
  sound_of_literal_split component51Node14Box component51Node6Box component51Node13Box
    .chi (25/128) (by rfl) (by rfl)
    component51Node6_sound component51Node13_sound

private noncomputable def component51Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component51Node15_sound : Sound component51Node15Box :=
  sound_of_literal_split component51Node15Box leaf2368Box leaf2369Box
    .k (221/64) (by rfl) (by rfl)
    leaf2368FlatSound leaf2369FlatSound

private noncomputable def component51Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node16_sound : Sound component51Node16Box :=
  sound_of_literal_split component51Node16Box leaf2370Box leaf2371Box
    .k (221/64) (by rfl) (by rfl)
    leaf2370FlatSound leaf2371FlatSound

private noncomputable def component51Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node17_sound : Sound component51Node17Box :=
  sound_of_literal_split component51Node17Box component51Node15Box component51Node16Box
    .chi (49/256) (by rfl) (by rfl)
    component51Node15_sound component51Node16_sound

private noncomputable def component51Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component51Node18_sound : Sound component51Node18Box :=
  sound_of_literal_split component51Node18Box leaf2372Box leaf2373Box
    .k (223/64) (by rfl) (by rfl)
    leaf2372FlatSound leaf2373FlatSound

private noncomputable def component51Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node19_sound : Sound component51Node19Box :=
  sound_of_literal_split component51Node19Box leaf2374Box leaf2375Box
    .k (223/64) (by rfl) (by rfl)
    leaf2374FlatSound leaf2375FlatSound

private noncomputable def component51Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node20_sound : Sound component51Node20Box :=
  sound_of_literal_split component51Node20Box component51Node18Box component51Node19Box
    .chi (49/256) (by rfl) (by rfl)
    component51Node18_sound component51Node19_sound

private noncomputable def component51Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node21_sound : Sound component51Node21Box :=
  sound_of_literal_split component51Node21Box component51Node17Box component51Node20Box
    .k (111/32) (by rfl) (by rfl)
    component51Node17_sound component51Node20_sound

private noncomputable def component51Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node22_sound : Sound component51Node22Box :=
  sound_of_literal_split component51Node22Box leaf2376Box leaf2377Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2376FlatSound leaf2377FlatSound

private noncomputable def component51Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node23_sound : Sound component51Node23Box :=
  sound_of_literal_split component51Node23Box leaf2378Box leaf2379Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2378FlatSound leaf2379FlatSound

private noncomputable def component51Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node24_sound : Sound component51Node24Box :=
  sound_of_literal_split component51Node24Box component51Node22Box component51Node23Box
    .k (221/64) (by rfl) (by rfl)
    component51Node22_sound component51Node23_sound

private noncomputable def component51Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node25_sound : Sound component51Node25Box :=
  sound_of_literal_split component51Node25Box leaf2380Box leaf2381Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2380FlatSound leaf2381FlatSound

private noncomputable def component51Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node26_sound : Sound component51Node26Box :=
  sound_of_literal_split component51Node26Box leaf2382Box leaf2383Box
    .chi (51/256) (by rfl) (by rfl)
    leaf2382FlatSound leaf2383FlatSound

private noncomputable def component51Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node27_sound : Sound component51Node27Box :=
  sound_of_literal_split component51Node27Box component51Node25Box component51Node26Box
    .k (223/64) (by rfl) (by rfl)
    component51Node25_sound component51Node26_sound

private noncomputable def component51Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node28_sound : Sound component51Node28Box :=
  sound_of_literal_split component51Node28Box component51Node24Box component51Node27Box
    .k (111/32) (by rfl) (by rfl)
    component51Node24_sound component51Node27_sound

private noncomputable def component51Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node29_sound : Sound component51Node29Box :=
  sound_of_literal_split component51Node29Box component51Node21Box component51Node28Box
    .chi (25/128) (by rfl) (by rfl)
    component51Node21_sound component51Node28_sound

private noncomputable def component51Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component51Node30_sound : Sound component51Node30Box :=
  sound_of_literal_split component51Node30Box component51Node14Box component51Node29Box
    .k (55/16) (by rfl) (by rfl)
    component51Node14_sound component51Node29_sound

private noncomputable def component51Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node31_sound : Sound component51Node31Box :=
  sound_of_literal_split component51Node31Box leaf2384Box leaf2385Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2384FlatSound leaf2385FlatSound

private noncomputable def component51Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node32_sound : Sound component51Node32Box :=
  sound_of_literal_split component51Node32Box leaf2386Box leaf2387Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2386FlatSound leaf2387FlatSound

private noncomputable def component51Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node33_sound : Sound component51Node33Box :=
  sound_of_literal_split component51Node33Box component51Node31Box component51Node32Box
    .k (217/64) (by rfl) (by rfl)
    component51Node31_sound component51Node32_sound

private noncomputable def component51Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node34_sound : Sound component51Node34Box :=
  sound_of_literal_split component51Node34Box leaf2388Box leaf2389Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2388FlatSound leaf2389FlatSound

private noncomputable def component51Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node35_sound : Sound component51Node35Box :=
  sound_of_literal_split component51Node35Box leaf2390Box leaf2391Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2390FlatSound leaf2391FlatSound

private noncomputable def component51Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node36_sound : Sound component51Node36Box :=
  sound_of_literal_split component51Node36Box component51Node34Box component51Node35Box
    .k (219/64) (by rfl) (by rfl)
    component51Node34_sound component51Node35_sound

private noncomputable def component51Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node37_sound : Sound component51Node37Box :=
  sound_of_literal_split component51Node37Box component51Node33Box component51Node36Box
    .k (109/32) (by rfl) (by rfl)
    component51Node33_sound component51Node36_sound

private noncomputable def component51Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node38_sound : Sound component51Node38Box :=
  sound_of_literal_split component51Node38Box leaf2392Box leaf2393Box
    .chi (55/256) (by rfl) (by rfl)
    leaf2392FlatSound leaf2393FlatSound

private noncomputable def component51Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node39_sound : Sound component51Node39Box :=
  sound_of_literal_split component51Node39Box leaf2394Box leaf2395Box
    .chi (55/256) (by rfl) (by rfl)
    leaf2394FlatSound leaf2395FlatSound

private noncomputable def component51Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node40_sound : Sound component51Node40Box :=
  sound_of_literal_split component51Node40Box component51Node38Box component51Node39Box
    .k (217/64) (by rfl) (by rfl)
    component51Node38_sound component51Node39_sound

private noncomputable def component51Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node41_sound : Sound component51Node41Box :=
  sound_of_literal_split component51Node41Box leaf2396Box leaf2397Box
    .chi (55/256) (by rfl) (by rfl)
    leaf2396FlatSound leaf2397FlatSound

private noncomputable def component51Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node42_sound : Sound component51Node42Box :=
  sound_of_literal_split component51Node42Box leaf2398Box leaf2399Box
    .chi (55/256) (by rfl) (by rfl)
    leaf2398FlatSound leaf2399FlatSound

private noncomputable def component51Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node43_sound : Sound component51Node43Box :=
  sound_of_literal_split component51Node43Box component51Node41Box component51Node42Box
    .k (219/64) (by rfl) (by rfl)
    component51Node41_sound component51Node42_sound

private noncomputable def component51Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node44_sound : Sound component51Node44Box :=
  sound_of_literal_split component51Node44Box component51Node40Box component51Node43Box
    .k (109/32) (by rfl) (by rfl)
    component51Node40_sound component51Node43_sound

private noncomputable def component51Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node45_sound : Sound component51Node45Box :=
  sound_of_literal_split component51Node45Box component51Node37Box component51Node44Box
    .chi (27/128) (by rfl) (by rfl)
    component51Node37_sound component51Node44_sound

private noncomputable def component51Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node46_sound : Sound component51Node46Box :=
  sound_of_literal_split component51Node46Box leaf2400Box leaf2401Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2400FlatSound leaf2401FlatSound

private noncomputable def component51Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node47_sound : Sound component51Node47Box :=
  sound_of_literal_split component51Node47Box leaf2402Box leaf2403Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2402FlatSound leaf2403FlatSound

private noncomputable def component51Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node48_sound : Sound component51Node48Box :=
  sound_of_literal_split component51Node48Box component51Node46Box component51Node47Box
    .k (221/64) (by rfl) (by rfl)
    component51Node46_sound component51Node47_sound

private noncomputable def component51Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node49_sound : Sound component51Node49Box :=
  sound_of_literal_split component51Node49Box leaf2404Box leaf2405Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2404FlatSound leaf2405FlatSound

private noncomputable def component51Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node50_sound : Sound component51Node50Box :=
  sound_of_literal_split component51Node50Box leaf2406Box leaf2407Box
    .chi (53/256) (by rfl) (by rfl)
    leaf2406FlatSound leaf2407FlatSound

private noncomputable def component51Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node51_sound : Sound component51Node51Box :=
  sound_of_literal_split component51Node51Box component51Node49Box component51Node50Box
    .k (223/64) (by rfl) (by rfl)
    component51Node49_sound component51Node50_sound

private noncomputable def component51Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component51Node52_sound : Sound component51Node52Box :=
  sound_of_literal_split component51Node52Box component51Node48Box component51Node51Box
    .k (111/32) (by rfl) (by rfl)
    component51Node48_sound component51Node51_sound

private noncomputable def component51Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node53_sound : Sound component51Node53Box :=
  sound_of_literal_split component51Node53Box leaf2408Box leaf2409Box
    .chi (55/256) (by rfl) (by rfl)
    leaf2408FlatSound leaf2409FlatSound

private noncomputable def component51Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node54_sound : Sound component51Node54Box :=
  sound_of_literal_split component51Node54Box leaf2410Box leaf2411Box
    .chi (55/256) (by rfl) (by rfl)
    leaf2410FlatSound leaf2411FlatSound

private noncomputable def component51Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node55_sound : Sound component51Node55Box :=
  sound_of_literal_split component51Node55Box component51Node53Box component51Node54Box
    .k (221/64) (by rfl) (by rfl)
    component51Node53_sound component51Node54_sound

private noncomputable def component51Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component51Node56_sound : Sound component51Node56Box :=
  sound_of_literal_split component51Node56Box leaf2412Box leaf2413Box
    .k (223/64) (by rfl) (by rfl)
    leaf2412FlatSound leaf2413FlatSound

private noncomputable def component51Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node57_sound : Sound component51Node57Box :=
  sound_of_literal_split component51Node57Box leaf2414Box leaf2415Box
    .k (223/64) (by rfl) (by rfl)
    leaf2414FlatSound leaf2415FlatSound

private noncomputable def component51Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node58_sound : Sound component51Node58Box :=
  sound_of_literal_split component51Node58Box component51Node56Box component51Node57Box
    .chi (55/256) (by rfl) (by rfl)
    component51Node56_sound component51Node57_sound

private noncomputable def component51Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node59_sound : Sound component51Node59Box :=
  sound_of_literal_split component51Node59Box component51Node55Box component51Node58Box
    .k (111/32) (by rfl) (by rfl)
    component51Node55_sound component51Node58_sound

private noncomputable def component51Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node60_sound : Sound component51Node60Box :=
  sound_of_literal_split component51Node60Box component51Node52Box component51Node59Box
    .chi (27/128) (by rfl) (by rfl)
    component51Node52_sound component51Node59_sound

private noncomputable def component51Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component51Node61_sound : Sound component51Node61Box :=
  sound_of_literal_split component51Node61Box component51Node45Box component51Node60Box
    .k (55/16) (by rfl) (by rfl)
    component51Node45_sound component51Node60_sound

noncomputable def component51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component51_sound : Sound component51Box :=
  sound_of_literal_split component51Box component51Node30Box component51Node61Box
    .chi (13/64) (by rfl) (by rfl)
    component51Node30_sound component51Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
