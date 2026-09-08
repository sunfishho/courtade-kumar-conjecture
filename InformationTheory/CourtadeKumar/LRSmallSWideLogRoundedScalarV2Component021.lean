import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf871Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf871Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553483) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (190804439/134217728) }, upper := { exponent := 0, mantissa := (2997/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67107947/67106966) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf871InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf871LocalValidity :
    LeafFacts leaf871Box leaf871Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf871Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553483) }) = true
      norm_num [leaf871Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf871CertificateValid :
    WideCertificateValid leaf871Box leaf871Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi34ValidityFacts
    leaf871LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf871CoverageChecked :
    coverageCheck (innerAD leaf871Box) leaf871InnerLog = true := by
  rfl'

private theorem leaf871InnerLogValid :
    leaf871InnerLog.Valid 8 (innerAD leaf871Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf871CoverageChecked

private noncomputable def leaf871InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf871InputLogOnePlusV_eq :
    leaf871InputLogOnePlusV = outerEnclosure 24
      (leaf871Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf871RoundedFacts : LeafRoundedFacts 8
    leaf871Certificate.logOnePlusV leaf871InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf871InputLogOnePlusV_eq }

private noncomputable def leaf871Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi34InputQChi innerPair27Input
    leaf871InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf871LowerChecked :
    lowerCheck 24 leaf871Box leaf871Inputs = true := by
  rfl'

private theorem leaf871CoversExact : CoversExact 8
    leaf871Box leaf871Certificate leaf871InnerLog leaf871Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi34RoundedFacts
    innerPair27RoundedFacts leaf871RoundedFacts (by rfl)

private theorem leaf871FlatSound : Sound leaf871Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf871CertificateValid
    leaf871InnerLogValid leaf871CoversExact leaf871LowerChecked

private noncomputable def leaf872Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf872Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776735) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (191590821/134217728) }, upper := { exponent := 0, mantissa := (1505/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33553967/33553470) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf872InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf872LocalValidity :
    LeafFacts leaf872Box leaf872Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf872Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776735) }) = true
      norm_num [leaf872Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf872CertificateValid :
    WideCertificateValid leaf872Box leaf872Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi34ValidityFacts
    leaf872LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf872CoverageChecked :
    coverageCheck (innerAD leaf872Box) leaf872InnerLog = true := by
  rfl'

private theorem leaf872InnerLogValid :
    leaf872InnerLog.Valid 8 (innerAD leaf872Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf872CoverageChecked

private noncomputable def leaf872InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf872InputLogOnePlusV_eq :
    leaf872InputLogOnePlusV = outerEnclosure 24
      (leaf872Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf872RoundedFacts : LeafRoundedFacts 8
    leaf872Certificate.logOnePlusV leaf872InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf872InputLogOnePlusV_eq }

private noncomputable def leaf872Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi34InputQChi innerPair27Input
    leaf872InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf872LowerChecked :
    lowerCheck 24 leaf872Box leaf872Inputs = true := by
  rfl'

private theorem leaf872CoversExact : CoversExact 8
    leaf872Box leaf872Certificate leaf872InnerLog leaf872Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi34RoundedFacts
    innerPair27RoundedFacts leaf872RoundedFacts (by rfl)

private theorem leaf872FlatSound : Sound leaf872Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf872CertificateValid
    leaf872InnerLogValid leaf872CoversExact leaf872LowerChecked

private noncomputable def leaf873Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf873Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (269484289/269479936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (195522741/134217728) }, upper := { exponent := 0, mantissa := (1535/1024) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (538964225/538959872) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf873InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf873LocalValidity :
    LeafFacts leaf873Box leaf873Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf873Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (269484289/269479936) }) = true
      norm_num [leaf873Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf873CertificateValid :
    WideCertificateValid leaf873Box leaf873Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi35ValidityFacts
    leaf873LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf873CoverageChecked :
    coverageCheck (innerAD leaf873Box) leaf873InnerLog = true := by
  rfl'

private theorem leaf873InnerLogValid :
    leaf873InnerLog.Valid 8 (innerAD leaf873Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf873CoverageChecked

private noncomputable def leaf873InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf873InputLogOnePlusV_eq :
    leaf873InputLogOnePlusV = outerEnclosure 24
      (leaf873Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf873RoundedFacts : LeafRoundedFacts 8
    leaf873Certificate.logOnePlusV leaf873InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf873InputLogOnePlusV_eq }

private noncomputable def leaf873Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi35InputQChi innerPair34Input
    leaf873InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf873LowerChecked :
    lowerCheck 24 leaf873Box leaf873Inputs = true := by
  rfl'

private theorem leaf873CoversExact : CoversExact 8
    leaf873Box leaf873Certificate leaf873InnerLog leaf873Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi35RoundedFacts
    innerPair34RoundedFacts leaf873RoundedFacts (by rfl)

private theorem leaf873FlatSound : Sound leaf873Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf873CertificateValid
    leaf873InnerLogValid leaf873CoversExact leaf873LowerChecked

private noncomputable def leaf874Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf874Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717355008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (196374655/134217728) }, upper := { exponent := 0, mantissa := (771/512) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435848703/137434710016) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf874InnerLog : WideLogData :=
  innerPair148Data

set_option maxRecDepth 1000000 in
private theorem leaf874LocalValidity :
    LeafFacts leaf874Box leaf874Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf874Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717355008) }) = true
      norm_num [leaf874Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf874CertificateValid :
    WideCertificateValid leaf874Box leaf874Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi35ValidityFacts
    leaf874LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf874CoverageChecked :
    coverageCheck (innerAD leaf874Box) leaf874InnerLog = true := by
  rfl'

private theorem leaf874InnerLogValid :
    leaf874InnerLog.Valid 8 (innerAD leaf874Box) :=
  wideLogDataValid_of_cachedCheck endpoint41PositiveFacts
    endpoint49PositiveFacts.valid leaf874CoverageChecked

private noncomputable def leaf874InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf874InputLogOnePlusV_eq :
    leaf874InputLogOnePlusV = outerEnclosure 24
      (leaf874Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf874RoundedFacts : LeafRoundedFacts 8
    leaf874Certificate.logOnePlusV leaf874InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf874InputLogOnePlusV_eq }

private noncomputable def leaf874Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi35InputQChi innerPair148Input
    leaf874InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf874LowerChecked :
    lowerCheck 24 leaf874Box leaf874Inputs = true := by
  rfl'

private theorem leaf874CoversExact : CoversExact 8
    leaf874Box leaf874Certificate leaf874InnerLog leaf874Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi35RoundedFacts
    innerPair148RoundedFacts leaf874RoundedFacts (by rfl)

private theorem leaf874FlatSound : Sound leaf874Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf874CertificateValid
    leaf874InnerLogValid leaf874CoversExact leaf874LowerChecked

private noncomputable def leaf875Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf875Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553457) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (192377203/134217728) }, upper := { exponent := 0, mantissa := (3023/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67107921/67106914) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf875InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf875LocalValidity :
    LeafFacts leaf875Box leaf875Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf875Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553457) }) = true
      norm_num [leaf875Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf875CertificateValid :
    WideCertificateValid leaf875Box leaf875Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi34ValidityFacts
    leaf875LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf875CoverageChecked :
    coverageCheck (innerAD leaf875Box) leaf875InnerLog = true := by
  rfl'

private theorem leaf875InnerLogValid :
    leaf875InnerLog.Valid 8 (innerAD leaf875Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf875CoverageChecked

private noncomputable def leaf875InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf875InputLogOnePlusV_eq :
    leaf875InputLogOnePlusV = outerEnclosure 24
      (leaf875Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf875RoundedFacts : LeafRoundedFacts 8
    leaf875Certificate.logOnePlusV leaf875InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf875InputLogOnePlusV_eq }

private noncomputable def leaf875Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi34InputQChi innerPair27Input
    leaf875InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf875LowerChecked :
    lowerCheck 24 leaf875Box leaf875Inputs = true := by
  rfl'

private theorem leaf875CoversExact : CoversExact 8
    leaf875Box leaf875Certificate leaf875InnerLog leaf875Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi34RoundedFacts
    innerPair27RoundedFacts leaf875RoundedFacts (by rfl)

private theorem leaf875FlatSound : Sound leaf875Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf875CertificateValid
    leaf875InnerLogValid leaf875CoversExact leaf875LowerChecked

private noncomputable def leaf876Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf876Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (493448/493433) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (193163585/134217728) }, upper := { exponent := 0, mantissa := (759/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (986881/986866) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf876InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf876LocalValidity :
    LeafFacts leaf876Box leaf876Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf876Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (493448/493433) }) = true
      norm_num [leaf876Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf876CertificateValid :
    WideCertificateValid leaf876Box leaf876Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi34ValidityFacts
    leaf876LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf876CoverageChecked :
    coverageCheck (innerAD leaf876Box) leaf876InnerLog = true := by
  rfl'

private theorem leaf876InnerLogValid :
    leaf876InnerLog.Valid 8 (innerAD leaf876Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf876CoverageChecked

private noncomputable def leaf876InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf876InputLogOnePlusV_eq :
    leaf876InputLogOnePlusV = outerEnclosure 24
      (leaf876Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf876RoundedFacts : LeafRoundedFacts 8
    leaf876Certificate.logOnePlusV leaf876InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf876InputLogOnePlusV_eq }

private noncomputable def leaf876Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi34InputQChi innerPair34Input
    leaf876InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf876LowerChecked :
    lowerCheck 24 leaf876Box leaf876Inputs = true := by
  rfl'

private theorem leaf876CoversExact : CoversExact 8
    leaf876Box leaf876Certificate leaf876InnerLog leaf876Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi34RoundedFacts
    innerPair34RoundedFacts leaf876RoundedFacts (by rfl)

private theorem leaf876FlatSound : Sound leaf876Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf876CertificateValid
    leaf876InnerLogValid leaf876CoversExact leaf876LowerChecked

private noncomputable def leaf877Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf877Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717326336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (197226569/134217728) }, upper := { exponent := 0, mantissa := (1549/1024) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435820031/137434652672) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf877InnerLog : WideLogData :=
  innerPair153Data

set_option maxRecDepth 1000000 in
private theorem leaf877LocalValidity :
    LeafFacts leaf877Box leaf877Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf877Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717326336) }) = true
      norm_num [leaf877Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf877CertificateValid :
    WideCertificateValid leaf877Box leaf877Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi35ValidityFacts
    leaf877LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf877CoverageChecked :
    coverageCheck (innerAD leaf877Box) leaf877InnerLog = true := by
  rfl'

private theorem leaf877InnerLogValid :
    leaf877InnerLog.Valid 8 (innerAD leaf877Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint49PositiveFacts.valid leaf877CoverageChecked

private noncomputable def leaf877InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf877InputLogOnePlusV_eq :
    leaf877InputLogOnePlusV = outerEnclosure 24
      (leaf877Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf877RoundedFacts : LeafRoundedFacts 8
    leaf877Certificate.logOnePlusV leaf877InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf877InputLogOnePlusV_eq }

private noncomputable def leaf877Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi35InputQChi innerPair153Input
    leaf877InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf877LowerChecked :
    lowerCheck 24 leaf877Box leaf877Inputs = true := by
  rfl'

private theorem leaf877CoversExact : CoversExact 8
    leaf877Box leaf877Certificate leaf877InnerLog leaf877Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi35RoundedFacts
    innerPair153RoundedFacts leaf877RoundedFacts (by rfl)

private theorem leaf877FlatSound : Sound leaf877Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf877CertificateValid
    leaf877InnerLogValid leaf877CoversExact leaf877LowerChecked

private noncomputable def leaf878Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf878Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905765888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (198078483/134217728) }, upper := { exponent := 0, mantissa := (389/256) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811930453/45811531776) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf878InnerLog : WideLogData :=
  innerPair151Data

set_option maxRecDepth 1000000 in
private theorem leaf878LocalValidity :
    LeafFacts leaf878Box leaf878Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf878Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905765888) }) = true
      norm_num [leaf878Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf878CertificateValid :
    WideCertificateValid leaf878Box leaf878Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi35ValidityFacts
    leaf878LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf878CoverageChecked :
    coverageCheck (innerAD leaf878Box) leaf878InnerLog = true := by
  rfl'

private theorem leaf878InnerLogValid :
    leaf878InnerLog.Valid 8 (innerAD leaf878Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint19PositiveFacts.valid leaf878CoverageChecked

private noncomputable def leaf878InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf878InputLogOnePlusV_eq :
    leaf878InputLogOnePlusV = outerEnclosure 24
      (leaf878Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf878RoundedFacts : LeafRoundedFacts 8
    leaf878Certificate.logOnePlusV leaf878InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf878InputLogOnePlusV_eq }

private noncomputable def leaf878Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi35InputQChi innerPair151Input
    leaf878InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf878LowerChecked :
    lowerCheck 24 leaf878Box leaf878Inputs = true := by
  rfl'

private theorem leaf878CoversExact : CoversExact 8
    leaf878Box leaf878Certificate leaf878InnerLog leaf878Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi35RoundedFacts
    innerPair151RoundedFacts leaf878RoundedFacts (by rfl)

private theorem leaf878FlatSound : Sound leaf878Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf878CertificateValid
    leaf878InnerLogValid leaf878CoversExact leaf878LowerChecked

private noncomputable def leaf879Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf879Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717234176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (200241043/134217728) }, upper := { exponent := 0, mantissa := (3143/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435727871/137434468352) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf879InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf879LocalValidity :
    LeafFacts leaf879Box leaf879Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf879Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717234176) }) = true
      norm_num [leaf879Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf879CertificateValid :
    WideCertificateValid leaf879Box leaf879Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi44ValidityFacts
    leaf879LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf879CoverageChecked :
    coverageCheck (innerAD leaf879Box) leaf879InnerLog = true := by
  rfl'

private theorem leaf879InnerLogValid :
    leaf879InnerLog.Valid 8 (innerAD leaf879Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf879CoverageChecked

private noncomputable def leaf879InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf879InputLogOnePlusV_eq :
    leaf879InputLogOnePlusV = outerEnclosure 24
      (leaf879Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf879RoundedFacts : LeafRoundedFacts 8
    leaf879Certificate.logOnePlusV leaf879InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf879InputLogOnePlusV_eq }

private noncomputable def leaf879Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi44InputQChi innerPair35Input
    leaf879InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf879LowerChecked :
    lowerCheck 24 leaf879Box leaf879Inputs = true := by
  rfl'

private theorem leaf879CoversExact : CoversExact 8
    leaf879Box leaf879Certificate leaf879InnerLog leaf879Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi44RoundedFacts
    innerPair35RoundedFacts leaf879RoundedFacts (by rfl)

private theorem leaf879FlatSound : Sound leaf879Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf879CertificateValid
    leaf879InnerLogValid leaf879CoversExact leaf879LowerChecked

private noncomputable def leaf880Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf880Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717203456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (201158489/134217728) }, upper := { exponent := 0, mantissa := (1579/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435697151/137434406912) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf880InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf880LocalValidity :
    LeafFacts leaf880Box leaf880Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf880Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717203456) }) = true
      norm_num [leaf880Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf880CertificateValid :
    WideCertificateValid leaf880Box leaf880Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi44ValidityFacts
    leaf880LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf880CoverageChecked :
    coverageCheck (innerAD leaf880Box) leaf880InnerLog = true := by
  rfl'

private theorem leaf880InnerLogValid :
    leaf880InnerLog.Valid 8 (innerAD leaf880Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf880CoverageChecked

private noncomputable def leaf880InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf880InputLogOnePlusV_eq :
    leaf880InputLogOnePlusV = outerEnclosure 24
      (leaf880Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf880RoundedFacts : LeafRoundedFacts 8
    leaf880Certificate.logOnePlusV leaf880InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf880InputLogOnePlusV_eq }

private noncomputable def leaf880Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi44InputQChi innerPair35Input
    leaf880InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf880LowerChecked :
    lowerCheck 24 leaf880Box leaf880Inputs = true := by
  rfl'

private theorem leaf880CoversExact : CoversExact 8
    leaf880Box leaf880Certificate leaf880InnerLog leaf880Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi44RoundedFacts
    innerPair35RoundedFacts leaf880RoundedFacts (by rfl)

private theorem leaf880FlatSound : Sound leaf880Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf880CertificateValid
    leaf880InnerLogValid leaf880CoversExact leaf880LowerChecked

private noncomputable def leaf881Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf881Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717084672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (204959345/134217728) }, upper := { exponent := 0, mantissa := (201/128) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435578367/137434169344) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf881InnerLog : WideLogData :=
  innerPair178Data

set_option maxRecDepth 1000000 in
private theorem leaf881LocalValidity :
    LeafFacts leaf881Box leaf881Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf881Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717084672) }) = true
      norm_num [leaf881Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf881CertificateValid :
    WideCertificateValid leaf881Box leaf881Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi45ValidityFacts
    leaf881LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf881CoverageChecked :
    coverageCheck (innerAD leaf881Box) leaf881InnerLog = true := by
  rfl'

private theorem leaf881InnerLogValid :
    leaf881InnerLog.Valid 8 (innerAD leaf881Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint47PositiveFacts.valid leaf881CoverageChecked

private noncomputable def leaf881InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf881InputLogOnePlusV_eq :
    leaf881InputLogOnePlusV = outerEnclosure 24
      (leaf881Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf881RoundedFacts : LeafRoundedFacts 8
    leaf881Certificate.logOnePlusV leaf881InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf881InputLogOnePlusV_eq }

private noncomputable def leaf881Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi45InputQChi innerPair178Input
    leaf881InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf881LowerChecked :
    lowerCheck 24 leaf881Box leaf881Inputs = true := by
  rfl'

private theorem leaf881CoversExact : CoversExact 8
    leaf881Box leaf881Certificate leaf881InnerLog leaf881Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi45RoundedFacts
    innerPair178RoundedFacts leaf881RoundedFacts (by rfl)

private theorem leaf881FlatSound : Sound leaf881Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf881CertificateValid
    leaf881InnerLogValid leaf881CoversExact leaf881LowerChecked

private noncomputable def leaf882Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf882Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905683968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (205942323/134217728) }, upper := { exponent := 0, mantissa := (101/64) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811848533/45811367936) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf882InnerLog : WideLogData :=
  innerPair87Data

set_option maxRecDepth 1000000 in
private theorem leaf882LocalValidity :
    LeafFacts leaf882Box leaf882Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf882Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905683968) }) = true
      norm_num [leaf882Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf882CertificateValid :
    WideCertificateValid leaf882Box leaf882Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi45ValidityFacts
    leaf882LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf882CoverageChecked :
    coverageCheck (innerAD leaf882Box) leaf882InnerLog = true := by
  rfl'

private theorem leaf882InnerLogValid :
    leaf882InnerLog.Valid 8 (innerAD leaf882Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint47PositiveFacts.valid leaf882CoverageChecked

private noncomputable def leaf882InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf882InputLogOnePlusV_eq :
    leaf882InputLogOnePlusV = outerEnclosure 24
      (leaf882Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf882RoundedFacts : LeafRoundedFacts 8
    leaf882Certificate.logOnePlusV leaf882InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf882InputLogOnePlusV_eq }

private noncomputable def leaf882Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi45InputQChi innerPair87Input
    leaf882InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf882LowerChecked :
    lowerCheck 24 leaf882Box leaf882Inputs = true := by
  rfl'

private theorem leaf882CoversExact : CoversExact 8
    leaf882Box leaf882Certificate leaf882InnerLog leaf882Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi45RoundedFacts
    innerPair87RoundedFacts leaf882RoundedFacts (by rfl)

private theorem leaf882FlatSound : Sound leaf882Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf882CertificateValid
    leaf882InnerLogValid leaf882CoversExact leaf882LowerChecked

private noncomputable def leaf883Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf883Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717172736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (202075935/134217728) }, upper := { exponent := 0, mantissa := (3173/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435666431/137434345472) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf883InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf883LocalValidity :
    LeafFacts leaf883Box leaf883Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf883Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717172736) }) = true
      norm_num [leaf883Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf883CertificateValid :
    WideCertificateValid leaf883Box leaf883Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi44ValidityFacts
    leaf883LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf883CoverageChecked :
    coverageCheck (innerAD leaf883Box) leaf883InnerLog = true := by
  rfl'

private theorem leaf883InnerLogValid :
    leaf883InnerLog.Valid 8 (innerAD leaf883Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf883CoverageChecked

private noncomputable def leaf883InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf883InputLogOnePlusV_eq :
    leaf883InputLogOnePlusV = outerEnclosure 24
      (leaf883Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf883RoundedFacts : LeafRoundedFacts 8
    leaf883Certificate.logOnePlusV leaf883InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf883InputLogOnePlusV_eq }

private noncomputable def leaf883Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi44InputQChi innerPair40Input
    leaf883InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf883LowerChecked :
    lowerCheck 24 leaf883Box leaf883Inputs = true := by
  rfl'

private theorem leaf883CoversExact : CoversExact 8
    leaf883Box leaf883Certificate leaf883InnerLog leaf883Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi44RoundedFacts
    innerPair40RoundedFacts leaf883RoundedFacts (by rfl)

private theorem leaf883FlatSound : Sound leaf883Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf883CertificateValid
    leaf883InnerLogValid leaf883CoversExact leaf883LowerChecked

private noncomputable def leaf884Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf884Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717142016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (202993381/134217728) }, upper := { exponent := 0, mantissa := (797/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435635711/137434284032) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf884InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf884LocalValidity :
    LeafFacts leaf884Box leaf884Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf884Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717142016) }) = true
      norm_num [leaf884Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf884CertificateValid :
    WideCertificateValid leaf884Box leaf884Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi44ValidityFacts
    leaf884LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf884CoverageChecked :
    coverageCheck (innerAD leaf884Box) leaf884InnerLog = true := by
  rfl'

private theorem leaf884InnerLogValid :
    leaf884InnerLog.Valid 8 (innerAD leaf884Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf884CoverageChecked

private noncomputable def leaf884InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf884InputLogOnePlusV_eq :
    leaf884InputLogOnePlusV = outerEnclosure 24
      (leaf884Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf884RoundedFacts : LeafRoundedFacts 8
    leaf884Certificate.logOnePlusV leaf884InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf884InputLogOnePlusV_eq }

private noncomputable def leaf884Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi44InputQChi innerPair40Input
    leaf884InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf884LowerChecked :
    lowerCheck 24 leaf884Box leaf884Inputs = true := by
  rfl'

private theorem leaf884CoversExact : CoversExact 8
    leaf884Box leaf884Certificate leaf884InnerLog leaf884Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi44RoundedFacts
    innerPair40RoundedFacts leaf884RoundedFacts (by rfl)

private theorem leaf884FlatSound : Sound leaf884Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf884CertificateValid
    leaf884InnerLogValid leaf884CoversExact leaf884LowerChecked

private noncomputable def leaf885Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf885Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717019136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (206925301/134217728) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435512831/137434038272) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf885InnerLog : WideLogData :=
  innerPair85Data

set_option maxRecDepth 1000000 in
private theorem leaf885LocalValidity :
    LeafFacts leaf885Box leaf885Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf885Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717019136) }) = true
      norm_num [leaf885Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf885CertificateValid :
    WideCertificateValid leaf885Box leaf885Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi45ValidityFacts
    leaf885LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf885CoverageChecked :
    coverageCheck (innerAD leaf885Box) leaf885InnerLog = true := by
  rfl'

private theorem leaf885InnerLogValid :
    leaf885InnerLog.Valid 8 (innerAD leaf885Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint44PositiveFacts.valid leaf885CoverageChecked

private noncomputable def leaf885InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf885InputLogOnePlusV_eq :
    leaf885InputLogOnePlusV = outerEnclosure 24
      (leaf885Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf885RoundedFacts : LeafRoundedFacts 8
    leaf885Certificate.logOnePlusV leaf885InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf885InputLogOnePlusV_eq }

private noncomputable def leaf885Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi45InputQChi innerPair85Input
    leaf885InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf885LowerChecked :
    lowerCheck 24 leaf885Box leaf885Inputs = true := by
  rfl'

private theorem leaf885CoversExact : CoversExact 8
    leaf885Box leaf885Certificate leaf885InnerLog leaf885Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi45RoundedFacts
    innerPair85RoundedFacts leaf885RoundedFacts (by rfl)

private theorem leaf885FlatSound : Sound leaf885Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf885CertificateValid
    leaf885InnerLogValid leaf885CoversExact leaf885LowerChecked

private noncomputable def leaf886Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf886Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217911/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716986368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (207908279/134217728) }, upper := { exponent := 0, mantissa := (51/32) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435480063/137433972736) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf886InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf886LocalValidity :
    LeafFacts leaf886Box leaf886Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf886Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716986368) }) = true
      norm_num [leaf886Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf886CertificateValid :
    WideCertificateValid leaf886Box leaf886Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi45ValidityFacts
    leaf886LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf886CoverageChecked :
    coverageCheck (innerAD leaf886Box) leaf886InnerLog = true := by
  rfl'

private theorem leaf886InnerLogValid :
    leaf886InnerLog.Valid 8 (innerAD leaf886Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf886CoverageChecked

private noncomputable def leaf886InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf886InputLogOnePlusV_eq :
    leaf886InputLogOnePlusV = outerEnclosure 24
      (leaf886Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf886RoundedFacts : LeafRoundedFacts 8
    leaf886Certificate.logOnePlusV leaf886InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf886InputLogOnePlusV_eq }

private noncomputable def leaf886Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi45InputQChi innerPair154Input
    leaf886InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf886LowerChecked :
    lowerCheck 24 leaf886Box leaf886Inputs = true := by
  rfl'

private theorem leaf886CoversExact : CoversExact 8
    leaf886Box leaf886Certificate leaf886InnerLog leaf886Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi45RoundedFacts
    innerPair154RoundedFacts leaf886RoundedFacts (by rfl)

private theorem leaf886FlatSound : Sound leaf886Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf886CertificateValid
    leaf886InnerLogValid leaf886CoversExact leaf886LowerChecked

private noncomputable def leaf887Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf887Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905808896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (193949967/134217728) }, upper := { exponent := 0, mantissa := (3049/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811973461/45811617792) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf887InnerLog : WideLogData :=
  innerPair397Data

set_option maxRecDepth 1000000 in
private theorem leaf887LocalValidity :
    LeafFacts leaf887Box leaf887Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf887Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905808896) }) = true
      norm_num [leaf887Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf887CertificateValid :
    WideCertificateValid leaf887Box leaf887Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi34ValidityFacts
    leaf887LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf887CoverageChecked :
    coverageCheck (innerAD leaf887Box) leaf887InnerLog = true := by
  rfl'

private theorem leaf887InnerLogValid :
    leaf887InnerLog.Valid 8 (innerAD leaf887Box) :=
  wideLogDataValid_of_cachedCheck endpoint109PositiveFacts
    endpoint110PositiveFacts.valid leaf887CoverageChecked

private noncomputable def leaf887InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf887InputLogOnePlusV_eq :
    leaf887InputLogOnePlusV = outerEnclosure 24
      (leaf887Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf887RoundedFacts : LeafRoundedFacts 8
    leaf887Certificate.logOnePlusV leaf887InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf887InputLogOnePlusV_eq }

private noncomputable def leaf887Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi34InputQChi innerPair397Input
    leaf887InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf887LowerChecked :
    lowerCheck 24 leaf887Box leaf887Inputs = true := by
  rfl'

private theorem leaf887CoversExact : CoversExact 8
    leaf887Box leaf887Certificate leaf887InnerLog leaf887Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi34RoundedFacts
    innerPair397RoundedFacts leaf887RoundedFacts (by rfl)

private theorem leaf887FlatSound : Sound leaf887Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf887CertificateValid
    leaf887InnerLogValid leaf887CoversExact leaf887LowerChecked

private noncomputable def leaf888Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf888Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553457) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (389505621/268435456) }, upper := { exponent := 0, mantissa := (3023/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67107921/67106914) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf888InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf888LocalValidity :
    LeafFacts leaf888Box leaf888Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf888Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553457) }) = true
      norm_num [leaf888Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf888CertificateValid :
    WideCertificateValid leaf888Box leaf888Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi115ValidityFacts
    leaf888LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf888CoverageChecked :
    coverageCheck (innerAD leaf888Box) leaf888InnerLog = true := by
  rfl'

private theorem leaf888InnerLogValid :
    leaf888InnerLog.Valid 8 (innerAD leaf888Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf888CoverageChecked

private noncomputable def leaf888InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf888InputLogOnePlusV_eq :
    leaf888InputLogOnePlusV = outerEnclosure 24
      (leaf888Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf888RoundedFacts : LeafRoundedFacts 8
    leaf888Certificate.logOnePlusV leaf888InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf888InputLogOnePlusV_eq }

private noncomputable def leaf888Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi115InputQChi innerPair34Input
    leaf888InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf888LowerChecked :
    lowerCheck 24 leaf888Box leaf888Inputs = true := by
  rfl'

private theorem leaf888CoversExact : CoversExact 8
    leaf888Box leaf888Certificate leaf888InnerLog leaf888Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi115RoundedFacts
    innerPair34RoundedFacts leaf888RoundedFacts (by rfl)

private theorem leaf888FlatSound : Sound leaf888Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf888CertificateValid
    leaf888InnerLogValid leaf888CoversExact leaf888LowerChecked

private noncomputable def leaf889Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf889Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717400064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (394551583/268435456) }, upper := { exponent := 0, mantissa := (1531/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435893759/137434800128) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf889InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf889LocalValidity :
    LeafFacts leaf889Box leaf889Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf889Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717400064) }) = true
      norm_num [leaf889Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf889CertificateValid :
    WideCertificateValid leaf889Box leaf889Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi116ValidityFacts
    leaf889LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf889CoverageChecked :
    coverageCheck (innerAD leaf889Box) leaf889InnerLog = true := by
  rfl'

private theorem leaf889InnerLogValid :
    leaf889InnerLog.Valid 8 (innerAD leaf889Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf889CoverageChecked

private noncomputable def leaf889InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf889InputLogOnePlusV_eq :
    leaf889InputLogOnePlusV = outerEnclosure 24
      (leaf889Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf889RoundedFacts : LeafRoundedFacts 8
    leaf889Certificate.logOnePlusV leaf889InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf889InputLogOnePlusV_eq }

private noncomputable def leaf889Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi116InputQChi innerPair34Input
    leaf889InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf889LowerChecked :
    lowerCheck 24 leaf889Box leaf889Inputs = true := by
  rfl'

private theorem leaf889CoversExact : CoversExact 8
    leaf889Box leaf889Certificate leaf889InnerLog leaf889Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi116RoundedFacts
    innerPair34RoundedFacts leaf889RoundedFacts (by rfl)

private theorem leaf889FlatSound : Sound leaf889Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf889CertificateValid
    leaf889InnerLogValid leaf889CoversExact leaf889LowerChecked

private noncomputable def leaf890Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf890Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217909/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717268992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (198930397/134217728) }, upper := { exponent := 0, mantissa := (1563/1024) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435762687/137434537984) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf890InnerLog : WideLogData :=
  innerPair398Data

set_option maxRecDepth 1000000 in
private theorem leaf890LocalValidity :
    LeafFacts leaf890Box leaf890Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf890Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717268992) }) = true
      norm_num [leaf890Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf890CertificateValid :
    WideCertificateValid leaf890Box leaf890Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi35ValidityFacts
    leaf890LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf890CoverageChecked :
    coverageCheck (innerAD leaf890Box) leaf890InnerLog = true := by
  rfl'

private theorem leaf890InnerLogValid :
    leaf890InnerLog.Valid 8 (innerAD leaf890Box) :=
  wideLogDataValid_of_cachedCheck endpoint111PositiveFacts
    endpoint112PositiveFacts.valid leaf890CoverageChecked

private noncomputable def leaf890InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf890InputLogOnePlusV_eq :
    leaf890InputLogOnePlusV = outerEnclosure 24
      (leaf890Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf890RoundedFacts : LeafRoundedFacts 8
    leaf890Certificate.logOnePlusV leaf890InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf890InputLogOnePlusV_eq }

private noncomputable def leaf890Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi35InputQChi innerPair398Input
    leaf890InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf890LowerChecked :
    lowerCheck 24 leaf890Box leaf890Inputs = true := by
  rfl'

private theorem leaf890CoversExact : CoversExact 8
    leaf890Box leaf890Certificate leaf890InnerLog leaf890Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi35RoundedFacts
    innerPair398RoundedFacts leaf890RoundedFacts (by rfl)

private theorem leaf890FlatSound : Sound leaf890Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf890CertificateValid
    leaf890InnerLogValid leaf890CoversExact leaf890LowerChecked

private noncomputable def leaf891Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf891Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435665/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717320192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (399597545/268435456) }, upper := { exponent := 0, mantissa := (3101/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435813887/137434640384) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf891InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf891LocalValidity :
    LeafFacts leaf891Box leaf891Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf891Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717320192) }) = true
      norm_num [leaf891Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf891CertificateValid :
    WideCertificateValid leaf891Box leaf891Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi117ValidityFacts
    leaf891LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf891CoverageChecked :
    coverageCheck (innerAD leaf891Box) leaf891InnerLog = true := by
  rfl'

private theorem leaf891InnerLogValid :
    leaf891InnerLog.Valid 8 (innerAD leaf891Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf891CoverageChecked

private noncomputable def leaf891InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf891InputLogOnePlusV_eq :
    leaf891InputLogOnePlusV = outerEnclosure 24
      (leaf891Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf891RoundedFacts : LeafRoundedFacts 8
    leaf891Certificate.logOnePlusV leaf891InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf891InputLogOnePlusV_eq }

private noncomputable def leaf891Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi117InputQChi innerPair35Input
    leaf891InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf891LowerChecked :
    lowerCheck 24 leaf891Box leaf891Inputs = true := by
  rfl'

private theorem leaf891CoversExact : CoversExact 8
    leaf891Box leaf891Certificate leaf891InnerLog leaf891Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi117RoundedFacts
    innerPair35RoundedFacts leaf891RoundedFacts (by rfl)

private theorem leaf891FlatSound : Sound leaf891Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf891CertificateValid
    leaf891InnerLogValid leaf891CoversExact leaf891LowerChecked

private noncomputable def leaf892Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf892Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435667/268435456) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743448064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (404643507/268435456) }, upper := { exponent := 0, mantissa := (785/512) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487146803/27486896128) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf892InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf892LocalValidity :
    LeafFacts leaf892Box leaf892Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf892Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743448064) }) = true
      norm_num [leaf892Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf892CertificateValid :
    WideCertificateValid leaf892Box leaf892Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi118ValidityFacts
    leaf892LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf892CoverageChecked :
    coverageCheck (innerAD leaf892Box) leaf892InnerLog = true := by
  rfl'

private theorem leaf892InnerLogValid :
    leaf892InnerLog.Valid 8 (innerAD leaf892Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf892CoverageChecked

private noncomputable def leaf892InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf892InputLogOnePlusV_eq :
    leaf892InputLogOnePlusV = outerEnclosure 24
      (leaf892Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf892RoundedFacts : LeafRoundedFacts 8
    leaf892Certificate.logOnePlusV leaf892InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf892InputLogOnePlusV_eq }

private noncomputable def leaf892Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi118InputQChi innerPair40Input
    leaf892InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf892LowerChecked :
    lowerCheck 24 leaf892Box leaf892Inputs = true := by
  rfl'

private theorem leaf892CoversExact : CoversExact 8
    leaf892Box leaf892Certificate leaf892InnerLog leaf892Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi118RoundedFacts
    innerPair40RoundedFacts leaf892RoundedFacts (by rfl)

private theorem leaf892FlatSound : Sound leaf892Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf892CertificateValid
    leaf892InnerLogValid leaf892CoversExact leaf892LowerChecked

private noncomputable def leaf893Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf893Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (65531/65536), upper := (67108928/67106889) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (391078387/268435456) }, upper := { exponent := 0, mantissa := (6071/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (134215817/134213778) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf893InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf893LocalValidity :
    LeafFacts leaf893Box leaf893Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf893Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67108928/67106889) }) = true
      norm_num [leaf893Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf893CertificateValid :
    WideCertificateValid leaf893Box leaf893Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi115ValidityFacts
    leaf893LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf893CoverageChecked :
    coverageCheck (innerAD leaf893Box) leaf893InnerLog = true := by
  rfl'

private theorem leaf893InnerLogValid :
    leaf893InnerLog.Valid 8 (innerAD leaf893Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf893CoverageChecked

private noncomputable def leaf893InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf893InputLogOnePlusV_eq :
    leaf893InputLogOnePlusV = outerEnclosure 24
      (leaf893Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf893RoundedFacts : LeafRoundedFacts 8
    leaf893Certificate.logOnePlusV leaf893InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf893InputLogOnePlusV_eq }

private noncomputable def leaf893Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi115InputQChi innerPair34Input
    leaf893InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf893LowerChecked :
    lowerCheck 24 leaf893Box leaf893Inputs = true := by
  rfl'

private theorem leaf893CoversExact : CoversExact 8
    leaf893Box leaf893Certificate leaf893InnerLog leaf893Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi115RoundedFacts
    innerPair34RoundedFacts leaf893RoundedFacts (by rfl)

private theorem leaf893FlatSound : Sound leaf893Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf893CertificateValid
    leaf893InnerLogValid leaf893CoversExact leaf893LowerChecked

private noncomputable def leaf894Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf894Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435665/268435456) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743474688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (396189881/268435456) }, upper := { exponent := 0, mantissa := (3075/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487173427/27486949376) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf894InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf894LocalValidity :
    LeafFacts leaf894Box leaf894Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf894Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743474688) }) = true
      norm_num [leaf894Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf894CertificateValid :
    WideCertificateValid leaf894Box leaf894Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi116ValidityFacts
    leaf894LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf894CoverageChecked :
    coverageCheck (innerAD leaf894Box) leaf894InnerLog = true := by
  rfl'

private theorem leaf894InnerLogValid :
    leaf894InnerLog.Valid 8 (innerAD leaf894Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf894CoverageChecked

private noncomputable def leaf894InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf894InputLogOnePlusV_eq :
    leaf894InputLogOnePlusV = outerEnclosure 24
      (leaf894Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf894RoundedFacts : LeafRoundedFacts 8
    leaf894Certificate.logOnePlusV leaf894InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf894InputLogOnePlusV_eq }

private noncomputable def leaf894Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi116InputQChi innerPair35Input
    leaf894InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf894LowerChecked :
    lowerCheck 24 leaf894Box leaf894Inputs = true := by
  rfl'

private theorem leaf894CoversExact : CoversExact 8
    leaf894Box leaf894Certificate leaf894InnerLog leaf894Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi116RoundedFacts
    innerPair35RoundedFacts leaf894RoundedFacts (by rfl)

private theorem leaf894FlatSound : Sound leaf894Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf894CertificateValid
    leaf894InnerLogValid leaf894CoversExact leaf894LowerChecked

private noncomputable def leaf895Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf895Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717428736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (392651153/268435456) }, upper := { exponent := 0, mantissa := (381/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435922431/137434857472) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf895InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf895LocalValidity :
    LeafFacts leaf895Box leaf895Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf895Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717428736) }) = true
      norm_num [leaf895Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf895CertificateValid :
    WideCertificateValid leaf895Box leaf895Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi115ValidityFacts
    leaf895LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf895CoverageChecked :
    coverageCheck (innerAD leaf895Box) leaf895InnerLog = true := by
  rfl'

private theorem leaf895InnerLogValid :
    leaf895InnerLog.Valid 8 (innerAD leaf895Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf895CoverageChecked

private noncomputable def leaf895InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf895InputLogOnePlusV_eq :
    leaf895InputLogOnePlusV = outerEnclosure 24
      (leaf895Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf895RoundedFacts : LeafRoundedFacts 8
    leaf895Certificate.logOnePlusV leaf895InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf895InputLogOnePlusV_eq }

private noncomputable def leaf895Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi115InputQChi innerPair34Input
    leaf895InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf895LowerChecked :
    lowerCheck 24 leaf895Box leaf895Inputs = true := by
  rfl'

private theorem leaf895CoversExact : CoversExact 8
    leaf895Box leaf895Certificate leaf895InnerLog leaf895Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi115RoundedFacts
    innerPair34RoundedFacts leaf895RoundedFacts (by rfl)

private theorem leaf895FlatSound : Sound leaf895Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf895CertificateValid
    leaf895InnerLogValid leaf895CoversExact leaf895LowerChecked

private noncomputable def leaf896Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf896Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905782272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (397828179/268435456) }, upper := { exponent := 0, mantissa := (193/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811946837/45811564544) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf896InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf896LocalValidity :
    LeafFacts leaf896Box leaf896Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf896Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905782272) }) = true
      norm_num [leaf896Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf896CertificateValid :
    WideCertificateValid leaf896Box leaf896Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi116ValidityFacts
    leaf896LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf896CoverageChecked :
    coverageCheck (innerAD leaf896Box) leaf896InnerLog = true := by
  rfl'

private theorem leaf896InnerLogValid :
    leaf896InnerLog.Valid 8 (innerAD leaf896Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf896CoverageChecked

private noncomputable def leaf896InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf896InputLogOnePlusV_eq :
    leaf896InputLogOnePlusV = outerEnclosure 24
      (leaf896Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf896RoundedFacts : LeafRoundedFacts 8
    leaf896Certificate.logOnePlusV leaf896InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf896InputLogOnePlusV_eq }

private noncomputable def leaf896Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi116InputQChi innerPair35Input
    leaf896InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf896LowerChecked :
    lowerCheck 24 leaf896Box leaf896Inputs = true := by
  rfl'

private theorem leaf896CoversExact : CoversExact 8
    leaf896Box leaf896Certificate leaf896InnerLog leaf896Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi116RoundedFacts
    innerPair35RoundedFacts leaf896RoundedFacts (by rfl)

private theorem leaf896FlatSound : Sound leaf896Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf896CertificateValid
    leaf896InnerLogValid leaf896CoversExact leaf896LowerChecked

private noncomputable def leaf897Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf897Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435667/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717292544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (401301375/268435456) }, upper := { exponent := 0, mantissa := (6229/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435786239/137434585088) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf897InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf897LocalValidity :
    LeafFacts leaf897Box leaf897Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf897Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717292544) }) = true
      norm_num [leaf897Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf897CertificateValid :
    WideCertificateValid leaf897Box leaf897Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi117ValidityFacts
    leaf897LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf897CoverageChecked :
    coverageCheck (innerAD leaf897Box) leaf897InnerLog = true := by
  rfl'

private theorem leaf897InnerLogValid :
    leaf897InnerLog.Valid 8 (innerAD leaf897Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf897CoverageChecked

private noncomputable def leaf897InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf897InputLogOnePlusV_eq :
    leaf897InputLogOnePlusV = outerEnclosure 24
      (leaf897Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf897RoundedFacts : LeafRoundedFacts 8
    leaf897Certificate.logOnePlusV leaf897InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf897InputLogOnePlusV_eq }

private noncomputable def leaf897Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi117InputQChi innerPair35Input
    leaf897InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf897LowerChecked :
    lowerCheck 24 leaf897Box leaf897Inputs = true := by
  rfl'

private theorem leaf897CoversExact : CoversExact 8
    leaf897Box leaf897Certificate leaf897InnerLog leaf897Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi117RoundedFacts
    innerPair35RoundedFacts leaf897RoundedFacts (by rfl)

private theorem leaf897FlatSound : Sound leaf897Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf897CertificateValid
    leaf897InnerLogValid leaf897CoversExact leaf897LowerChecked

private noncomputable def leaf898Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf898Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435669/268435456) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905737216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (406412869/268435456) }, upper := { exponent := 0, mantissa := (1577/1024) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811901781/45811474432) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf898InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf898LocalValidity :
    LeafFacts leaf898Box leaf898Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf898Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905737216) }) = true
      norm_num [leaf898Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf898CertificateValid :
    WideCertificateValid leaf898Box leaf898Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi118ValidityFacts
    leaf898LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf898CoverageChecked :
    coverageCheck (innerAD leaf898Box) leaf898InnerLog = true := by
  rfl'

private theorem leaf898InnerLogValid :
    leaf898InnerLog.Valid 8 (innerAD leaf898Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf898CoverageChecked

private noncomputable def leaf898InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf898InputLogOnePlusV_eq :
    leaf898InputLogOnePlusV = outerEnclosure 24
      (leaf898Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf898RoundedFacts : LeafRoundedFacts 8
    leaf898Certificate.logOnePlusV leaf898InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf898InputLogOnePlusV_eq }

private noncomputable def leaf898Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi118InputQChi innerPair40Input
    leaf898InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf898LowerChecked :
    lowerCheck 24 leaf898Box leaf898Inputs = true := by
  rfl'

private theorem leaf898CoversExact : CoversExact 8
    leaf898Box leaf898Certificate leaf898InnerLog leaf898Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi118RoundedFacts
    innerPair40RoundedFacts leaf898RoundedFacts (by rfl)

private theorem leaf898FlatSound : Sound leaf898Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf898CertificateValid
    leaf898InnerLogValid leaf898CoversExact leaf898LowerChecked

private noncomputable def leaf899Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf899Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717264896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (403005205/268435456) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435758591/137434529792) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf899InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf899LocalValidity :
    LeafFacts leaf899Box leaf899Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf899Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717264896) }) = true
      norm_num [leaf899Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf899CertificateValid :
    WideCertificateValid leaf899Box leaf899Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi117ValidityFacts
    leaf899LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf899CoverageChecked :
    coverageCheck (innerAD leaf899Box) leaf899InnerLog = true := by
  rfl'

private theorem leaf899InnerLogValid :
    leaf899InnerLog.Valid 8 (innerAD leaf899Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf899CoverageChecked

private noncomputable def leaf899InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf899InputLogOnePlusV_eq :
    leaf899InputLogOnePlusV = outerEnclosure 24
      (leaf899Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf899RoundedFacts : LeafRoundedFacts 8
    leaf899Certificate.logOnePlusV leaf899InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf899InputLogOnePlusV_eq }

private noncomputable def leaf899Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi117InputQChi innerPair40Input
    leaf899InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf899LowerChecked :
    lowerCheck 24 leaf899Box leaf899Inputs = true := by
  rfl'

private theorem leaf899CoversExact : CoversExact 8
    leaf899Box leaf899Certificate leaf899InnerLog leaf899Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi117RoundedFacts
    innerPair40RoundedFacts leaf899RoundedFacts (by rfl)

private theorem leaf899FlatSound : Sound leaf899Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf899CertificateValid
    leaf899InnerLogValid leaf899CoversExact leaf899LowerChecked

private noncomputable def leaf900Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf900Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717182976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (408182231/268435456) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435676671/137434365952) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf900InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf900LocalValidity :
    LeafFacts leaf900Box leaf900Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf900Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717182976) }) = true
      norm_num [leaf900Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf900CertificateValid :
    WideCertificateValid leaf900Box leaf900Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi118ValidityFacts
    leaf900LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf900CoverageChecked :
    coverageCheck (innerAD leaf900Box) leaf900InnerLog = true := by
  rfl'

private theorem leaf900InnerLogValid :
    leaf900InnerLog.Valid 8 (innerAD leaf900Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf900CoverageChecked

private noncomputable def leaf900InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf900InputLogOnePlusV_eq :
    leaf900InputLogOnePlusV = outerEnclosure 24
      (leaf900Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf900RoundedFacts : LeafRoundedFacts 8
    leaf900Certificate.logOnePlusV leaf900InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf900InputLogOnePlusV_eq }

private noncomputable def leaf900Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi118InputQChi innerPair40Input
    leaf900InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf900LowerChecked :
    lowerCheck 24 leaf900Box leaf900Inputs = true := by
  rfl'

private theorem leaf900CoversExact : CoversExact 8
    leaf900Box leaf900Certificate leaf900InnerLog leaf900Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi118RoundedFacts
    innerPair40RoundedFacts leaf900RoundedFacts (by rfl)

private theorem leaf900FlatSound : Sound leaf900Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf900CertificateValid
    leaf900InnerLogValid leaf900CoversExact leaf900LowerChecked

private noncomputable def leaf901Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf901Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435667/268435456) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905730048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (407854575/268435456) }, upper := { exponent := 0, mantissa := (6329/4096) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811894613/45811460096) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf901InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf901LocalValidity :
    LeafFacts leaf901Box leaf901Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf901Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905730048) }) = true
      norm_num [leaf901Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf901CertificateValid :
    WideCertificateValid leaf901Box leaf901Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi119ValidityFacts
    leaf901LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf901CoverageChecked :
    coverageCheck (innerAD leaf901Box) leaf901InnerLog = true := by
  rfl'

private theorem leaf901InnerLogValid :
    leaf901InnerLog.Valid 8 (innerAD leaf901Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf901CoverageChecked

private noncomputable def leaf901InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf901InputLogOnePlusV_eq :
    leaf901InputLogOnePlusV = outerEnclosure 24
      (leaf901Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf901RoundedFacts : LeafRoundedFacts 8
    leaf901Certificate.logOnePlusV leaf901InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf901InputLogOnePlusV_eq }

private noncomputable def leaf901Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi119InputQChi innerPair40Input
    leaf901InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf901LowerChecked :
    lowerCheck 24 leaf901Box leaf901Inputs = true := by
  rfl'

private theorem leaf901CoversExact : CoversExact 8
    leaf901Box leaf901Certificate leaf901InnerLog leaf901Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi119RoundedFacts
    innerPair40RoundedFacts leaf901RoundedFacts (by rfl)

private theorem leaf901FlatSound : Sound leaf901Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf901CertificateValid
    leaf901InnerLogValid leaf901CoversExact leaf901LowerChecked

private noncomputable def leaf902Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf902Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435669/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717111296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (412835005/268435456) }, upper := { exponent := 0, mantissa := (3203/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435604991/137434222592) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf902InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf902LocalValidity :
    LeafFacts leaf902Box leaf902Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf902Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717111296) }) = true
      norm_num [leaf902Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf902CertificateValid :
    WideCertificateValid leaf902Box leaf902Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi120ValidityFacts
    leaf902LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf902CoverageChecked :
    coverageCheck (innerAD leaf902Box) leaf902InnerLog = true := by
  rfl'

private theorem leaf902InnerLogValid :
    leaf902InnerLog.Valid 8 (innerAD leaf902Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf902CoverageChecked

private noncomputable def leaf902InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf902InputLogOnePlusV_eq :
    leaf902InputLogOnePlusV = outerEnclosure 24
      (leaf902Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf902RoundedFacts : LeafRoundedFacts 8
    leaf902Certificate.logOnePlusV leaf902InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf902InputLogOnePlusV_eq }

private noncomputable def leaf902Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi120InputQChi innerPair41Input
    leaf902InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf902LowerChecked :
    lowerCheck 24 leaf902Box leaf902Inputs = true := by
  rfl'

private theorem leaf902CoversExact : CoversExact 8
    leaf902Box leaf902Certificate leaf902InnerLog leaf902Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi120RoundedFacts
    innerPair41RoundedFacts leaf902RoundedFacts (by rfl)

private theorem leaf902FlatSound : Sound leaf902Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf902CertificateValid
    leaf902InnerLogValid leaf902CoversExact leaf902LowerChecked

private noncomputable def leaf903Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf903Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435669/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717160448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (409689469/268435456) }, upper := { exponent := 0, mantissa := (3179/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435654143/137434320896) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf903InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf903LocalValidity :
    LeafFacts leaf903Box leaf903Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf903Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717160448) }) = true
      norm_num [leaf903Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf903CertificateValid :
    WideCertificateValid leaf903Box leaf903Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi119ValidityFacts
    leaf903LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf903CoverageChecked :
    coverageCheck (innerAD leaf903Box) leaf903InnerLog = true := by
  rfl'

private theorem leaf903InnerLogValid :
    leaf903InnerLog.Valid 8 (innerAD leaf903Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf903CoverageChecked

private noncomputable def leaf903InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf903InputLogOnePlusV_eq :
    leaf903InputLogOnePlusV = outerEnclosure 24
      (leaf903Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf903RoundedFacts : LeafRoundedFacts 8
    leaf903Certificate.logOnePlusV leaf903InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf903InputLogOnePlusV_eq }

private noncomputable def leaf903Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi119InputQChi innerPair40Input
    leaf903InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf903LowerChecked :
    lowerCheck 24 leaf903Box leaf903Inputs = true := by
  rfl'

private theorem leaf903CoversExact : CoversExact 8
    leaf903Box leaf903Certificate leaf903InnerLog leaf903Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi119RoundedFacts
    innerPair40RoundedFacts leaf903RoundedFacts (by rfl)

private theorem leaf903FlatSound : Sound leaf903Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf903CertificateValid
    leaf903InnerLogValid leaf903CoversExact leaf903LowerChecked

private noncomputable def leaf904Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf904Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435671/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717080576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (414735431/268435456) }, upper := { exponent := 0, mantissa := (1609/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435574271/137434161152) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf904InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf904LocalValidity :
    LeafFacts leaf904Box leaf904Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf904Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717080576) }) = true
      norm_num [leaf904Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf904CertificateValid :
    WideCertificateValid leaf904Box leaf904Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi120ValidityFacts
    leaf904LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf904CoverageChecked :
    coverageCheck (innerAD leaf904Box) leaf904InnerLog = true := by
  rfl'

private theorem leaf904InnerLogValid :
    leaf904InnerLog.Valid 8 (innerAD leaf904Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf904CoverageChecked

private noncomputable def leaf904InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf904InputLogOnePlusV_eq :
    leaf904InputLogOnePlusV = outerEnclosure 24
      (leaf904Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf904RoundedFacts : LeafRoundedFacts 8
    leaf904Certificate.logOnePlusV leaf904InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf904InputLogOnePlusV_eq }

private noncomputable def leaf904Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi120InputQChi innerPair41Input
    leaf904InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf904LowerChecked :
    lowerCheck 24 leaf904Box leaf904Inputs = true := by
  rfl'

private theorem leaf904CoversExact : CoversExact 8
    leaf904Box leaf904Certificate leaf904InnerLog leaf904Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi120RoundedFacts
    innerPair41RoundedFacts leaf904RoundedFacts (by rfl)

private theorem leaf904FlatSound : Sound leaf904Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf904CertificateValid
    leaf904InnerLogValid leaf904CoversExact leaf904LowerChecked

private noncomputable def leaf905Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf905Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217913/134217728) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581130240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (208891257/134217728) }, upper := { exponent := 0, mantissa := (205/128) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162363153/9162260480) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf905InnerLog : WideLogData :=
  innerPair401Data

set_option maxRecDepth 1000000 in
private theorem leaf905LocalValidity :
    LeafFacts leaf905Box leaf905Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf905Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581130240) }) = true
      norm_num [leaf905Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf905CertificateValid :
    WideCertificateValid leaf905Box leaf905Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi45ValidityFacts
    leaf905LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf905CoverageChecked :
    coverageCheck (innerAD leaf905Box) leaf905InnerLog = true := by
  rfl'

private theorem leaf905InnerLogValid :
    leaf905InnerLog.Valid 8 (innerAD leaf905Box) :=
  wideLogDataValid_of_cachedCheck endpoint113PositiveFacts
    endpoint114PositiveFacts.valid leaf905CoverageChecked

private noncomputable def leaf905InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf905InputLogOnePlusV_eq :
    leaf905InputLogOnePlusV = outerEnclosure 24
      (leaf905Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf905RoundedFacts : LeafRoundedFacts 8
    leaf905Certificate.logOnePlusV leaf905InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf905InputLogOnePlusV_eq }

private noncomputable def leaf905Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi45InputQChi innerPair401Input
    leaf905InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf905LowerChecked :
    lowerCheck 24 leaf905Box leaf905Inputs = true := by
  rfl'

private theorem leaf905CoversExact : CoversExact 8
    leaf905Box leaf905Certificate leaf905InnerLog leaf905Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi45RoundedFacts
    innerPair401RoundedFacts leaf905RoundedFacts (by rfl)

private theorem leaf905FlatSound : Sound leaf905Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf905CertificateValid
    leaf905InnerLogValid leaf905CoversExact leaf905LowerChecked

private noncomputable def leaf906Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf906Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435673/268435456) }, vSqrt := { lower := (65531/65536), upper := (4042264335/4042176512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (419781393/268435456) }, upper := { exponent := 0, mantissa := (3257/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8084440847/8084353024) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf906InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf906LocalValidity :
    LeafFacts leaf906Box leaf906Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf906Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4042264335/4042176512) }) = true
      norm_num [leaf906Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf906CertificateValid :
    WideCertificateValid leaf906Box leaf906Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi121ValidityFacts
    leaf906LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf906CoverageChecked :
    coverageCheck (innerAD leaf906Box) leaf906InnerLog = true := by
  rfl'

private theorem leaf906InnerLogValid :
    leaf906InnerLog.Valid 8 (innerAD leaf906Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf906CoverageChecked

private noncomputable def leaf906InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf906InputLogOnePlusV_eq :
    leaf906InputLogOnePlusV = outerEnclosure 24
      (leaf906Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf906RoundedFacts : LeafRoundedFacts 8
    leaf906Certificate.logOnePlusV leaf906InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf906InputLogOnePlusV_eq }

private noncomputable def leaf906Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi121InputQChi innerPair50Input
    leaf906InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf906LowerChecked :
    lowerCheck 24 leaf906Box leaf906Inputs = true := by
  rfl'

private theorem leaf906CoversExact : CoversExact 8
    leaf906Box leaf906Certificate leaf906InnerLog leaf906Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi121RoundedFacts
    innerPair50RoundedFacts leaf906RoundedFacts (by rfl)

private theorem leaf906FlatSound : Sound leaf906Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf906CertificateValid
    leaf906InnerLogValid leaf906CoversExact leaf906LowerChecked

private noncomputable def leaf907Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf907Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716920832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (424827355/268435456) }, upper := { exponent := 0, mantissa := (103/64) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435414527/137433841664) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf907InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf907LocalValidity :
    LeafFacts leaf907Box leaf907Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf907Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716920832) }) = true
      norm_num [leaf907Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf907CertificateValid :
    WideCertificateValid leaf907Box leaf907Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi122ValidityFacts
    leaf907LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf907CoverageChecked :
    coverageCheck (innerAD leaf907Box) leaf907InnerLog = true := by
  rfl'

private theorem leaf907InnerLogValid :
    leaf907InnerLog.Valid 8 (innerAD leaf907Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf907CoverageChecked

private noncomputable def leaf907InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf907InputLogOnePlusV_eq :
    leaf907InputLogOnePlusV = outerEnclosure 24
      (leaf907Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf907RoundedFacts : LeafRoundedFacts 8
    leaf907Certificate.logOnePlusV leaf907InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf907InputLogOnePlusV_eq }

private noncomputable def leaf907Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi122InputQChi innerPair50Input
    leaf907InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf907LowerChecked :
    lowerCheck 24 leaf907Box leaf907Inputs = true := by
  rfl'

private theorem leaf907CoversExact : CoversExact 8
    leaf907Box leaf907Certificate leaf907InnerLog leaf907Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi122RoundedFacts
    innerPair50RoundedFacts leaf907RoundedFacts (by rfl)

private theorem leaf907FlatSound : Sound leaf907Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf907CertificateValid
    leaf907InnerLogValid leaf907CoversExact leaf907LowerChecked

private noncomputable def leaf908Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf908Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435671/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717130752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (411524363/268435456) }, upper := { exponent := 0, mantissa := (6387/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435624447/137434261504) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf908InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf908LocalValidity :
    LeafFacts leaf908Box leaf908Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf908Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717130752) }) = true
      norm_num [leaf908Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf908CertificateValid :
    WideCertificateValid leaf908Box leaf908Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi119ValidityFacts
    leaf908LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf908CoverageChecked :
    coverageCheck (innerAD leaf908Box) leaf908InnerLog = true := by
  rfl'

private theorem leaf908InnerLogValid :
    leaf908InnerLog.Valid 8 (innerAD leaf908Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf908CoverageChecked

private noncomputable def leaf908InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf908InputLogOnePlusV_eq :
    leaf908InputLogOnePlusV = outerEnclosure 24
      (leaf908Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf908RoundedFacts : LeafRoundedFacts 8
    leaf908Certificate.logOnePlusV leaf908InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf908InputLogOnePlusV_eq }

private noncomputable def leaf908Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi119InputQChi innerPair40Input
    leaf908InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf908LowerChecked :
    lowerCheck 24 leaf908Box leaf908Inputs = true := by
  rfl'

private theorem leaf908CoversExact : CoversExact 8
    leaf908Box leaf908Certificate leaf908InnerLog leaf908Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi119RoundedFacts
    innerPair40RoundedFacts leaf908RoundedFacts (by rfl)

private theorem leaf908FlatSound : Sound leaf908Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf908CertificateValid
    leaf908InnerLogValid leaf908CoversExact leaf908LowerChecked

private noncomputable def leaf909Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf909Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435673/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68717049856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (416635857/268435456) }, upper := { exponent := 0, mantissa := (3233/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435543551/137434099712) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf909InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf909LocalValidity :
    LeafFacts leaf909Box leaf909Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf909Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68717049856) }) = true
      norm_num [leaf909Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf909CertificateValid :
    WideCertificateValid leaf909Box leaf909Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi120ValidityFacts
    leaf909LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf909CoverageChecked :
    coverageCheck (innerAD leaf909Box) leaf909InnerLog = true := by
  rfl'

private theorem leaf909InnerLogValid :
    leaf909InnerLog.Valid 8 (innerAD leaf909Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf909CoverageChecked

private noncomputable def leaf909InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf909InputLogOnePlusV_eq :
    leaf909InputLogOnePlusV = outerEnclosure 24
      (leaf909Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf909RoundedFacts : LeafRoundedFacts 8
    leaf909Certificate.logOnePlusV leaf909InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf909InputLogOnePlusV_eq }

private noncomputable def leaf909Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi120InputQChi innerPair41Input
    leaf909InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf909LowerChecked :
    lowerCheck 24 leaf909Box leaf909Inputs = true := by
  rfl'

private theorem leaf909CoversExact : CoversExact 8
    leaf909Box leaf909Certificate leaf909InnerLog leaf909Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi120RoundedFacts
    innerPair41RoundedFacts leaf909RoundedFacts (by rfl)

private theorem leaf909FlatSound : Sound leaf909Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf909CertificateValid
    leaf909InnerLogValid leaf909CoversExact leaf909LowerChecked

private noncomputable def leaf910Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf910Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905700352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (413359257/268435456) }, upper := { exponent := 0, mantissa := (401/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811864917/45811400704) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf910InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf910LocalValidity :
    LeafFacts leaf910Box leaf910Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf910Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905700352) }) = true
      norm_num [leaf910Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf910CertificateValid :
    WideCertificateValid leaf910Box leaf910Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi119ValidityFacts
    leaf910LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf910CoverageChecked :
    coverageCheck (innerAD leaf910Box) leaf910InnerLog = true := by
  rfl'

private theorem leaf910InnerLogValid :
    leaf910InnerLog.Valid 8 (innerAD leaf910Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf910CoverageChecked

private noncomputable def leaf910InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf910InputLogOnePlusV_eq :
    leaf910InputLogOnePlusV = outerEnclosure 24
      (leaf910Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf910RoundedFacts : LeafRoundedFacts 8
    leaf910Certificate.logOnePlusV leaf910InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf910InputLogOnePlusV_eq }

private noncomputable def leaf910Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi119InputQChi innerPair41Input
    leaf910InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf910LowerChecked :
    lowerCheck 24 leaf910Box leaf910Inputs = true := by
  rfl'

private theorem leaf910CoversExact : CoversExact 8
    leaf910Box leaf910Certificate leaf910InnerLog leaf910Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi119RoundedFacts
    innerPair41RoundedFacts leaf910RoundedFacts (by rfl)

private theorem leaf910FlatSound : Sound leaf910Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf910CertificateValid
    leaf910InnerLogValid leaf910CoversExact leaf910LowerChecked

private noncomputable def leaf911Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf911Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717019136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (418536283/268435456) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435512831/137434038272) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf911InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf911LocalValidity :
    LeafFacts leaf911Box leaf911Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf911Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717019136) }) = true
      norm_num [leaf911Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf911CertificateValid :
    WideCertificateValid leaf911Box leaf911Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi120ValidityFacts
    leaf911LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf911CoverageChecked :
    coverageCheck (innerAD leaf911Box) leaf911InnerLog = true := by
  rfl'

private theorem leaf911InnerLogValid :
    leaf911InnerLog.Valid 8 (innerAD leaf911Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf911CoverageChecked

private noncomputable def leaf911InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf911InputLogOnePlusV_eq :
    leaf911InputLogOnePlusV = outerEnclosure 24
      (leaf911Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf911RoundedFacts : LeafRoundedFacts 8
    leaf911Certificate.logOnePlusV leaf911InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf911InputLogOnePlusV_eq }

private noncomputable def leaf911Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi120InputQChi innerPair41Input
    leaf911InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf911LowerChecked :
    lowerCheck 24 leaf911Box leaf911Inputs = true := by
  rfl'

private theorem leaf911CoversExact : CoversExact 8
    leaf911Box leaf911Certificate leaf911InnerLog leaf911Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi120RoundedFacts
    innerPair41RoundedFacts leaf911RoundedFacts (by rfl)

private theorem leaf911FlatSound : Sound leaf911Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf911CertificateValid
    leaf911InnerLogValid leaf911CoversExact leaf911LowerChecked

private noncomputable def leaf912Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf912Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581131264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (421747351/268435456) }, upper := { exponent := 0, mantissa := (6545/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162364177/9162262528) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf912InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf912LocalValidity :
    LeafFacts leaf912Box leaf912Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf912Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581131264) }) = true
      norm_num [leaf912Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf912CertificateValid :
    WideCertificateValid leaf912Box leaf912Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi121ValidityFacts
    leaf912LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf912CoverageChecked :
    coverageCheck (innerAD leaf912Box) leaf912InnerLog = true := by
  rfl'

private theorem leaf912InnerLogValid :
    leaf912InnerLog.Valid 8 (innerAD leaf912Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf912CoverageChecked

private noncomputable def leaf912InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf912InputLogOnePlusV_eq :
    leaf912InputLogOnePlusV = outerEnclosure 24
      (leaf912Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf912RoundedFacts : LeafRoundedFacts 8
    leaf912Certificate.logOnePlusV leaf912InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf912InputLogOnePlusV_eq }

private noncomputable def leaf912Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi121InputQChi innerPair50Input
    leaf912InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf912LowerChecked :
    lowerCheck 24 leaf912Box leaf912Inputs = true := by
  rfl'

private theorem leaf912CoversExact : CoversExact 8
    leaf912Box leaf912Certificate leaf912InnerLog leaf912Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi121RoundedFacts
    innerPair50RoundedFacts leaf912RoundedFacts (by rfl)

private theorem leaf912FlatSound : Sound leaf912Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf912CertificateValid
    leaf912InnerLogValid leaf912CoversExact leaf912LowerChecked

private noncomputable def leaf913Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf913Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716888064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (426858845/268435456) }, upper := { exponent := 0, mantissa := (207/128) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435381759/137433776128) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf913InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf913LocalValidity :
    LeafFacts leaf913Box leaf913Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf913Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716888064) }) = true
      norm_num [leaf913Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf913CertificateValid :
    WideCertificateValid leaf913Box leaf913Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi122ValidityFacts
    leaf913LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf913CoverageChecked :
    coverageCheck (innerAD leaf913Box) leaf913InnerLog = true := by
  rfl'

private theorem leaf913InnerLogValid :
    leaf913InnerLog.Valid 8 (innerAD leaf913Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf913CoverageChecked

private noncomputable def leaf913InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf913InputLogOnePlusV_eq :
    leaf913InputLogOnePlusV = outerEnclosure 24
      (leaf913Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf913RoundedFacts : LeafRoundedFacts 8
    leaf913Certificate.logOnePlusV leaf913InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf913InputLogOnePlusV_eq }

private noncomputable def leaf913Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi122InputQChi innerPair50Input
    leaf913InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf913LowerChecked :
    lowerCheck 24 leaf913Box leaf913Inputs = true := by
  rfl'

private theorem leaf913CoversExact : CoversExact 8
    leaf913Box leaf913Certificate leaf913InnerLog leaf913Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi122RoundedFacts
    innerPair50RoundedFacts leaf913RoundedFacts (by rfl)

private theorem leaf913FlatSound : Sound leaf913Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf913CertificateValid
    leaf913InnerLogValid leaf913CoversExact leaf913LowerChecked

private noncomputable def leaf914Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf914Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716937216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (423713309/268435456) }, upper := { exponent := 0, mantissa := (411/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435430911/137433874432) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf914InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf914LocalValidity :
    LeafFacts leaf914Box leaf914Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf914Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716937216) }) = true
      norm_num [leaf914Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf914CertificateValid :
    WideCertificateValid leaf914Box leaf914Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi121ValidityFacts
    leaf914LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf914CoverageChecked :
    coverageCheck (innerAD leaf914Box) leaf914InnerLog = true := by
  rfl'

private theorem leaf914InnerLogValid :
    leaf914InnerLog.Valid 8 (innerAD leaf914Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf914CoverageChecked

private noncomputable def leaf914InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf914InputLogOnePlusV_eq :
    leaf914InputLogOnePlusV = outerEnclosure 24
      (leaf914Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf914RoundedFacts : LeafRoundedFacts 8
    leaf914Certificate.logOnePlusV leaf914InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf914InputLogOnePlusV_eq }

private noncomputable def leaf914Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi121InputQChi innerPair50Input
    leaf914InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf914LowerChecked :
    lowerCheck 24 leaf914Box leaf914Inputs = true := by
  rfl'

private theorem leaf914CoversExact : CoversExact 8
    leaf914Box leaf914Certificate leaf914InnerLog leaf914Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi121RoundedFacts
    innerPair50RoundedFacts leaf914RoundedFacts (by rfl)

private theorem leaf914FlatSound : Sound leaf914Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf914CertificateValid
    leaf914InnerLogValid leaf914CoversExact leaf914LowerChecked

private noncomputable def leaf915Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf915Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905618432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (428890335/268435456) }, upper := { exponent := 0, mantissa := (13/8) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811782997/45811236864) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf915InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf915LocalValidity :
    LeafFacts leaf915Box leaf915Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf915Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905618432) }) = true
      norm_num [leaf915Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf915CertificateValid :
    WideCertificateValid leaf915Box leaf915Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi122ValidityFacts
    leaf915LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf915CoverageChecked :
    coverageCheck (innerAD leaf915Box) leaf915InnerLog = true := by
  rfl'

private theorem leaf915InnerLogValid :
    leaf915InnerLog.Valid 8 (innerAD leaf915Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf915CoverageChecked

private noncomputable def leaf915InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf915InputLogOnePlusV_eq :
    leaf915InputLogOnePlusV = outerEnclosure 24
      (leaf915Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf915RoundedFacts : LeafRoundedFacts 8
    leaf915Certificate.logOnePlusV leaf915InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf915InputLogOnePlusV_eq }

private noncomputable def leaf915Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi122InputQChi innerPair50Input
    leaf915InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf915LowerChecked :
    lowerCheck 24 leaf915Box leaf915Inputs = true := by
  rfl'

private theorem leaf915CoversExact : CoversExact 8
    leaf915Box leaf915Certificate leaf915InnerLog leaf915Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi122RoundedFacts
    innerPair50RoundedFacts leaf915RoundedFacts (by rfl)

private theorem leaf915FlatSound : Sound leaf915Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf915CertificateValid
    leaf915InnerLogValid leaf915CoversExact leaf915LowerChecked

private noncomputable def component21Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node0_sound : Sound component21Node0Box :=
  sound_of_literal_split component21Node0Box leaf871Box leaf872Box
    .k (73/32) (by rfl) (by rfl)
    leaf871FlatSound leaf872FlatSound

private noncomputable def component21Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node1_sound : Sound component21Node1Box :=
  sound_of_literal_split component21Node1Box leaf873Box leaf874Box
    .k (73/32) (by rfl) (by rfl)
    leaf873FlatSound leaf874FlatSound

private noncomputable def component21Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node2_sound : Sound component21Node2Box :=
  sound_of_literal_split component21Node2Box component21Node0Box component21Node1Box
    .chi (13/64) (by rfl) (by rfl)
    component21Node0_sound component21Node1_sound

private noncomputable def component21Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node3_sound : Sound component21Node3Box :=
  sound_of_literal_split component21Node3Box leaf875Box leaf876Box
    .k (75/32) (by rfl) (by rfl)
    leaf875FlatSound leaf876FlatSound

private noncomputable def component21Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node4_sound : Sound component21Node4Box :=
  sound_of_literal_split component21Node4Box leaf877Box leaf878Box
    .k (75/32) (by rfl) (by rfl)
    leaf877FlatSound leaf878FlatSound

private noncomputable def component21Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node5_sound : Sound component21Node5Box :=
  sound_of_literal_split component21Node5Box component21Node3Box component21Node4Box
    .chi (13/64) (by rfl) (by rfl)
    component21Node3_sound component21Node4_sound

private noncomputable def component21Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node6_sound : Sound component21Node6Box :=
  sound_of_literal_split component21Node6Box component21Node2Box component21Node5Box
    .k (37/16) (by rfl) (by rfl)
    component21Node2_sound component21Node5_sound

private noncomputable def component21Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node7_sound : Sound component21Node7Box :=
  sound_of_literal_split component21Node7Box leaf879Box leaf880Box
    .k (73/32) (by rfl) (by rfl)
    leaf879FlatSound leaf880FlatSound

private noncomputable def component21Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node8_sound : Sound component21Node8Box :=
  sound_of_literal_split component21Node8Box leaf881Box leaf882Box
    .k (73/32) (by rfl) (by rfl)
    leaf881FlatSound leaf882FlatSound

private noncomputable def component21Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node9_sound : Sound component21Node9Box :=
  sound_of_literal_split component21Node9Box component21Node7Box component21Node8Box
    .chi (15/64) (by rfl) (by rfl)
    component21Node7_sound component21Node8_sound

private noncomputable def component21Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node10_sound : Sound component21Node10Box :=
  sound_of_literal_split component21Node10Box leaf883Box leaf884Box
    .k (75/32) (by rfl) (by rfl)
    leaf883FlatSound leaf884FlatSound

private noncomputable def component21Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node11_sound : Sound component21Node11Box :=
  sound_of_literal_split component21Node11Box leaf885Box leaf886Box
    .k (75/32) (by rfl) (by rfl)
    leaf885FlatSound leaf886FlatSound

private noncomputable def component21Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node12_sound : Sound component21Node12Box :=
  sound_of_literal_split component21Node12Box component21Node10Box component21Node11Box
    .chi (15/64) (by rfl) (by rfl)
    component21Node10_sound component21Node11_sound

private noncomputable def component21Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node13_sound : Sound component21Node13Box :=
  sound_of_literal_split component21Node13Box component21Node9Box component21Node12Box
    .k (37/16) (by rfl) (by rfl)
    component21Node9_sound component21Node12_sound

private noncomputable def component21Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node14_sound : Sound component21Node14Box :=
  sound_of_literal_split component21Node14Box component21Node6Box component21Node13Box
    .chi (7/32) (by rfl) (by rfl)
    component21Node6_sound component21Node13_sound

private noncomputable def component21Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node15_sound : Sound component21Node15Box :=
  sound_of_literal_split component21Node15Box leaf888Box leaf889Box
    .chi (25/128) (by rfl) (by rfl)
    leaf888FlatSound leaf889FlatSound

private noncomputable def component21Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node16_sound : Sound component21Node16Box :=
  sound_of_literal_split component21Node16Box leaf887Box component21Node15Box
    .k (77/32) (by rfl) (by rfl)
    leaf887FlatSound component21Node15_sound

private noncomputable def component21Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node17_sound : Sound component21Node17Box :=
  sound_of_literal_split component21Node17Box leaf891Box leaf892Box
    .chi (27/128) (by rfl) (by rfl)
    leaf891FlatSound leaf892FlatSound

private noncomputable def component21Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node18_sound : Sound component21Node18Box :=
  sound_of_literal_split component21Node18Box leaf890Box component21Node17Box
    .k (77/32) (by rfl) (by rfl)
    leaf890FlatSound component21Node17_sound

private noncomputable def component21Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node19_sound : Sound component21Node19Box :=
  sound_of_literal_split component21Node19Box component21Node16Box component21Node18Box
    .chi (13/64) (by rfl) (by rfl)
    component21Node16_sound component21Node18_sound

private noncomputable def component21Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node20_sound : Sound component21Node20Box :=
  sound_of_literal_split component21Node20Box leaf893Box leaf894Box
    .chi (25/128) (by rfl) (by rfl)
    leaf893FlatSound leaf894FlatSound

private noncomputable def component21Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node21_sound : Sound component21Node21Box :=
  sound_of_literal_split component21Node21Box leaf895Box leaf896Box
    .chi (25/128) (by rfl) (by rfl)
    leaf895FlatSound leaf896FlatSound

private noncomputable def component21Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node22_sound : Sound component21Node22Box :=
  sound_of_literal_split component21Node22Box component21Node20Box component21Node21Box
    .k (79/32) (by rfl) (by rfl)
    component21Node20_sound component21Node21_sound

private noncomputable def component21Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node23_sound : Sound component21Node23Box :=
  sound_of_literal_split component21Node23Box leaf897Box leaf898Box
    .chi (27/128) (by rfl) (by rfl)
    leaf897FlatSound leaf898FlatSound

private noncomputable def component21Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node24_sound : Sound component21Node24Box :=
  sound_of_literal_split component21Node24Box leaf899Box leaf900Box
    .chi (27/128) (by rfl) (by rfl)
    leaf899FlatSound leaf900FlatSound

private noncomputable def component21Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node25_sound : Sound component21Node25Box :=
  sound_of_literal_split component21Node25Box component21Node23Box component21Node24Box
    .k (79/32) (by rfl) (by rfl)
    component21Node23_sound component21Node24_sound

private noncomputable def component21Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node26_sound : Sound component21Node26Box :=
  sound_of_literal_split component21Node26Box component21Node22Box component21Node25Box
    .chi (13/64) (by rfl) (by rfl)
    component21Node22_sound component21Node25_sound

private noncomputable def component21Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component21Node27_sound : Sound component21Node27Box :=
  sound_of_literal_split component21Node27Box component21Node19Box component21Node26Box
    .k (39/16) (by rfl) (by rfl)
    component21Node19_sound component21Node26_sound

private noncomputable def component21Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node28_sound : Sound component21Node28Box :=
  sound_of_literal_split component21Node28Box leaf901Box leaf902Box
    .chi (29/128) (by rfl) (by rfl)
    leaf901FlatSound leaf902FlatSound

private noncomputable def component21Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node29_sound : Sound component21Node29Box :=
  sound_of_literal_split component21Node29Box leaf903Box leaf904Box
    .chi (29/128) (by rfl) (by rfl)
    leaf903FlatSound leaf904FlatSound

private noncomputable def component21Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node30_sound : Sound component21Node30Box :=
  sound_of_literal_split component21Node30Box component21Node28Box component21Node29Box
    .k (77/32) (by rfl) (by rfl)
    component21Node28_sound component21Node29_sound

private noncomputable def component21Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node31_sound : Sound component21Node31Box :=
  sound_of_literal_split component21Node31Box leaf906Box leaf907Box
    .chi (31/128) (by rfl) (by rfl)
    leaf906FlatSound leaf907FlatSound

private noncomputable def component21Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node32_sound : Sound component21Node32Box :=
  sound_of_literal_split component21Node32Box leaf905Box component21Node31Box
    .k (77/32) (by rfl) (by rfl)
    leaf905FlatSound component21Node31_sound

private noncomputable def component21Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node33_sound : Sound component21Node33Box :=
  sound_of_literal_split component21Node33Box component21Node30Box component21Node32Box
    .chi (15/64) (by rfl) (by rfl)
    component21Node30_sound component21Node32_sound

private noncomputable def component21Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node34_sound : Sound component21Node34Box :=
  sound_of_literal_split component21Node34Box leaf908Box leaf909Box
    .chi (29/128) (by rfl) (by rfl)
    leaf908FlatSound leaf909FlatSound

private noncomputable def component21Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node35_sound : Sound component21Node35Box :=
  sound_of_literal_split component21Node35Box leaf910Box leaf911Box
    .chi (29/128) (by rfl) (by rfl)
    leaf910FlatSound leaf911FlatSound

private noncomputable def component21Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component21Node36_sound : Sound component21Node36Box :=
  sound_of_literal_split component21Node36Box component21Node34Box component21Node35Box
    .k (79/32) (by rfl) (by rfl)
    component21Node34_sound component21Node35_sound

private noncomputable def component21Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node37_sound : Sound component21Node37Box :=
  sound_of_literal_split component21Node37Box leaf912Box leaf913Box
    .chi (31/128) (by rfl) (by rfl)
    leaf912FlatSound leaf913FlatSound

private noncomputable def component21Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node38_sound : Sound component21Node38Box :=
  sound_of_literal_split component21Node38Box leaf914Box leaf915Box
    .chi (31/128) (by rfl) (by rfl)
    leaf914FlatSound leaf915FlatSound

private noncomputable def component21Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node39_sound : Sound component21Node39Box :=
  sound_of_literal_split component21Node39Box component21Node37Box component21Node38Box
    .k (79/32) (by rfl) (by rfl)
    component21Node37_sound component21Node38_sound

private noncomputable def component21Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node40_sound : Sound component21Node40Box :=
  sound_of_literal_split component21Node40Box component21Node36Box component21Node39Box
    .chi (15/64) (by rfl) (by rfl)
    component21Node36_sound component21Node39_sound

private noncomputable def component21Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node41_sound : Sound component21Node41Box :=
  sound_of_literal_split component21Node41Box component21Node33Box component21Node40Box
    .k (39/16) (by rfl) (by rfl)
    component21Node33_sound component21Node40_sound

private noncomputable def component21Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component21Node42_sound : Sound component21Node42Box :=
  sound_of_literal_split component21Node42Box component21Node27Box component21Node41Box
    .chi (7/32) (by rfl) (by rfl)
    component21Node27_sound component21Node41_sound

noncomputable def component21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component21_sound : Sound component21Box :=
  sound_of_literal_split component21Box component21Node14Box component21Node42Box
    .k (19/8) (by rfl) (by rfl)
    component21Node14_sound component21Node42_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
