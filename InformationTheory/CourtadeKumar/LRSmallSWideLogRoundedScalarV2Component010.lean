import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0

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

private noncomputable def leaf387Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (57/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf387Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217875/134217728) }, vSqrt := { lower := (16383/16384), upper := (33554464/33553463) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (192901487/134217728) }, upper := { exponent := 0, mantissa := (3017/2048) } }, logOuter := sk57LogOuterCertificate, logK := sk57LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (67107927/67106926) } }, logDArg := sk57LogDArgCertificate }

private noncomputable def leaf387InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf387LocalValidity :
    LeafFacts leaf387Box leaf387Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf387Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (33554464/33553463) }) = true
      norm_num [leaf387Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf387CertificateValid :
    WideCertificateValid leaf387Box leaf387Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk57ValidityFacts chi54ValidityFacts
    leaf387LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf387CoverageChecked :
    coverageCheck (innerAD leaf387Box) leaf387InnerLog = true := by
  rfl'

private theorem leaf387InnerLogValid :
    leaf387InnerLog.Valid 8 (innerAD leaf387Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf387CoverageChecked

private noncomputable def leaf387InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf387InputLogOnePlusV_eq :
    leaf387InputLogOnePlusV = outerEnclosure 24
      (leaf387Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf387RoundedFacts : LeafRoundedFacts 8
    leaf387Certificate.logOnePlusV leaf387InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf387InputLogOnePlusV_eq }

private noncomputable def leaf387Inputs : Inputs :=
  inputsOfCaches globalInput sk57RoundedInputs
    chi54InputQChi innerPair27Input
    leaf387InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf387LowerChecked :
    lowerCheck 24 leaf387Box leaf387Inputs = true := by
  rfl'

private theorem leaf387CoversExact : CoversExact 8
    leaf387Box leaf387Certificate leaf387InnerLog leaf387Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk57RoundedFacts chi54RoundedFacts
    innerPair27RoundedFacts leaf387RoundedFacts (by rfl)

private theorem leaf387FlatSound : Sound leaf387Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf387CertificateValid
    leaf387InnerLogValid leaf387CoversExact leaf387LowerChecked

private noncomputable def leaf388Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/32), kHi := (29/16), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf388Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217877/134217728) }, vSqrt := { lower := (16383/16384), upper := (16777232/16776723) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (193949997/134217728) }, upper := { exponent := 0, mantissa := (1517/1024) } }, logOuter := sk58LogOuterCertificate, logK := sk58LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33553955/33553446) } }, logDArg := sk58LogDArgCertificate }

private noncomputable def leaf388InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf388LocalValidity :
    LeafFacts leaf388Box leaf388Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf388Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777232/16776723) }) = true
      norm_num [leaf388Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf388CertificateValid :
    WideCertificateValid leaf388Box leaf388Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk58ValidityFacts chi54ValidityFacts
    leaf388LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf388CoverageChecked :
    coverageCheck (innerAD leaf388Box) leaf388InnerLog = true := by
  rfl'

private theorem leaf388InnerLogValid :
    leaf388InnerLog.Valid 8 (innerAD leaf388Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf388CoverageChecked

private noncomputable def leaf388InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf388InputLogOnePlusV_eq :
    leaf388InputLogOnePlusV = outerEnclosure 24
      (leaf388Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf388RoundedFacts : LeafRoundedFacts 8
    leaf388Certificate.logOnePlusV leaf388InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf388InputLogOnePlusV_eq }

private noncomputable def leaf388Inputs : Inputs :=
  inputsOfCaches globalInput sk58RoundedInputs
    chi54InputQChi innerPair34Input
    leaf388InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf388LowerChecked :
    lowerCheck 24 leaf388Box leaf388Inputs = true := by
  rfl'

private theorem leaf388CoversExact : CoversExact 8
    leaf388Box leaf388Certificate leaf388InnerLog leaf388Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk58RoundedFacts chi54RoundedFacts
    innerPair34RoundedFacts leaf388RoundedFacts (by rfl)

private theorem leaf388FlatSound : Sound leaf388Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf388CertificateValid
    leaf388InnerLogValid leaf388CoversExact leaf388LowerChecked

private noncomputable def leaf389Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (57/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf389Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217877/134217728) }, vSqrt := { lower := (16383/16384), upper := (267387135/267382784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (196571277/134217728) }, upper := { exponent := 0, mantissa := (1537/1024) } }, logOuter := sk57LogOuterCertificate, logK := sk57LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (534769919/534765568) } }, logDArg := sk57LogDArgCertificate }

private noncomputable def leaf389InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf389LocalValidity :
    LeafFacts leaf389Box leaf389Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf389Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (267387135/267382784) }) = true
      norm_num [leaf389Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf389CertificateValid :
    WideCertificateValid leaf389Box leaf389Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk57ValidityFacts chi55ValidityFacts
    leaf389LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf389CoverageChecked :
    coverageCheck (innerAD leaf389Box) leaf389InnerLog = true := by
  rfl'

private theorem leaf389InnerLogValid :
    leaf389InnerLog.Valid 8 (innerAD leaf389Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf389CoverageChecked

private noncomputable def leaf389InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf389InputLogOnePlusV_eq :
    leaf389InputLogOnePlusV = outerEnclosure 24
      (leaf389Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf389RoundedFacts : LeafRoundedFacts 8
    leaf389Certificate.logOnePlusV leaf389InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf389InputLogOnePlusV_eq }

private noncomputable def leaf389Inputs : Inputs :=
  inputsOfCaches globalInput sk57RoundedInputs
    chi55InputQChi innerPair35Input
    leaf389InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf389LowerChecked :
    lowerCheck 24 leaf389Box leaf389Inputs = true := by
  rfl'

private theorem leaf389CoversExact : CoversExact 8
    leaf389Box leaf389Certificate leaf389InnerLog leaf389Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk57RoundedFacts chi55RoundedFacts
    innerPair35RoundedFacts leaf389RoundedFacts (by rfl)

private theorem leaf389FlatSound : Sound leaf389Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf389CertificateValid
    leaf389InnerLogValid leaf389CoversExact leaf389LowerChecked

private noncomputable def leaf390Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/32), kHi := (29/16), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf390Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217879/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717338624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (197685319/134217728) }, upper := { exponent := 0, mantissa := (773/512) } }, logOuter := sk58LogOuterCertificate, logK := sk58LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435832319/137434677248) } }, logDArg := sk58LogDArgCertificate }

private noncomputable def leaf390InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf390LocalValidity :
    LeafFacts leaf390Box leaf390Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf390Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717338624) }) = true
      norm_num [leaf390Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf390CertificateValid :
    WideCertificateValid leaf390Box leaf390Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk58ValidityFacts chi55ValidityFacts
    leaf390LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf390CoverageChecked :
    coverageCheck (innerAD leaf390Box) leaf390InnerLog = true := by
  rfl'

private theorem leaf390InnerLogValid :
    leaf390InnerLog.Valid 8 (innerAD leaf390Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf390CoverageChecked

private noncomputable def leaf390InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf390InputLogOnePlusV_eq :
    leaf390InputLogOnePlusV = outerEnclosure 24
      (leaf390Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf390RoundedFacts : LeafRoundedFacts 8
    leaf390Certificate.logOnePlusV leaf390InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf390InputLogOnePlusV_eq }

private noncomputable def leaf390Inputs : Inputs :=
  inputsOfCaches globalInput sk58RoundedInputs
    chi55InputQChi innerPair35Input
    leaf390InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf390LowerChecked :
    lowerCheck 24 leaf390Box leaf390Inputs = true := by
  rfl'

private theorem leaf390CoversExact : CoversExact 8
    leaf390Box leaf390Certificate leaf390InnerLog leaf390Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk58RoundedFacts chi55RoundedFacts
    innerPair35RoundedFacts leaf390RoundedFacts (by rfl)

private theorem leaf390FlatSound : Sound leaf390Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf390CertificateValid
    leaf390InnerLogValid leaf390CoversExact leaf390LowerChecked

private noncomputable def leaf391Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf391Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217879/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717422592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (194998507/134217728) }, upper := { exponent := 0, mantissa := (3051/2048) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435916287/137434845184) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf391InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf391LocalValidity :
    LeafFacts leaf391Box leaf391Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf391Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717422592) }) = true
      norm_num [leaf391Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf391CertificateValid :
    WideCertificateValid leaf391Box leaf391Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi54ValidityFacts
    leaf391LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf391CoverageChecked :
    coverageCheck (innerAD leaf391Box) leaf391InnerLog = true := by
  rfl'

private theorem leaf391InnerLogValid :
    leaf391InnerLog.Valid 8 (innerAD leaf391Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf391CoverageChecked

private noncomputable def leaf391InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf391InputLogOnePlusV_eq :
    leaf391InputLogOnePlusV = outerEnclosure 24
      (leaf391Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf391RoundedFacts : LeafRoundedFacts 8
    leaf391Certificate.logOnePlusV leaf391InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf391InputLogOnePlusV_eq }

private noncomputable def leaf391Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi54InputQChi innerPair34Input
    leaf391InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf391LowerChecked :
    lowerCheck 24 leaf391Box leaf391Inputs = true := by
  rfl'

private theorem leaf391CoversExact : CoversExact 8
    leaf391Box leaf391Certificate leaf391InnerLog leaf391Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi54RoundedFacts
    innerPair34RoundedFacts leaf391RoundedFacts (by rfl)

private theorem leaf391FlatSound : Sound leaf391Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf391CertificateValid
    leaf391InnerLogValid leaf391CoversExact leaf391LowerChecked

private noncomputable def leaf392Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf392Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217881/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717387776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (196047017/134217728) }, upper := { exponent := 0, mantissa := (767/512) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435881471/137434775552) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf392InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf392LocalValidity :
    LeafFacts leaf392Box leaf392Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf392Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717387776) }) = true
      norm_num [leaf392Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf392CertificateValid :
    WideCertificateValid leaf392Box leaf392Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi54ValidityFacts
    leaf392LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf392CoverageChecked :
    coverageCheck (innerAD leaf392Box) leaf392InnerLog = true := by
  rfl'

private theorem leaf392InnerLogValid :
    leaf392InnerLog.Valid 8 (innerAD leaf392Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf392CoverageChecked

private noncomputable def leaf392InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf392InputLogOnePlusV_eq :
    leaf392InputLogOnePlusV = outerEnclosure 24
      (leaf392Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf392RoundedFacts : LeafRoundedFacts 8
    leaf392Certificate.logOnePlusV leaf392InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf392InputLogOnePlusV_eq }

private noncomputable def leaf392Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi54InputQChi innerPair34Input
    leaf392InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf392LowerChecked :
    lowerCheck 24 leaf392Box leaf392Inputs = true := by
  rfl'

private theorem leaf392CoversExact : CoversExact 8
    leaf392Box leaf392Certificate leaf392InnerLog leaf392Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi54RoundedFacts
    innerPair34RoundedFacts leaf392RoundedFacts (by rfl)

private theorem leaf392FlatSound : Sound leaf392Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf392CertificateValid
    leaf392InnerLogValid leaf392CoversExact leaf392LowerChecked

private noncomputable def leaf393Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf393Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217881/134217728) }, vSqrt := { lower := (16383/16384), upper := (13743698739/13743460352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (198799361/134217728) }, upper := { exponent := 0, mantissa := (1555/1024) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (27487159091/27486920704) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf393InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf393LocalValidity :
    LeafFacts leaf393Box leaf393Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf393Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (13743698739/13743460352) }) = true
      norm_num [leaf393Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf393CertificateValid :
    WideCertificateValid leaf393Box leaf393Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi55ValidityFacts
    leaf393LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf393CoverageChecked :
    coverageCheck (innerAD leaf393Box) leaf393InnerLog = true := by
  rfl'

private theorem leaf393InnerLogValid :
    leaf393InnerLog.Valid 8 (innerAD leaf393Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf393CoverageChecked

private noncomputable def leaf393InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf393InputLogOnePlusV_eq :
    leaf393InputLogOnePlusV = outerEnclosure 24
      (leaf393Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf393RoundedFacts : LeafRoundedFacts 8
    leaf393Certificate.logOnePlusV leaf393InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf393InputLogOnePlusV_eq }

private noncomputable def leaf393Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi55InputQChi innerPair35Input
    leaf393InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf393LowerChecked :
    lowerCheck 24 leaf393Box leaf393Inputs = true := by
  rfl'

private theorem leaf393CoversExact : CoversExact 8
    leaf393Box leaf393Certificate leaf393InnerLog leaf393Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi55RoundedFacts
    innerPair35RoundedFacts leaf393RoundedFacts (by rfl)

private theorem leaf393FlatSound : Sound leaf393Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf393CertificateValid
    leaf393InnerLogValid leaf393CoversExact leaf393LowerChecked

private noncomputable def leaf394Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf394Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217883/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717264896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (199913403/134217728) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435758591/137434529792) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf394InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf394LocalValidity :
    LeafFacts leaf394Box leaf394Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf394Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717264896) }) = true
      norm_num [leaf394Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf394CertificateValid :
    WideCertificateValid leaf394Box leaf394Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi55ValidityFacts
    leaf394LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf394CoverageChecked :
    coverageCheck (innerAD leaf394Box) leaf394InnerLog = true := by
  rfl'

private theorem leaf394InnerLogValid :
    leaf394InnerLog.Valid 8 (innerAD leaf394Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf394CoverageChecked

private noncomputable def leaf394InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf394InputLogOnePlusV_eq :
    leaf394InputLogOnePlusV = outerEnclosure 24
      (leaf394Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf394RoundedFacts : LeafRoundedFacts 8
    leaf394Certificate.logOnePlusV leaf394InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf394InputLogOnePlusV_eq }

private noncomputable def leaf394Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi55InputQChi innerPair35Input
    leaf394InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf394LowerChecked :
    lowerCheck 24 leaf394Box leaf394Inputs = true := by
  rfl'

private theorem leaf394CoversExact : CoversExact 8
    leaf394Box leaf394Certificate leaf394InnerLog leaf394Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi55RoundedFacts
    innerPair35RoundedFacts leaf394RoundedFacts (by rfl)

private theorem leaf394FlatSound : Sound leaf394Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf394CertificateValid
    leaf394InnerLogValid leaf394CoversExact leaf394LowerChecked

private noncomputable def leaf395Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf395Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108959/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871721984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (100104131/67108864) }, upper := { exponent := 0, mantissa := (1575/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743577907/13743443968) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf395InnerLog : WideLogData :=
  innerPair180Data

set_option maxRecDepth 1000000 in
private theorem leaf395LocalValidity :
    LeafFacts leaf395Box leaf395Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf395Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871721984) }) = true
      norm_num [leaf395Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf395CertificateValid :
    WideCertificateValid leaf395Box leaf395Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi56ValidityFacts
    leaf395LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf395CoverageChecked :
    coverageCheck (innerAD leaf395Box) leaf395InnerLog = true := by
  rfl'

private theorem leaf395InnerLogValid :
    leaf395InnerLog.Valid 8 (innerAD leaf395Box) :=
  wideLogDataValid_of_cachedCheck endpoint50PositiveFacts
    endpoint51PositiveFacts.valid leaf395CoverageChecked

private noncomputable def leaf395InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf395InputLogOnePlusV_eq :
    leaf395InputLogOnePlusV = outerEnclosure 24
      (leaf395Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf395RoundedFacts : LeafRoundedFacts 8
    leaf395Certificate.logOnePlusV leaf395InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf395InputLogOnePlusV_eq }

private noncomputable def leaf395Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi56InputQChi innerPair180Input
    leaf395InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf395LowerChecked :
    lowerCheck 24 leaf395Box leaf395Inputs = true := by
  rfl'

private theorem leaf395CoversExact : CoversExact 8
    leaf395Box leaf395Certificate leaf395InnerLog leaf395Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi56RoundedFacts
    innerPair180RoundedFacts leaf395RoundedFacts (by rfl)

private theorem leaf395FlatSound : Sound leaf395Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf395CertificateValid
    leaf395InnerLogValid leaf395CoversExact leaf395LowerChecked

private noncomputable def leaf396Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf396Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108961/67108864) }, vSqrt := { lower := (16383/16384), upper := (11453093205/11452850176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (101939025/67108864) }, upper := { exponent := 0, mantissa := (401/256) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (22905943381/22905700352) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf396InnerLog : WideLogData :=
  innerPair179Data

set_option maxRecDepth 1000000 in
private theorem leaf396LocalValidity :
    LeafFacts leaf396Box leaf396Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf396Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (11453093205/11452850176) }) = true
      norm_num [leaf396Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf396CertificateValid :
    WideCertificateValid leaf396Box leaf396Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi57ValidityFacts
    leaf396LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf396CoverageChecked :
    coverageCheck (innerAD leaf396Box) leaf396InnerLog = true := by
  rfl'

private theorem leaf396InnerLogValid :
    leaf396InnerLog.Valid 8 (innerAD leaf396Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint52PositiveFacts.valid leaf396CoverageChecked

private noncomputable def leaf396InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf396InputLogOnePlusV_eq :
    leaf396InputLogOnePlusV = outerEnclosure 24
      (leaf396Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf396RoundedFacts : LeafRoundedFacts 8
    leaf396Certificate.logOnePlusV leaf396InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf396InputLogOnePlusV_eq }

private noncomputable def leaf396Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi57InputQChi innerPair179Input
    leaf396InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf396LowerChecked :
    lowerCheck 24 leaf396Box leaf396Inputs = true := by
  rfl'

private theorem leaf396CoversExact : CoversExact 8
    leaf396Box leaf396Certificate leaf396InnerLog leaf396Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi57RoundedFacts
    innerPair179RoundedFacts leaf396RoundedFacts (by rfl)

private theorem leaf396FlatSound : Sound leaf396Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf396CertificateValid
    leaf396InnerLogValid leaf396CoversExact leaf396LowerChecked

private noncomputable def leaf397Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf397Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217883/134217728) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905726976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (202600215/134217728) }, upper := { exponent := 0, mantissa := (3169/2048) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811891541/45811453952) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf397InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf397LocalValidity :
    LeafFacts leaf397Box leaf397Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf397Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905726976) }) = true
      norm_num [leaf397Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf397CertificateValid :
    WideCertificateValid leaf397Box leaf397Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi56ValidityFacts
    leaf397LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf397CoverageChecked :
    coverageCheck (innerAD leaf397Box) leaf397InnerLog = true := by
  rfl'

private theorem leaf397InnerLogValid :
    leaf397InnerLog.Valid 8 (innerAD leaf397Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf397CoverageChecked

private noncomputable def leaf397InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf397InputLogOnePlusV_eq :
    leaf397InputLogOnePlusV = outerEnclosure 24
      (leaf397Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf397RoundedFacts : LeafRoundedFacts 8
    leaf397Certificate.logOnePlusV leaf397InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf397InputLogOnePlusV_eq }

private noncomputable def leaf397Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi56InputQChi innerPair40Input
    leaf397InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf397LowerChecked :
    lowerCheck 24 leaf397Box leaf397Inputs = true := by
  rfl'

private theorem leaf397CoversExact : CoversExact 8
    leaf397Box leaf397Certificate leaf397InnerLog leaf397Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi56RoundedFacts
    innerPair40RoundedFacts leaf397RoundedFacts (by rfl)

private theorem leaf397FlatSound : Sound leaf397Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf397CertificateValid
    leaf397InnerLogValid leaf397CoversExact leaf397LowerChecked

private noncomputable def leaf398Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf398Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217885/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717142016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (203779789/134217728) }, upper := { exponent := 0, mantissa := (797/512) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435635711/137434284032) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf398InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf398LocalValidity :
    LeafFacts leaf398Box leaf398Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf398Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717142016) }) = true
      norm_num [leaf398Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf398CertificateValid :
    WideCertificateValid leaf398Box leaf398Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi56ValidityFacts
    leaf398LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf398CoverageChecked :
    coverageCheck (innerAD leaf398Box) leaf398InnerLog = true := by
  rfl'

private theorem leaf398InnerLogValid :
    leaf398InnerLog.Valid 8 (innerAD leaf398Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf398CoverageChecked

private noncomputable def leaf398InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf398InputLogOnePlusV_eq :
    leaf398InputLogOnePlusV = outerEnclosure 24
      (leaf398Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf398RoundedFacts : LeafRoundedFacts 8
    leaf398Certificate.logOnePlusV leaf398InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf398InputLogOnePlusV_eq }

private noncomputable def leaf398Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi56InputQChi innerPair40Input
    leaf398InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf398LowerChecked :
    lowerCheck 24 leaf398Box leaf398Inputs = true := by
  rfl'

private theorem leaf398CoversExact : CoversExact 8
    leaf398Box leaf398Certificate leaf398InnerLog leaf398Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi56RoundedFacts
    innerPair40RoundedFacts leaf398RoundedFacts (by rfl)

private theorem leaf398FlatSound : Sound leaf398Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf398CertificateValid
    leaf398InnerLogValid leaf398CoversExact leaf398LowerChecked

private noncomputable def leaf399Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf399Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217885/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717060096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (206401069/134217728) }, upper := { exponent := 0, mantissa := (807/512) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435553791/137434120192) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf399InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf399LocalValidity :
    LeafFacts leaf399Box leaf399Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf399Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717060096) }) = true
      norm_num [leaf399Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf399CertificateValid :
    WideCertificateValid leaf399Box leaf399Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi57ValidityFacts
    leaf399LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf399CoverageChecked :
    coverageCheck (innerAD leaf399Box) leaf399InnerLog = true := by
  rfl'

private theorem leaf399InnerLogValid :
    leaf399InnerLog.Valid 8 (innerAD leaf399Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf399CoverageChecked

private noncomputable def leaf399InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf399InputLogOnePlusV_eq :
    leaf399InputLogOnePlusV = outerEnclosure 24
      (leaf399Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf399RoundedFacts : LeafRoundedFacts 8
    leaf399Certificate.logOnePlusV leaf399InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf399InputLogOnePlusV_eq }

private noncomputable def leaf399Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi57InputQChi innerPair41Input
    leaf399InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf399LowerChecked :
    lowerCheck 24 leaf399Box leaf399Inputs = true := by
  rfl'

private theorem leaf399CoversExact : CoversExact 8
    leaf399Box leaf399Certificate leaf399InnerLog leaf399Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi57RoundedFacts
    innerPair41RoundedFacts leaf399RoundedFacts (by rfl)

private theorem leaf399FlatSound : Sound leaf399Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf399CertificateValid
    leaf399InnerLogValid leaf399CoversExact leaf399LowerChecked

private noncomputable def leaf400Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf400Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217887/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717019136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (207646175/134217728) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435512831/137434038272) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf400InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf400LocalValidity :
    LeafFacts leaf400Box leaf400Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf400Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717019136) }) = true
      norm_num [leaf400Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf400CertificateValid :
    WideCertificateValid leaf400Box leaf400Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi57ValidityFacts
    leaf400LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf400CoverageChecked :
    coverageCheck (innerAD leaf400Box) leaf400InnerLog = true := by
  rfl'

private theorem leaf400InnerLogValid :
    leaf400InnerLog.Valid 8 (innerAD leaf400Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf400CoverageChecked

private noncomputable def leaf400InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf400InputLogOnePlusV_eq :
    leaf400InputLogOnePlusV = outerEnclosure 24
      (leaf400Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf400RoundedFacts : LeafRoundedFacts 8
    leaf400Certificate.logOnePlusV leaf400InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf400InputLogOnePlusV_eq }

private noncomputable def leaf400Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi57InputQChi innerPair41Input
    leaf400InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf400LowerChecked :
    lowerCheck 24 leaf400Box leaf400Inputs = true := by
  rfl'

private theorem leaf400CoversExact : CoversExact 8
    leaf400Box leaf400Certificate leaf400InnerLog leaf400Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi57RoundedFacts
    innerPair41RoundedFacts leaf400RoundedFacts (by rfl)

private theorem leaf400FlatSound : Sound leaf400Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf400CertificateValid
    leaf400InnerLogValid leaf400CoversExact leaf400LowerChecked

private noncomputable def leaf401Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf401Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217883/134217728) }, vSqrt := { lower := (16383/16384), upper := (4581232913/4581156864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (197095527/134217728) }, upper := { exponent := 0, mantissa := (3085/2048) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (9162389777/9162313728) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf401InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf401LocalValidity :
    LeafFacts leaf401Box leaf401Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf401Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4581232913/4581156864) }) = true
      norm_num [leaf401Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf401CertificateValid :
    WideCertificateValid leaf401Box leaf401Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi54ValidityFacts
    leaf401LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf401CoverageChecked :
    coverageCheck (innerAD leaf401Box) leaf401InnerLog = true := by
  rfl'

private theorem leaf401InnerLogValid :
    leaf401InnerLog.Valid 8 (innerAD leaf401Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf401CoverageChecked

private noncomputable def leaf401InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf401InputLogOnePlusV_eq :
    leaf401InputLogOnePlusV = outerEnclosure 24
      (leaf401Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf401RoundedFacts : LeafRoundedFacts 8
    leaf401Certificate.logOnePlusV leaf401InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf401InputLogOnePlusV_eq }

private noncomputable def leaf401Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi54InputQChi innerPair35Input
    leaf401InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf401LowerChecked :
    lowerCheck 24 leaf401Box leaf401Inputs = true := by
  rfl'

private theorem leaf401CoversExact : CoversExact 8
    leaf401Box leaf401Certificate leaf401InnerLog leaf401Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi54RoundedFacts
    innerPair35RoundedFacts leaf401RoundedFacts (by rfl)

private theorem leaf401FlatSound : Sound leaf401Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf401CertificateValid
    leaf401InnerLogValid leaf401CoversExact leaf401LowerChecked

private noncomputable def leaf402Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf402Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217885/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717318144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (198144037/134217728) }, upper := { exponent := 0, mantissa := (1551/1024) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435811839/137434636288) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf402InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf402LocalValidity :
    LeafFacts leaf402Box leaf402Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf402Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717318144) }) = true
      norm_num [leaf402Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf402CertificateValid :
    WideCertificateValid leaf402Box leaf402Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi54ValidityFacts
    leaf402LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf402CoverageChecked :
    coverageCheck (innerAD leaf402Box) leaf402InnerLog = true := by
  rfl'

private theorem leaf402InnerLogValid :
    leaf402InnerLog.Valid 8 (innerAD leaf402Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf402CoverageChecked

private noncomputable def leaf402InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf402InputLogOnePlusV_eq :
    leaf402InputLogOnePlusV = outerEnclosure 24
      (leaf402Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf402RoundedFacts : LeafRoundedFacts 8
    leaf402Certificate.logOnePlusV leaf402InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf402InputLogOnePlusV_eq }

private noncomputable def leaf402Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi54InputQChi innerPair35Input
    leaf402InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf402LowerChecked :
    lowerCheck 24 leaf402Box leaf402Inputs = true := by
  rfl'

private theorem leaf402CoversExact : CoversExact 8
    leaf402Box leaf402Certificate leaf402InnerLog leaf402Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi54RoundedFacts
    innerPair35RoundedFacts leaf402RoundedFacts (by rfl)

private theorem leaf402FlatSound : Sound leaf402Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf402CertificateValid
    leaf402InnerLogValid leaf402CoversExact leaf402LowerChecked

private noncomputable def leaf403Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf403Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217885/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717228032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (201027445/134217728) }, upper := { exponent := 0, mantissa := (1573/1024) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435721727/137434456064) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf403InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf403LocalValidity :
    LeafFacts leaf403Box leaf403Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf403Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717228032) }) = true
      norm_num [leaf403Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf403CertificateValid :
    WideCertificateValid leaf403Box leaf403Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi55ValidityFacts
    leaf403LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf403CoverageChecked :
    coverageCheck (innerAD leaf403Box) leaf403InnerLog = true := by
  rfl'

private theorem leaf403InnerLogValid :
    leaf403InnerLog.Valid 8 (innerAD leaf403Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf403CoverageChecked

private noncomputable def leaf403InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf403InputLogOnePlusV_eq :
    leaf403InputLogOnePlusV = outerEnclosure 24
      (leaf403Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf403RoundedFacts : LeafRoundedFacts 8
    leaf403Certificate.logOnePlusV leaf403InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf403InputLogOnePlusV_eq }

private noncomputable def leaf403Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi55InputQChi innerPair35Input
    leaf403InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf403LowerChecked :
    lowerCheck 24 leaf403Box leaf403Inputs = true := by
  rfl'

private theorem leaf403CoversExact : CoversExact 8
    leaf403Box leaf403Certificate leaf403InnerLog leaf403Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi55RoundedFacts
    innerPair35RoundedFacts leaf403RoundedFacts (by rfl)

private theorem leaf403FlatSound : Sound leaf403Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf403CertificateValid
    leaf403InnerLogValid leaf403CoversExact leaf403LowerChecked

private noncomputable def leaf404Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf404Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217887/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717191168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (202141487/134217728) }, upper := { exponent := 0, mantissa := (791/512) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435684863/137434382336) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf404InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf404LocalValidity :
    LeafFacts leaf404Box leaf404Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf404Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717191168) }) = true
      norm_num [leaf404Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf404CertificateValid :
    WideCertificateValid leaf404Box leaf404Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi55ValidityFacts
    leaf404LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf404CoverageChecked :
    coverageCheck (innerAD leaf404Box) leaf404InnerLog = true := by
  rfl'

private theorem leaf404InnerLogValid :
    leaf404InnerLog.Valid 8 (innerAD leaf404Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf404CoverageChecked

private noncomputable def leaf404InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf404InputLogOnePlusV_eq :
    leaf404InputLogOnePlusV = outerEnclosure 24
      (leaf404Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf404RoundedFacts : LeafRoundedFacts 8
    leaf404Certificate.logOnePlusV leaf404InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf404InputLogOnePlusV_eq }

private noncomputable def leaf404Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi55InputQChi innerPair40Input
    leaf404InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf404LowerChecked :
    lowerCheck 24 leaf404Box leaf404Inputs = true := by
  rfl'

private theorem leaf404CoversExact : CoversExact 8
    leaf404Box leaf404Certificate leaf404InnerLog leaf404Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi55RoundedFacts
    innerPair40RoundedFacts leaf404RoundedFacts (by rfl)

private theorem leaf404FlatSound : Sound leaf404Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf404CertificateValid
    leaf404InnerLogValid leaf404CoversExact leaf404LowerChecked

private noncomputable def leaf405Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf405Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217887/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717283328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (199192547/134217728) }, upper := { exponent := 0, mantissa := (3119/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435777023/137434566656) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf405InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf405LocalValidity :
    LeafFacts leaf405Box leaf405Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf405Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717283328) }) = true
      norm_num [leaf405Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf405CertificateValid :
    WideCertificateValid leaf405Box leaf405Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi54ValidityFacts
    leaf405LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf405CoverageChecked :
    coverageCheck (innerAD leaf405Box) leaf405InnerLog = true := by
  rfl'

private theorem leaf405InnerLogValid :
    leaf405InnerLog.Valid 8 (innerAD leaf405Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf405CoverageChecked

private noncomputable def leaf405InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf405InputLogOnePlusV_eq :
    leaf405InputLogOnePlusV = outerEnclosure 24
      (leaf405Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf405RoundedFacts : LeafRoundedFacts 8
    leaf405Certificate.logOnePlusV leaf405InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf405InputLogOnePlusV_eq }

private noncomputable def leaf405Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi54InputQChi innerPair35Input
    leaf405InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf405LowerChecked :
    lowerCheck 24 leaf405Box leaf405Inputs = true := by
  rfl'

private theorem leaf405CoversExact : CoversExact 8
    leaf405Box leaf405Certificate leaf405InnerLog leaf405Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi54RoundedFacts
    innerPair35RoundedFacts leaf405RoundedFacts (by rfl)

private theorem leaf405FlatSound : Sound leaf405Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf405CertificateValid
    leaf405InnerLogValid leaf405CoversExact leaf405LowerChecked

private noncomputable def leaf406Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (1/4), chiHi := (17/64) }

private noncomputable def leaf406Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217889/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905749504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (200241057/134217728) }, upper := { exponent := 0, mantissa := (49/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi54LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811914069/45811499008) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf406InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf406LocalValidity :
    LeafFacts leaf406Box leaf406Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf406Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905749504) }) = true
      norm_num [leaf406Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf406CertificateValid :
    WideCertificateValid leaf406Box leaf406Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi54ValidityFacts
    leaf406LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf406CoverageChecked :
    coverageCheck (innerAD leaf406Box) leaf406InnerLog = true := by
  rfl'

private theorem leaf406InnerLogValid :
    leaf406InnerLog.Valid 8 (innerAD leaf406Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf406CoverageChecked

private noncomputable def leaf406InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf406InputLogOnePlusV_eq :
    leaf406InputLogOnePlusV = outerEnclosure 24
      (leaf406Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf406RoundedFacts : LeafRoundedFacts 8
    leaf406Certificate.logOnePlusV leaf406InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf406InputLogOnePlusV_eq }

private noncomputable def leaf406Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi54InputQChi innerPair35Input
    leaf406InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf406LowerChecked :
    lowerCheck 24 leaf406Box leaf406Inputs = true := by
  rfl'

private theorem leaf406CoversExact : CoversExact 8
    leaf406Box leaf406Certificate leaf406InnerLog leaf406Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi54RoundedFacts
    innerPair35RoundedFacts leaf406RoundedFacts (by rfl)

private theorem leaf406FlatSound : Sound leaf406Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf406CertificateValid
    leaf406InnerLogValid leaf406CoversExact leaf406LowerChecked

private noncomputable def leaf407Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf407Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217889/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717154304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (203255529/134217728) }, upper := { exponent := 0, mantissa := (1591/1024) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435647999/137434308608) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf407InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf407LocalValidity :
    LeafFacts leaf407Box leaf407Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf407Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717154304) }) = true
      norm_num [leaf407Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf407CertificateValid :
    WideCertificateValid leaf407Box leaf407Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi55ValidityFacts
    leaf407LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf407CoverageChecked :
    coverageCheck (innerAD leaf407Box) leaf407InnerLog = true := by
  rfl'

private theorem leaf407InnerLogValid :
    leaf407InnerLog.Valid 8 (innerAD leaf407Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf407CoverageChecked

private noncomputable def leaf407InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf407InputLogOnePlusV_eq :
    leaf407InputLogOnePlusV = outerEnclosure 24
      (leaf407Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf407RoundedFacts : LeafRoundedFacts 8
    leaf407Certificate.logOnePlusV leaf407InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf407InputLogOnePlusV_eq }

private noncomputable def leaf407Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi55InputQChi innerPair40Input
    leaf407InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf407LowerChecked :
    lowerCheck 24 leaf407Box leaf407Inputs = true := by
  rfl'

private theorem leaf407CoversExact : CoversExact 8
    leaf407Box leaf407Certificate leaf407InnerLog leaf407Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi55RoundedFacts
    innerPair40RoundedFacts leaf407RoundedFacts (by rfl)

private theorem leaf407FlatSound : Sound leaf407Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf407CertificateValid
    leaf407InnerLogValid leaf407CoversExact leaf407LowerChecked

private noncomputable def leaf408Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (17/64), chiHi := (9/32) }

private noncomputable def leaf408Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217891/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743423488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (204369571/134217728) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi55LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27487122227/27486846976) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf408InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf408LocalValidity :
    LeafFacts leaf408Box leaf408Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf408Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743423488) }) = true
      norm_num [leaf408Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf408CertificateValid :
    WideCertificateValid leaf408Box leaf408Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi55ValidityFacts
    leaf408LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf408CoverageChecked :
    coverageCheck (innerAD leaf408Box) leaf408InnerLog = true := by
  rfl'

private theorem leaf408InnerLogValid :
    leaf408InnerLog.Valid 8 (innerAD leaf408Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf408CoverageChecked

private noncomputable def leaf408InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf408InputLogOnePlusV_eq :
    leaf408InputLogOnePlusV = outerEnclosure 24
      (leaf408Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf408RoundedFacts : LeafRoundedFacts 8
    leaf408Certificate.logOnePlusV leaf408InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf408InputLogOnePlusV_eq }

private noncomputable def leaf408Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi55InputQChi innerPair40Input
    leaf408InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf408LowerChecked :
    lowerCheck 24 leaf408Box leaf408Inputs = true := by
  rfl'

private theorem leaf408CoversExact : CoversExact 8
    leaf408Box leaf408Certificate leaf408InnerLog leaf408Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi55RoundedFacts
    innerPair40RoundedFacts leaf408RoundedFacts (by rfl)

private theorem leaf408FlatSound : Sound leaf408Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf408CertificateValid
    leaf408InnerLogValid leaf408CoversExact leaf408LowerChecked

private noncomputable def leaf409Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf409Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217887/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68717103104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (204959363/134217728) }, upper := { exponent := 0, mantissa := (3207/2048) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435596799/137434206208) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf409InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf409LocalValidity :
    LeafFacts leaf409Box leaf409Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf409Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68717103104) }) = true
      norm_num [leaf409Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf409CertificateValid :
    WideCertificateValid leaf409Box leaf409Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi56ValidityFacts
    leaf409LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf409CoverageChecked :
    coverageCheck (innerAD leaf409Box) leaf409InnerLog = true := by
  rfl'

private theorem leaf409InnerLogValid :
    leaf409InnerLog.Valid 8 (innerAD leaf409Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf409CoverageChecked

private noncomputable def leaf409InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf409InputLogOnePlusV_eq :
    leaf409InputLogOnePlusV = outerEnclosure 24
      (leaf409Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf409RoundedFacts : LeafRoundedFacts 8
    leaf409Certificate.logOnePlusV leaf409InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf409InputLogOnePlusV_eq }

private noncomputable def leaf409Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi56InputQChi innerPair41Input
    leaf409InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf409LowerChecked :
    lowerCheck 24 leaf409Box leaf409Inputs = true := by
  rfl'

private theorem leaf409CoversExact : CoversExact 8
    leaf409Box leaf409Certificate leaf409InnerLog leaf409Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi56RoundedFacts
    innerPair41RoundedFacts leaf409RoundedFacts (by rfl)

private theorem leaf409FlatSound : Sound leaf409Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf409CertificateValid
    leaf409InnerLogValid leaf409CoversExact leaf409LowerChecked

private noncomputable def leaf410Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf410Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217889/134217728) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905688064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (206138937/134217728) }, upper := { exponent := 0, mantissa := (1613/1024) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811852629/45811376128) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf410InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf410LocalValidity :
    LeafFacts leaf410Box leaf410Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf410Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905688064) }) = true
      norm_num [leaf410Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf410CertificateValid :
    WideCertificateValid leaf410Box leaf410Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi56ValidityFacts
    leaf410LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf410CoverageChecked :
    coverageCheck (innerAD leaf410Box) leaf410InnerLog = true := by
  rfl'

private theorem leaf410InnerLogValid :
    leaf410InnerLog.Valid 8 (innerAD leaf410Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf410CoverageChecked

private noncomputable def leaf410InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf410InputLogOnePlusV_eq :
    leaf410InputLogOnePlusV = outerEnclosure 24
      (leaf410Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf410RoundedFacts : LeafRoundedFacts 8
    leaf410Certificate.logOnePlusV leaf410InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf410InputLogOnePlusV_eq }

private noncomputable def leaf410Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi56InputQChi innerPair41Input
    leaf410InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf410LowerChecked :
    lowerCheck 24 leaf410Box leaf410Inputs = true := by
  rfl'

private theorem leaf410CoversExact : CoversExact 8
    leaf410Box leaf410Certificate leaf410InnerLog leaf410Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi56RoundedFacts
    innerPair41RoundedFacts leaf410RoundedFacts (by rfl)

private theorem leaf410FlatSound : Sound leaf410Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf410CertificateValid
    leaf410InnerLogValid leaf410CoversExact leaf410LowerChecked

private noncomputable def leaf411Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf411Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217889/134217728) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905659392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (208891281/134217728) }, upper := { exponent := 0, mantissa := (817/512) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811823957/45811318784) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf411InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf411LocalValidity :
    LeafFacts leaf411Box leaf411Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf411Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905659392) }) = true
      norm_num [leaf411Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf411CertificateValid :
    WideCertificateValid leaf411Box leaf411Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi57ValidityFacts
    leaf411LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf411CoverageChecked :
    coverageCheck (innerAD leaf411Box) leaf411InnerLog = true := by
  rfl'

private theorem leaf411InnerLogValid :
    leaf411InnerLog.Valid 8 (innerAD leaf411Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf411CoverageChecked

private noncomputable def leaf411InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf411InputLogOnePlusV_eq :
    leaf411InputLogOnePlusV = outerEnclosure 24
      (leaf411Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf411RoundedFacts : LeafRoundedFacts 8
    leaf411Certificate.logOnePlusV leaf411InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf411InputLogOnePlusV_eq }

private noncomputable def leaf411Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi57InputQChi innerPair41Input
    leaf411InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf411LowerChecked :
    lowerCheck 24 leaf411Box leaf411Inputs = true := by
  rfl'

private theorem leaf411CoversExact : CoversExact 8
    leaf411Box leaf411Certificate leaf411InnerLog leaf411Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi57RoundedFacts
    innerPair41RoundedFacts leaf411RoundedFacts (by rfl)

private theorem leaf411FlatSound : Sound leaf411Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf411CertificateValid
    leaf411InnerLogValid leaf411CoversExact leaf411LowerChecked

private noncomputable def leaf412Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf412Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217891/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716937216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (210136387/134217728) }, upper := { exponent := 0, mantissa := (411/256) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435430911/137433874432) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf412InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf412LocalValidity :
    LeafFacts leaf412Box leaf412Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf412Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716937216) }) = true
      norm_num [leaf412Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf412CertificateValid :
    WideCertificateValid leaf412Box leaf412Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi57ValidityFacts
    leaf412LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf412CoverageChecked :
    coverageCheck (innerAD leaf412Box) leaf412InnerLog = true := by
  rfl'

private theorem leaf412InnerLogValid :
    leaf412InnerLog.Valid 8 (innerAD leaf412Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf412CoverageChecked

private noncomputable def leaf412InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf412InputLogOnePlusV_eq :
    leaf412InputLogOnePlusV = outerEnclosure 24
      (leaf412Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf412RoundedFacts : LeafRoundedFacts 8
    leaf412Certificate.logOnePlusV leaf412InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf412InputLogOnePlusV_eq }

private noncomputable def leaf412Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi57InputQChi innerPair50Input
    leaf412InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf412LowerChecked :
    lowerCheck 24 leaf412Box leaf412Inputs = true := by
  rfl'

private theorem leaf412CoversExact : CoversExact 8
    leaf412Box leaf412Certificate leaf412InnerLog leaf412Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi57RoundedFacts
    innerPair50RoundedFacts leaf412RoundedFacts (by rfl)

private theorem leaf412FlatSound : Sound leaf412Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf412CertificateValid
    leaf412InnerLogValid leaf412CoversExact leaf412LowerChecked

private noncomputable def leaf413Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf413Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217891/134217728) }, vSqrt := { lower := (16383/16384), upper := (13743698739/13743405056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (207318511/134217728) }, upper := { exponent := 0, mantissa := (3245/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (27487103795/27486810112) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf413InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf413LocalValidity :
    LeafFacts leaf413Box leaf413Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf413Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (13743698739/13743405056) }) = true
      norm_num [leaf413Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf413CertificateValid :
    WideCertificateValid leaf413Box leaf413Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi56ValidityFacts
    leaf413LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf413CoverageChecked :
    coverageCheck (innerAD leaf413Box) leaf413InnerLog = true := by
  rfl'

private theorem leaf413InnerLogValid :
    leaf413InnerLog.Valid 8 (innerAD leaf413Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf413CoverageChecked

private noncomputable def leaf413InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf413InputLogOnePlusV_eq :
    leaf413InputLogOnePlusV = outerEnclosure 24
      (leaf413Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf413RoundedFacts : LeafRoundedFacts 8
    leaf413Certificate.logOnePlusV leaf413InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf413InputLogOnePlusV_eq }

private noncomputable def leaf413Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi56InputQChi innerPair41Input
    leaf413InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf413LowerChecked :
    lowerCheck 24 leaf413Box leaf413Inputs = true := by
  rfl'

private theorem leaf413CoversExact : CoversExact 8
    leaf413Box leaf413Certificate leaf413InnerLog leaf413Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi56RoundedFacts
    innerPair41RoundedFacts leaf413RoundedFacts (by rfl)

private theorem leaf413FlatSound : Sound leaf413Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf413CertificateValid
    leaf413InnerLogValid leaf413CoversExact leaf413LowerChecked

private noncomputable def leaf414Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (9/32), chiHi := (19/64) }

private noncomputable def leaf414Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217893/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716986368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (208498085/134217728) }, upper := { exponent := 0, mantissa := (51/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi56LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435480063/137433972736) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf414InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf414LocalValidity :
    LeafFacts leaf414Box leaf414Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf414Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716986368) }) = true
      norm_num [leaf414Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf414CertificateValid :
    WideCertificateValid leaf414Box leaf414Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi56ValidityFacts
    leaf414LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf414CoverageChecked :
    coverageCheck (innerAD leaf414Box) leaf414InnerLog = true := by
  rfl'

private theorem leaf414InnerLogValid :
    leaf414InnerLog.Valid 8 (innerAD leaf414Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf414CoverageChecked

private noncomputable def leaf414InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf414InputLogOnePlusV_eq :
    leaf414InputLogOnePlusV = outerEnclosure 24
      (leaf414Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf414RoundedFacts : LeafRoundedFacts 8
    leaf414Certificate.logOnePlusV leaf414InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf414InputLogOnePlusV_eq }

private noncomputable def leaf414Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi56InputQChi innerPair41Input
    leaf414InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf414LowerChecked :
    lowerCheck 24 leaf414Box leaf414Inputs = true := by
  rfl'

private theorem leaf414CoversExact : CoversExact 8
    leaf414Box leaf414Certificate leaf414InnerLog leaf414Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi56RoundedFacts
    innerPair41RoundedFacts leaf414RoundedFacts (by rfl)

private theorem leaf414FlatSound : Sound leaf414Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf414CertificateValid
    leaf414InnerLogValid leaf414CoversExact leaf414LowerChecked

private noncomputable def leaf415Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf415Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217893/134217728) }, vSqrt := { lower := (16383/16384), upper := (4042264335/4042170368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (211381493/134217728) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8084434703/8084340736) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf415InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf415LocalValidity :
    LeafFacts leaf415Box leaf415Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf415Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4042264335/4042170368) }) = true
      norm_num [leaf415Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf415CertificateValid :
    WideCertificateValid leaf415Box leaf415Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi57ValidityFacts
    leaf415LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf415CoverageChecked :
    coverageCheck (innerAD leaf415Box) leaf415InnerLog = true := by
  rfl'

private theorem leaf415InnerLogValid :
    leaf415InnerLog.Valid 8 (innerAD leaf415Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf415CoverageChecked

private noncomputable def leaf415InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf415InputLogOnePlusV_eq :
    leaf415InputLogOnePlusV = outerEnclosure 24
      (leaf415Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf415RoundedFacts : LeafRoundedFacts 8
    leaf415Certificate.logOnePlusV leaf415InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf415InputLogOnePlusV_eq }

private noncomputable def leaf415Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi57InputQChi innerPair50Input
    leaf415InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf415LowerChecked :
    lowerCheck 24 leaf415Box leaf415Inputs = true := by
  rfl'

private theorem leaf415CoversExact : CoversExact 8
    leaf415Box leaf415Certificate leaf415InnerLog leaf415Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi57RoundedFacts
    innerPair50RoundedFacts leaf415RoundedFacts (by rfl)

private theorem leaf415FlatSound : Sound leaf415Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf415CertificateValid
    leaf415InnerLogValid leaf415CoversExact leaf415LowerChecked

private noncomputable def leaf416Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (19/64), chiHi := (5/16) }

private noncomputable def leaf416Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905618432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (212626599/134217728) }, upper := { exponent := 0, mantissa := (13/8) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi57LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811782997/45811236864) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf416InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf416LocalValidity :
    LeafFacts leaf416Box leaf416Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf416Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905618432) }) = true
      norm_num [leaf416Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf416CertificateValid :
    WideCertificateValid leaf416Box leaf416Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi57ValidityFacts
    leaf416LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf416CoverageChecked :
    coverageCheck (innerAD leaf416Box) leaf416InnerLog = true := by
  rfl'

private theorem leaf416InnerLogValid :
    leaf416InnerLog.Valid 8 (innerAD leaf416Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf416CoverageChecked

private noncomputable def leaf416InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf416InputLogOnePlusV_eq :
    leaf416InputLogOnePlusV = outerEnclosure 24
      (leaf416Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf416RoundedFacts : LeafRoundedFacts 8
    leaf416Certificate.logOnePlusV leaf416InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf416InputLogOnePlusV_eq }

private noncomputable def leaf416Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi57InputQChi innerPair50Input
    leaf416InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf416LowerChecked :
    lowerCheck 24 leaf416Box leaf416Inputs = true := by
  rfl'

private theorem leaf416CoversExact : CoversExact 8
    leaf416Box leaf416Certificate leaf416InnerLog leaf416Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi57RoundedFacts
    innerPair50RoundedFacts leaf416RoundedFacts (by rfl)

private theorem leaf416FlatSound : Sound leaf416Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf416CertificateValid
    leaf416InnerLogValid leaf416CoversExact leaf416LowerChecked

private noncomputable def leaf417Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf417Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108963/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358491136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (103773919/67108864) }, upper := { exponent := 0, mantissa := (1633/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717770751/68716982272) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf417InnerLog : WideLogData :=
  innerPair183Data

set_option maxRecDepth 1000000 in
private theorem leaf417LocalValidity :
    LeafFacts leaf417Box leaf417Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf417Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358491136) }) = true
      norm_num [leaf417Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf417CertificateValid :
    WideCertificateValid leaf417Box leaf417Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi58ValidityFacts
    leaf417LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf417CoverageChecked :
    coverageCheck (innerAD leaf417Box) leaf417InnerLog = true := by
  rfl'

private theorem leaf417InnerLogValid :
    leaf417InnerLog.Valid 8 (innerAD leaf417Box) :=
  wideLogDataValid_of_cachedCheck endpoint53PositiveFacts
    endpoint54PositiveFacts.valid leaf417CoverageChecked

private noncomputable def leaf417InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf417InputLogOnePlusV_eq :
    leaf417InputLogOnePlusV = outerEnclosure 24
      (leaf417Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf417RoundedFacts : LeafRoundedFacts 8
    leaf417Certificate.logOnePlusV leaf417InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf417InputLogOnePlusV_eq }

private noncomputable def leaf417Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi58InputQChi innerPair183Input
    leaf417InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf417LowerChecked :
    lowerCheck 24 leaf417Box leaf417Inputs = true := by
  rfl'

private theorem leaf417CoversExact : CoversExact 8
    leaf417Box leaf417Certificate leaf417InnerLog leaf417Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi58RoundedFacts
    innerPair183RoundedFacts leaf417RoundedFacts (by rfl)

private theorem leaf417FlatSound : Sound leaf417Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf417CertificateValid
    leaf417InnerLogValid leaf417CoversExact leaf417LowerChecked

private noncomputable def leaf418Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf418Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108965/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358431744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (105608813/67108864) }, upper := { exponent := 0, mantissa := (831/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717711359/68716863488) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf418InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf418LocalValidity :
    LeafFacts leaf418Box leaf418Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf418Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358431744) }) = true
      norm_num [leaf418Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf418CertificateValid :
    WideCertificateValid leaf418Box leaf418Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi59ValidityFacts
    leaf418LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf418CoverageChecked :
    coverageCheck (innerAD leaf418Box) leaf418InnerLog = true := by
  rfl'

private theorem leaf418InnerLogValid :
    leaf418InnerLog.Valid 8 (innerAD leaf418Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf418CoverageChecked

private noncomputable def leaf418InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf418InputLogOnePlusV_eq :
    leaf418InputLogOnePlusV = outerEnclosure 24
      (leaf418Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf418RoundedFacts : LeafRoundedFacts 8
    leaf418Certificate.logOnePlusV leaf418InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf418InputLogOnePlusV_eq }

private noncomputable def leaf418Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi59InputQChi innerPair50Input
    leaf418InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf418LowerChecked :
    lowerCheck 24 leaf418Box leaf418Inputs = true := by
  rfl'

private theorem leaf418CoversExact : CoversExact 8
    leaf418Box leaf418Certificate leaf418InnerLog leaf418Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi59RoundedFacts
    innerPair50RoundedFacts leaf418RoundedFacts (by rfl)

private theorem leaf418FlatSound : Sound leaf418Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf418CertificateValid
    leaf418InnerLogValid leaf418CoversExact leaf418LowerChecked

private noncomputable def leaf419Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf419Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217887/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716939264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (210201923/134217728) }, upper := { exponent := 0, mantissa := (3287/2048) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435432959/137433878528) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf419InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf419LocalValidity :
    LeafFacts leaf419Box leaf419Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf419Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716939264) }) = true
      norm_num [leaf419Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf419CertificateValid :
    WideCertificateValid leaf419Box leaf419Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi58ValidityFacts
    leaf419LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf419CoverageChecked :
    coverageCheck (innerAD leaf419Box) leaf419InnerLog = true := by
  rfl'

private theorem leaf419InnerLogValid :
    leaf419InnerLog.Valid 8 (innerAD leaf419Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf419CoverageChecked

private noncomputable def leaf419InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf419InputLogOnePlusV_eq :
    leaf419InputLogOnePlusV = outerEnclosure 24
      (leaf419Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf419RoundedFacts : LeafRoundedFacts 8
    leaf419Certificate.logOnePlusV leaf419InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf419InputLogOnePlusV_eq }

private noncomputable def leaf419Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi58InputQChi innerPair50Input
    leaf419InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf419LowerChecked :
    lowerCheck 24 leaf419Box leaf419Inputs = true := by
  rfl'

private theorem leaf419CoversExact : CoversExact 8
    leaf419Box leaf419Certificate leaf419InnerLog leaf419Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi58RoundedFacts
    innerPair50RoundedFacts leaf419RoundedFacts (by rfl)

private theorem leaf419FlatSound : Sound leaf419Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf419CertificateValid
    leaf419InnerLogValid leaf419CoversExact leaf419LowerChecked

private noncomputable def leaf420Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf420Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217889/134217728) }, vSqrt := { lower := (16383/16384), upper := (4042264335/4042170368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (211512561/134217728) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8084434703/8084340736) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf420InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf420LocalValidity :
    LeafFacts leaf420Box leaf420Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf420Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4042264335/4042170368) }) = true
      norm_num [leaf420Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf420CertificateValid :
    WideCertificateValid leaf420Box leaf420Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi58ValidityFacts
    leaf420LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf420CoverageChecked :
    coverageCheck (innerAD leaf420Box) leaf420InnerLog = true := by
  rfl'

private theorem leaf420InnerLogValid :
    leaf420InnerLog.Valid 8 (innerAD leaf420Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf420CoverageChecked

private noncomputable def leaf420InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf420InputLogOnePlusV_eq :
    leaf420InputLogOnePlusV = outerEnclosure 24
      (leaf420Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf420RoundedFacts : LeafRoundedFacts 8
    leaf420Certificate.logOnePlusV leaf420InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf420InputLogOnePlusV_eq }

private noncomputable def leaf420Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi58InputQChi innerPair50Input
    leaf420InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf420LowerChecked :
    lowerCheck 24 leaf420Box leaf420Inputs = true := by
  rfl'

private theorem leaf420CoversExact : CoversExact 8
    leaf420Box leaf420Certificate leaf420InnerLog leaf420Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi58RoundedFacts
    innerPair50RoundedFacts leaf420RoundedFacts (by rfl)

private theorem leaf420FlatSound : Sound leaf420Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf420CertificateValid
    leaf420InnerLogValid leaf420CoversExact leaf420LowerChecked

private noncomputable def leaf421Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (59/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf421Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217889/134217728) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905606144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (214002777/134217728) }, upper := { exponent := 0, mantissa := (1673/1024) } }, logOuter := sk51LogOuterCertificate, logK := sk51LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811770709/45811212288) } }, logDArg := sk51LogDArgCertificate }

private noncomputable def leaf421InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf421LocalValidity :
    LeafFacts leaf421Box leaf421Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf421Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905606144) }) = true
      norm_num [leaf421Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf421CertificateValid :
    WideCertificateValid leaf421Box leaf421Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk51ValidityFacts chi59ValidityFacts
    leaf421LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf421CoverageChecked :
    coverageCheck (innerAD leaf421Box) leaf421InnerLog = true := by
  rfl'

private theorem leaf421InnerLogValid :
    leaf421InnerLog.Valid 8 (innerAD leaf421Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf421CoverageChecked

private noncomputable def leaf421InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf421InputLogOnePlusV_eq :
    leaf421InputLogOnePlusV = outerEnclosure 24
      (leaf421Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf421RoundedFacts : LeafRoundedFacts 8
    leaf421Certificate.logOnePlusV leaf421InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf421InputLogOnePlusV_eq }

private noncomputable def leaf421Inputs : Inputs :=
  inputsOfCaches globalInput sk51RoundedInputs
    chi59InputQChi innerPair51Input
    leaf421InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf421LowerChecked :
    lowerCheck 24 leaf421Box leaf421Inputs = true := by
  rfl'

private theorem leaf421CoversExact : CoversExact 8
    leaf421Box leaf421Certificate leaf421InnerLog leaf421Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk51RoundedFacts chi59RoundedFacts
    innerPair51RoundedFacts leaf421RoundedFacts (by rfl)

private theorem leaf421FlatSound : Sound leaf421Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf421CertificateValid
    leaf421InnerLogValid leaf421CoversExact leaf421LowerChecked

private noncomputable def leaf422Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/32), kHi := (15/8), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf422Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217891/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716773376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (215378947/134217728) }, upper := { exponent := 0, mantissa := (421/256) } }, logOuter := sk52LogOuterCertificate, logK := sk52LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435267071/137433546752) } }, logDArg := sk52LogDArgCertificate }

private noncomputable def leaf422InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf422LocalValidity :
    LeafFacts leaf422Box leaf422Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf422Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716773376) }) = true
      norm_num [leaf422Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf422CertificateValid :
    WideCertificateValid leaf422Box leaf422Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk52ValidityFacts chi59ValidityFacts
    leaf422LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf422CoverageChecked :
    coverageCheck (innerAD leaf422Box) leaf422InnerLog = true := by
  rfl'

private theorem leaf422InnerLogValid :
    leaf422InnerLog.Valid 8 (innerAD leaf422Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf422CoverageChecked

private noncomputable def leaf422InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf422InputLogOnePlusV_eq :
    leaf422InputLogOnePlusV = outerEnclosure 24
      (leaf422Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf422RoundedFacts : LeafRoundedFacts 8
    leaf422Certificate.logOnePlusV leaf422InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf422InputLogOnePlusV_eq }

private noncomputable def leaf422Inputs : Inputs :=
  inputsOfCaches globalInput sk52RoundedInputs
    chi59InputQChi innerPair51Input
    leaf422InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf422LowerChecked :
    lowerCheck 24 leaf422Box leaf422Inputs = true := by
  rfl'

private theorem leaf422CoversExact : CoversExact 8
    leaf422Box leaf422Certificate leaf422InnerLog leaf422Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk52RoundedFacts chi59RoundedFacts
    innerPair51RoundedFacts leaf422RoundedFacts (by rfl)

private theorem leaf422FlatSound : Sound leaf422Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf422CertificateValid
    leaf422InnerLogValid leaf422CoversExact leaf422LowerChecked

private noncomputable def leaf423Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf423Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108967/67108864) }, vSqrt := { lower := (16383/16384), upper := (3817697735/3817596928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (107443707/67108864) }, upper := { exponent := 0, mantissa := (1691/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (7635294663/7635193856) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf423InnerLog : WideLogData :=
  innerPair158Data

set_option maxRecDepth 1000000 in
private theorem leaf423LocalValidity :
    LeafFacts leaf423Box leaf423Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf423Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (3817697735/3817596928) }) = true
      norm_num [leaf423Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf423CertificateValid :
    WideCertificateValid leaf423Box leaf423Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi60ValidityFacts
    leaf423LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf423CoverageChecked :
    coverageCheck (innerAD leaf423Box) leaf423InnerLog = true := by
  rfl'

private theorem leaf423InnerLogValid :
    leaf423InnerLog.Valid 8 (innerAD leaf423Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint48PositiveFacts.valid leaf423CoverageChecked

private noncomputable def leaf423InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf423InputLogOnePlusV_eq :
    leaf423InputLogOnePlusV = outerEnclosure 24
      (leaf423Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf423RoundedFacts : LeafRoundedFacts 8
    leaf423Certificate.logOnePlusV leaf423InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf423InputLogOnePlusV_eq }

private noncomputable def leaf423Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi60InputQChi innerPair158Input
    leaf423InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf423LowerChecked :
    lowerCheck 24 leaf423Box leaf423Inputs = true := by
  rfl'

private theorem leaf423CoversExact : CoversExact 8
    leaf423Box leaf423Certificate leaf423InnerLog leaf423Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi60RoundedFacts
    innerPair158RoundedFacts leaf423RoundedFacts (by rfl)

private theorem leaf423FlatSound : Sound leaf423Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf423CertificateValid
    leaf423InnerLogValid leaf423CoversExact leaf423LowerChecked

private noncomputable def leaf424Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf424Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108969/67108864) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871662592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (109278601/67108864) }, upper := { exponent := 0, mantissa := (215/128) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743518515/13743325184) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf424InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf424LocalValidity :
    LeafFacts leaf424Box leaf424Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf424Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871662592) }) = true
      norm_num [leaf424Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf424CertificateValid :
    WideCertificateValid leaf424Box leaf424Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi61ValidityFacts
    leaf424LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf424CoverageChecked :
    coverageCheck (innerAD leaf424Box) leaf424InnerLog = true := by
  rfl'

private theorem leaf424InnerLogValid :
    leaf424InnerLog.Valid 8 (innerAD leaf424Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf424CoverageChecked

private noncomputable def leaf424InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf424InputLogOnePlusV_eq :
    leaf424InputLogOnePlusV = outerEnclosure 24
      (leaf424Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf424RoundedFacts : LeafRoundedFacts 8
    leaf424Certificate.logOnePlusV leaf424InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf424InputLogOnePlusV_eq }

private noncomputable def leaf424Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi61InputQChi innerPair56Input
    leaf424InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf424LowerChecked :
    lowerCheck 24 leaf424Box leaf424Inputs = true := by
  rfl'

private theorem leaf424CoversExact : CoversExact 8
    leaf424Box leaf424Certificate leaf424InnerLog leaf424Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi61RoundedFacts
    innerPair56RoundedFacts leaf424RoundedFacts (by rfl)

private theorem leaf424FlatSound : Sound leaf424Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf424CertificateValid
    leaf424InnerLogValid leaf424CoversExact leaf424LowerChecked

private noncomputable def leaf425Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf425Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108969/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358325248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (108885409/67108864) }, upper := { exponent := 0, mantissa := (857/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717604863/68716650496) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf425InnerLog : WideLogData :=
  innerPair187Data

set_option maxRecDepth 1000000 in
private theorem leaf425LocalValidity :
    LeafFacts leaf425Box leaf425Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf425Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358325248) }) = true
      norm_num [leaf425Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf425CertificateValid :
    WideCertificateValid leaf425Box leaf425Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi60ValidityFacts
    leaf425LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf425CoverageChecked :
    coverageCheck (innerAD leaf425Box) leaf425InnerLog = true := by
  rfl'

private theorem leaf425InnerLogValid :
    leaf425InnerLog.Valid 8 (innerAD leaf425Box) :=
  wideLogDataValid_of_cachedCheck endpoint55PositiveFacts
    endpoint56PositiveFacts.valid leaf425CoverageChecked

private noncomputable def leaf425InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf425InputLogOnePlusV_eq :
    leaf425InputLogOnePlusV = outerEnclosure 24
      (leaf425Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf425RoundedFacts : LeafRoundedFacts 8
    leaf425Certificate.logOnePlusV leaf425InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf425InputLogOnePlusV_eq }

private noncomputable def leaf425Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi60InputQChi innerPair187Input
    leaf425InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf425LowerChecked :
    lowerCheck 24 leaf425Box leaf425Inputs = true := by
  rfl'

private theorem leaf425CoversExact : CoversExact 8
    leaf425Box leaf425Certificate leaf425InnerLog leaf425Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi60RoundedFacts
    innerPair187RoundedFacts leaf425RoundedFacts (by rfl)

private theorem leaf425FlatSound : Sound leaf425Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf425CertificateValid
    leaf425InnerLogValid leaf425CoversExact leaf425LowerChecked

private noncomputable def leaf426Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf426Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108971/67108864) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358263808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (110785835/67108864) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717543423/68716527616) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf426InnerLog : WideLogData :=
  innerPair160Data

set_option maxRecDepth 1000000 in
private theorem leaf426LocalValidity :
    LeafFacts leaf426Box leaf426Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf426Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358263808) }) = true
      norm_num [leaf426Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf426CertificateValid :
    WideCertificateValid leaf426Box leaf426Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi61ValidityFacts
    leaf426LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf426CoverageChecked :
    coverageCheck (innerAD leaf426Box) leaf426InnerLog = true := by
  rfl'

private theorem leaf426InnerLogValid :
    leaf426InnerLog.Valid 8 (innerAD leaf426Box) :=
  wideLogDataValid_of_cachedCheck endpoint45PositiveFacts
    endpoint20PositiveFacts.valid leaf426CoverageChecked

private noncomputable def leaf426InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf426InputLogOnePlusV_eq :
    leaf426InputLogOnePlusV = outerEnclosure 24
      (leaf426Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf426RoundedFacts : LeafRoundedFacts 8
    leaf426Certificate.logOnePlusV leaf426InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf426InputLogOnePlusV_eq }

private noncomputable def leaf426Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi61InputQChi innerPair160Input
    leaf426InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf426LowerChecked :
    lowerCheck 24 leaf426Box leaf426Inputs = true := by
  rfl'

private theorem leaf426CoversExact : CoversExact 8
    leaf426Box leaf426Certificate leaf426InnerLog leaf426Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi61RoundedFacts
    innerPair160RoundedFacts leaf426RoundedFacts (by rfl)

private theorem leaf426FlatSound : Sound leaf426Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf426CertificateValid
    leaf426InnerLogValid leaf426CoversExact leaf426LowerChecked

private noncomputable def leaf427Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf427Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217891/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716853248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (212823199/134217728) }, upper := { exponent := 0, mantissa := (3329/2048) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435346943/137433706496) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf427InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf427LocalValidity :
    LeafFacts leaf427Box leaf427Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf427Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716853248) }) = true
      norm_num [leaf427Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf427CertificateValid :
    WideCertificateValid leaf427Box leaf427Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi58ValidityFacts
    leaf427LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf427CoverageChecked :
    coverageCheck (innerAD leaf427Box) leaf427InnerLog = true := by
  rfl'

private theorem leaf427InnerLogValid :
    leaf427InnerLog.Valid 8 (innerAD leaf427Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf427CoverageChecked

private noncomputable def leaf427InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf427InputLogOnePlusV_eq :
    leaf427InputLogOnePlusV = outerEnclosure 24
      (leaf427Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf427RoundedFacts : LeafRoundedFacts 8
    leaf427Certificate.logOnePlusV leaf427InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf427InputLogOnePlusV_eq }

private noncomputable def leaf427Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi58InputQChi innerPair51Input
    leaf427InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf427LowerChecked :
    lowerCheck 24 leaf427Box leaf427Inputs = true := by
  rfl'

private theorem leaf427CoversExact : CoversExact 8
    leaf427Box leaf427Certificate leaf427InnerLog leaf427Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi58RoundedFacts
    innerPair51RoundedFacts leaf427RoundedFacts (by rfl)

private theorem leaf427FlatSound : Sound leaf427Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf427CertificateValid
    leaf427InnerLogValid leaf427CoversExact leaf427LowerChecked

private noncomputable def leaf428Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf428Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217893/134217728) }, vSqrt := { lower := (16383/16384), upper := (13743698739/13743362048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (214133837/134217728) }, upper := { exponent := 0, mantissa := (1675/1024) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (27487060787/27486724096) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf428InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf428LocalValidity :
    LeafFacts leaf428Box leaf428Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf428Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (13743698739/13743362048) }) = true
      norm_num [leaf428Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf428CertificateValid :
    WideCertificateValid leaf428Box leaf428Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi58ValidityFacts
    leaf428LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf428CoverageChecked :
    coverageCheck (innerAD leaf428Box) leaf428InnerLog = true := by
  rfl'

private theorem leaf428InnerLogValid :
    leaf428InnerLog.Valid 8 (innerAD leaf428Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf428CoverageChecked

private noncomputable def leaf428InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf428InputLogOnePlusV_eq :
    leaf428InputLogOnePlusV = outerEnclosure 24
      (leaf428Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf428RoundedFacts : LeafRoundedFacts 8
    leaf428Certificate.logOnePlusV leaf428InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf428InputLogOnePlusV_eq }

private noncomputable def leaf428Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi58InputQChi innerPair51Input
    leaf428InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf428LowerChecked :
    lowerCheck 24 leaf428Box leaf428Inputs = true := by
  rfl'

private theorem leaf428CoversExact : CoversExact 8
    leaf428Box leaf428Certificate leaf428InnerLog leaf428Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi58RoundedFacts
    innerPair51RoundedFacts leaf428RoundedFacts (by rfl)

private theorem leaf428FlatSound : Sound leaf428Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf428CertificateValid
    leaf428InnerLogValid leaf428CoversExact leaf428LowerChecked

private noncomputable def leaf429Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf429Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217893/134217728) }, vSqrt := { lower := (16383/16384), upper := (13743698739/13743345664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (216755117/134217728) }, upper := { exponent := 0, mantissa := (1695/1024) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (27487044403/27486691328) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf429InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf429LocalValidity :
    LeafFacts leaf429Box leaf429Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf429Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (13743698739/13743345664) }) = true
      norm_num [leaf429Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf429CertificateValid :
    WideCertificateValid leaf429Box leaf429Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi59ValidityFacts
    leaf429LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf429CoverageChecked :
    coverageCheck (innerAD leaf429Box) leaf429InnerLog = true := by
  rfl'

private theorem leaf429InnerLogValid :
    leaf429InnerLog.Valid 8 (innerAD leaf429Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf429CoverageChecked

private noncomputable def leaf429InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf429InputLogOnePlusV_eq :
    leaf429InputLogOnePlusV = outerEnclosure 24
      (leaf429Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf429RoundedFacts : LeafRoundedFacts 8
    leaf429Certificate.logOnePlusV leaf429InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf429InputLogOnePlusV_eq }

private noncomputable def leaf429Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi59InputQChi innerPair51Input
    leaf429InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf429LowerChecked :
    lowerCheck 24 leaf429Box leaf429Inputs = true := by
  rfl'

private theorem leaf429CoversExact : CoversExact 8
    leaf429Box leaf429Certificate leaf429InnerLog leaf429Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi59RoundedFacts
    innerPair51RoundedFacts leaf429RoundedFacts (by rfl)

private theorem leaf429FlatSound : Sound leaf429Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf429CertificateValid
    leaf429InnerLogValid leaf429CoversExact leaf429LowerChecked

private noncomputable def leaf430Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf430Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905561088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (218131287/134217728) }, upper := { exponent := 0, mantissa := (853/512) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811725653/45811122176) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf430InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf430LocalValidity :
    LeafFacts leaf430Box leaf430Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf430Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905561088) }) = true
      norm_num [leaf430Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf430CertificateValid :
    WideCertificateValid leaf430Box leaf430Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi59ValidityFacts
    leaf430LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf430CoverageChecked :
    coverageCheck (innerAD leaf430Box) leaf430InnerLog = true := by
  rfl'

private theorem leaf430InnerLogValid :
    leaf430InnerLog.Valid 8 (innerAD leaf430Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf430CoverageChecked

private noncomputable def leaf430InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf430InputLogOnePlusV_eq :
    leaf430InputLogOnePlusV = outerEnclosure 24
      (leaf430Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf430RoundedFacts : LeafRoundedFacts 8
    leaf430Certificate.logOnePlusV leaf430InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf430InputLogOnePlusV_eq }

private noncomputable def leaf430Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi59InputQChi innerPair56Input
    leaf430InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf430LowerChecked :
    lowerCheck 24 leaf430Box leaf430Inputs = true := by
  rfl'

private theorem leaf430CoversExact : CoversExact 8
    leaf430Box leaf430Certificate leaf430InnerLog leaf430Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi59RoundedFacts
    innerPair56RoundedFacts leaf430RoundedFacts (by rfl)

private theorem leaf430FlatSound : Sound leaf430Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf430CertificateValid
    leaf430InnerLogValid leaf430CoversExact leaf430LowerChecked

private noncomputable def leaf431Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf431Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716767232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (215444475/134217728) }, upper := { exponent := 0, mantissa := (3371/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435260927/137433534464) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf431InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf431LocalValidity :
    LeafFacts leaf431Box leaf431Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf431Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716767232) }) = true
      norm_num [leaf431Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf431CertificateValid :
    WideCertificateValid leaf431Box leaf431Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi58ValidityFacts
    leaf431LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf431CoverageChecked :
    coverageCheck (innerAD leaf431Box) leaf431InnerLog = true := by
  rfl'

private theorem leaf431InnerLogValid :
    leaf431InnerLog.Valid 8 (innerAD leaf431Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf431CoverageChecked

private noncomputable def leaf431InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf431InputLogOnePlusV_eq :
    leaf431InputLogOnePlusV = outerEnclosure 24
      (leaf431Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf431RoundedFacts : LeafRoundedFacts 8
    leaf431Certificate.logOnePlusV leaf431InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf431InputLogOnePlusV_eq }

private noncomputable def leaf431Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi58InputQChi innerPair51Input
    leaf431InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf431LowerChecked :
    lowerCheck 24 leaf431Box leaf431Inputs = true := by
  rfl'

private theorem leaf431CoversExact : CoversExact 8
    leaf431Box leaf431Certificate leaf431InnerLog leaf431Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi58RoundedFacts
    innerPair51RoundedFacts leaf431RoundedFacts (by rfl)

private theorem leaf431FlatSound : Sound leaf431Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf431CertificateValid
    leaf431InnerLogValid leaf431CoversExact leaf431LowerChecked

private noncomputable def leaf432Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf432Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716724224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (216755113/134217728) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435217919/137433448448) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf432InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf432LocalValidity :
    LeafFacts leaf432Box leaf432Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf432Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716724224) }) = true
      norm_num [leaf432Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf432CertificateValid :
    WideCertificateValid leaf432Box leaf432Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi58ValidityFacts
    leaf432LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf432CoverageChecked :
    coverageCheck (innerAD leaf432Box) leaf432InnerLog = true := by
  rfl'

private theorem leaf432InnerLogValid :
    leaf432InnerLog.Valid 8 (innerAD leaf432Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf432CoverageChecked

private noncomputable def leaf432InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf432InputLogOnePlusV_eq :
    leaf432InputLogOnePlusV = outerEnclosure 24
      (leaf432Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf432RoundedFacts : LeafRoundedFacts 8
    leaf432Certificate.logOnePlusV leaf432InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf432InputLogOnePlusV_eq }

private noncomputable def leaf432Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi58InputQChi innerPair51Input
    leaf432InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf432LowerChecked :
    lowerCheck 24 leaf432Box leaf432Inputs = true := by
  rfl'

private theorem leaf432CoversExact : CoversExact 8
    leaf432Box leaf432Certificate leaf432InnerLog leaf432Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi58RoundedFacts
    innerPair51RoundedFacts leaf432RoundedFacts (by rfl)

private theorem leaf432FlatSound : Sound leaf432Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf432CertificateValid
    leaf432InnerLogValid leaf432CoversExact leaf432LowerChecked

private noncomputable def leaf433Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf433Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716638208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (219507457/134217728) }, upper := { exponent := 0, mantissa := (1717/1024) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435131903/137433276416) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf433InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf433LocalValidity :
    LeafFacts leaf433Box leaf433Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf433Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716638208) }) = true
      norm_num [leaf433Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf433CertificateValid :
    WideCertificateValid leaf433Box leaf433Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi59ValidityFacts
    leaf433LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf433CoverageChecked :
    coverageCheck (innerAD leaf433Box) leaf433InnerLog = true := by
  rfl'

private theorem leaf433InnerLogValid :
    leaf433InnerLog.Valid 8 (innerAD leaf433Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf433CoverageChecked

private noncomputable def leaf433InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf433InputLogOnePlusV_eq :
    leaf433InputLogOnePlusV = outerEnclosure 24
      (leaf433Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf433RoundedFacts : LeafRoundedFacts 8
    leaf433Certificate.logOnePlusV leaf433InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf433InputLogOnePlusV_eq }

private noncomputable def leaf433Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi59InputQChi innerPair56Input
    leaf433InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf433LowerChecked :
    lowerCheck 24 leaf433Box leaf433Inputs = true := by
  rfl'

private theorem leaf433CoversExact : CoversExact 8
    leaf433Box leaf433Certificate leaf433InnerLog leaf433Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi59RoundedFacts
    innerPair56RoundedFacts leaf433RoundedFacts (by rfl)

private theorem leaf433FlatSound : Sound leaf433Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf433CertificateValid
    leaf433InnerLogValid leaf433CoversExact leaf433LowerChecked

private noncomputable def leaf434Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf434Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716593152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (220883627/134217728) }, upper := { exponent := 0, mantissa := (27/16) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137435086847/137433186304) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf434InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf434LocalValidity :
    LeafFacts leaf434Box leaf434Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf434Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716593152) }) = true
      norm_num [leaf434Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf434CertificateValid :
    WideCertificateValid leaf434Box leaf434Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi59ValidityFacts
    leaf434LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf434CoverageChecked :
    coverageCheck (innerAD leaf434Box) leaf434InnerLog = true := by
  rfl'

private theorem leaf434InnerLogValid :
    leaf434InnerLog.Valid 8 (innerAD leaf434Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf434CoverageChecked

private noncomputable def leaf434InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf434InputLogOnePlusV_eq :
    leaf434InputLogOnePlusV = outerEnclosure 24
      (leaf434Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf434RoundedFacts : LeafRoundedFacts 8
    leaf434Certificate.logOnePlusV leaf434InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf434InputLogOnePlusV_eq }

private noncomputable def leaf434Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi59InputQChi innerPair56Input
    leaf434InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf434LowerChecked :
    lowerCheck 24 leaf434Box leaf434Inputs = true := by
  rfl'

private theorem leaf434CoversExact : CoversExact 8
    leaf434Box leaf434Certificate leaf434InnerLog leaf434Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi59RoundedFacts
    innerPair56RoundedFacts leaf434RoundedFacts (by rfl)

private theorem leaf434FlatSound : Sound leaf434Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf434CertificateValid
    leaf434InnerLogValid leaf434CoversExact leaf434LowerChecked

private noncomputable def leaf435Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf435Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217895/134217728) }, vSqrt := { lower := (16383/16384), upper := (22906164565/22905534464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (220687035/134217728) }, upper := { exponent := 0, mantissa := (3451/2048) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (45811699029/45811068928) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf435InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf435LocalValidity :
    LeafFacts leaf435Box leaf435Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf435Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (22906164565/22905534464) }) = true
      norm_num [leaf435Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf435CertificateValid :
    WideCertificateValid leaf435Box leaf435Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi60ValidityFacts
    leaf435LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf435CoverageChecked :
    coverageCheck (innerAD leaf435Box) leaf435InnerLog = true := by
  rfl'

private theorem leaf435InnerLogValid :
    leaf435InnerLog.Valid 8 (innerAD leaf435Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf435CoverageChecked

private noncomputable def leaf435InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf435InputLogOnePlusV_eq :
    leaf435InputLogOnePlusV = outerEnclosure 24
      (leaf435Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf435RoundedFacts : LeafRoundedFacts 8
    leaf435Certificate.logOnePlusV leaf435InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf435InputLogOnePlusV_eq }

private noncomputable def leaf435Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi60InputQChi innerPair56Input
    leaf435InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf435LowerChecked :
    lowerCheck 24 leaf435Box leaf435Inputs = true := by
  rfl'

private theorem leaf435CoversExact : CoversExact 8
    leaf435Box leaf435Certificate leaf435InnerLog leaf435Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi60RoundedFacts
    innerPair56RoundedFacts leaf435RoundedFacts (by rfl)

private theorem leaf435FlatSound : Sound leaf435Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf435CertificateValid
    leaf435InnerLogValid leaf435CoversExact leaf435LowerChecked

private noncomputable def leaf436Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf436Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716556288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (222128737/134217728) }, upper := { exponent := 0, mantissa := (1737/1024) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435049983/137433112576) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf436InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf436LocalValidity :
    LeafFacts leaf436Box leaf436Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf436Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716556288) }) = true
      norm_num [leaf436Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf436CertificateValid :
    WideCertificateValid leaf436Box leaf436Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi60ValidityFacts
    leaf436LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf436CoverageChecked :
    coverageCheck (innerAD leaf436Box) leaf436InnerLog = true := by
  rfl'

private theorem leaf436InnerLogValid :
    leaf436InnerLog.Valid 8 (innerAD leaf436Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf436CoverageChecked

private noncomputable def leaf436InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf436InputLogOnePlusV_eq :
    leaf436InputLogOnePlusV = outerEnclosure 24
      (leaf436Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf436RoundedFacts : LeafRoundedFacts 8
    leaf436Certificate.logOnePlusV leaf436InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf436InputLogOnePlusV_eq }

private noncomputable def leaf436Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi60InputQChi innerPair57Input
    leaf436InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf436LowerChecked :
    lowerCheck 24 leaf436Box leaf436Inputs = true := by
  rfl'

private theorem leaf436CoversExact : CoversExact 8
    leaf436Box leaf436Certificate leaf436InnerLog leaf436Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi60RoundedFacts
    innerPair57RoundedFacts leaf436RoundedFacts (by rfl)

private theorem leaf436FlatSound : Sound leaf436Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf436CertificateValid
    leaf436InnerLogValid leaf436CoversExact leaf436LowerChecked

private noncomputable def leaf437Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (61/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf437Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217897/134217728) }, vSqrt := { lower := (16383/16384), upper := (4042264335/4042145792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (224618953/134217728) }, upper := { exponent := 0, mantissa := (439/256) } }, logOuter := sk49LogOuterCertificate, logK := sk49LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8084410127/8084291584) } }, logDArg := sk49LogDArgCertificate }

private noncomputable def leaf437InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf437LocalValidity :
    LeafFacts leaf437Box leaf437Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf437Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4042264335/4042145792) }) = true
      norm_num [leaf437Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf437CertificateValid :
    WideCertificateValid leaf437Box leaf437Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk49ValidityFacts chi61ValidityFacts
    leaf437LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf437CoverageChecked :
    coverageCheck (innerAD leaf437Box) leaf437InnerLog = true := by
  rfl'

private theorem leaf437InnerLogValid :
    leaf437InnerLog.Valid 8 (innerAD leaf437Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf437CoverageChecked

private noncomputable def leaf437InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf437InputLogOnePlusV_eq :
    leaf437InputLogOnePlusV = outerEnclosure 24
      (leaf437Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf437RoundedFacts : LeafRoundedFacts 8
    leaf437Certificate.logOnePlusV leaf437InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf437InputLogOnePlusV_eq }

private noncomputable def leaf437Inputs : Inputs :=
  inputsOfCaches globalInput sk49RoundedInputs
    chi61InputQChi innerPair57Input
    leaf437InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf437LowerChecked :
    lowerCheck 24 leaf437Box leaf437Inputs = true := by
  rfl'

private theorem leaf437CoversExact : CoversExact 8
    leaf437Box leaf437Certificate leaf437InnerLog leaf437Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk49RoundedFacts chi61RoundedFacts
    innerPair57RoundedFacts leaf437RoundedFacts (by rfl)

private theorem leaf437FlatSound : Sound leaf437Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf437CertificateValid
    leaf437InnerLogValid leaf437CoversExact leaf437LowerChecked

private noncomputable def leaf438Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/32), kHi := (31/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf438Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716429312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (226126187/134217728) }, upper := { exponent := 0, mantissa := (221/128) } }, logOuter := sk50LogOuterCertificate, logK := sk50LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137434923007/137432858624) } }, logDArg := sk50LogDArgCertificate }

private noncomputable def leaf438InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf438LocalValidity :
    LeafFacts leaf438Box leaf438Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf438Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716429312) }) = true
      norm_num [leaf438Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf438CertificateValid :
    WideCertificateValid leaf438Box leaf438Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk50ValidityFacts chi61ValidityFacts
    leaf438LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf438CoverageChecked :
    coverageCheck (innerAD leaf438Box) leaf438InnerLog = true := by
  rfl'

private theorem leaf438InnerLogValid :
    leaf438InnerLog.Valid 8 (innerAD leaf438Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf438CoverageChecked

private noncomputable def leaf438InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf438InputLogOnePlusV_eq :
    leaf438InputLogOnePlusV = outerEnclosure 24
      (leaf438Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf438RoundedFacts : LeafRoundedFacts 8
    leaf438Certificate.logOnePlusV leaf438InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf438InputLogOnePlusV_eq }

private noncomputable def leaf438Inputs : Inputs :=
  inputsOfCaches globalInput sk50RoundedInputs
    chi61InputQChi innerPair57Input
    leaf438InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf438LowerChecked :
    lowerCheck 24 leaf438Box leaf438Inputs = true := by
  rfl'

private theorem leaf438CoversExact : CoversExact 8
    leaf438Box leaf438Certificate leaf438InnerLog leaf438Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk50RoundedFacts chi61RoundedFacts
    innerPair57RoundedFacts leaf438RoundedFacts (by rfl)

private theorem leaf438FlatSound : Sound leaf438Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf438CertificateValid
    leaf438InnerLogValid leaf438CoversExact leaf438LowerChecked

private noncomputable def leaf439Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf439Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217899/134217728) }, vSqrt := { lower := (16383/16384), upper := (68718493695/68716509184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (223570439/134217728) }, upper := { exponent := 0, mantissa := (3497/2048) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (137435002879/137433018368) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf439InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf439LocalValidity :
    LeafFacts leaf439Box leaf439Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf439Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (68718493695/68716509184) }) = true
      norm_num [leaf439Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf439CertificateValid :
    WideCertificateValid leaf439Box leaf439Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi60ValidityFacts
    leaf439LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf439CoverageChecked :
    coverageCheck (innerAD leaf439Box) leaf439InnerLog = true := by
  rfl'

private theorem leaf439InnerLogValid :
    leaf439InnerLog.Valid 8 (innerAD leaf439Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf439CoverageChecked

private noncomputable def leaf439InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf439InputLogOnePlusV_eq :
    leaf439InputLogOnePlusV = outerEnclosure 24
      (leaf439Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf439RoundedFacts : LeafRoundedFacts 8
    leaf439Certificate.logOnePlusV leaf439InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf439InputLogOnePlusV_eq }

private noncomputable def leaf439Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi60InputQChi innerPair57Input
    leaf439InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf439LowerChecked :
    lowerCheck 24 leaf439Box leaf439Inputs = true := by
  rfl'

private theorem leaf439CoversExact : CoversExact 8
    leaf439Box leaf439Certificate leaf439InnerLog leaf439Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi60RoundedFacts
    innerPair57RoundedFacts leaf439RoundedFacts (by rfl)

private theorem leaf439FlatSound : Sound leaf439Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf439CertificateValid
    leaf439InnerLogValid leaf439CoversExact leaf439LowerChecked

private noncomputable def leaf440Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf440Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581097472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (225012141/134217728) }, upper := { exponent := 0, mantissa := (55/32) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162330385/9162194944) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf440InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf440LocalValidity :
    LeafFacts leaf440Box leaf440Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf440Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581097472) }) = true
      norm_num [leaf440Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf440CertificateValid :
    WideCertificateValid leaf440Box leaf440Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi60ValidityFacts
    leaf440LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf440CoverageChecked :
    coverageCheck (innerAD leaf440Box) leaf440InnerLog = true := by
  rfl'

private theorem leaf440InnerLogValid :
    leaf440InnerLog.Valid 8 (innerAD leaf440Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf440CoverageChecked

private noncomputable def leaf440InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf440InputLogOnePlusV_eq :
    leaf440InputLogOnePlusV = outerEnclosure 24
      (leaf440Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf440RoundedFacts : LeafRoundedFacts 8
    leaf440Certificate.logOnePlusV leaf440InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf440InputLogOnePlusV_eq }

private noncomputable def leaf440Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi60InputQChi innerPair57Input
    leaf440InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf440LowerChecked :
    lowerCheck 24 leaf440Box leaf440Inputs = true := by
  rfl'

private theorem leaf440CoversExact : CoversExact 8
    leaf440Box leaf440Certificate leaf440InnerLog leaf440Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi60RoundedFacts
    innerPair57RoundedFacts leaf440RoundedFacts (by rfl)

private theorem leaf440FlatSound : Sound leaf440Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf440CertificateValid
    leaf440InnerLogValid leaf440CoversExact leaf440LowerChecked

private noncomputable def leaf441Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (63/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf441Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217901/134217728) }, vSqrt := { lower := (16383/16384), upper := (13743698739/13743276032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (227633421/134217728) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk47LogOuterCertificate, logK := sk47LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (27486974771/27486552064) } }, logDArg := sk47LogDArgCertificate }

private noncomputable def leaf441InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf441LocalValidity :
    LeafFacts leaf441Box leaf441Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf441Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (13743698739/13743276032) }) = true
      norm_num [leaf441Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf441CertificateValid :
    WideCertificateValid leaf441Box leaf441Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk47ValidityFacts chi61ValidityFacts
    leaf441LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf441CoverageChecked :
    coverageCheck (innerAD leaf441Box) leaf441InnerLog = true := by
  rfl'

private theorem leaf441InnerLogValid :
    leaf441InnerLog.Valid 8 (innerAD leaf441Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf441CoverageChecked

private noncomputable def leaf441InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf441InputLogOnePlusV_eq :
    leaf441InputLogOnePlusV = outerEnclosure 24
      (leaf441Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf441RoundedFacts : LeafRoundedFacts 8
    leaf441Certificate.logOnePlusV leaf441InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf441InputLogOnePlusV_eq }

private noncomputable def leaf441Inputs : Inputs :=
  inputsOfCaches globalInput sk47RoundedInputs
    chi61InputQChi innerPair64Input
    leaf441InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf441LowerChecked :
    lowerCheck 24 leaf441Box leaf441Inputs = true := by
  rfl'

private theorem leaf441CoversExact : CoversExact 8
    leaf441Box leaf441Certificate leaf441InnerLog leaf441Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk47RoundedFacts chi61RoundedFacts
    innerPair64RoundedFacts leaf441RoundedFacts (by rfl)

private theorem leaf441FlatSound : Sound leaf441Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf441CertificateValid
    leaf441InnerLogValid leaf441CoversExact leaf441LowerChecked

private noncomputable def leaf442Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/32), kHi := (2), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf442Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716331008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (229140655/134217728) }, upper := { exponent := 0, mantissa := (7/4) } }, logOuter := sk48LogOuterCertificate, logK := sk48LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434824703/137432662016) } }, logDArg := sk48LogDArgCertificate }

private noncomputable def leaf442InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf442LocalValidity :
    LeafFacts leaf442Box leaf442Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf442Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716331008) }) = true
      norm_num [leaf442Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf442CertificateValid :
    WideCertificateValid leaf442Box leaf442Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk48ValidityFacts chi61ValidityFacts
    leaf442LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf442CoverageChecked :
    coverageCheck (innerAD leaf442Box) leaf442InnerLog = true := by
  rfl'

private theorem leaf442InnerLogValid :
    leaf442InnerLog.Valid 8 (innerAD leaf442Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf442CoverageChecked

private noncomputable def leaf442InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf442InputLogOnePlusV_eq :
    leaf442InputLogOnePlusV = outerEnclosure 24
      (leaf442Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf442RoundedFacts : LeafRoundedFacts 8
    leaf442Certificate.logOnePlusV leaf442InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf442InputLogOnePlusV_eq }

private noncomputable def leaf442Inputs : Inputs :=
  inputsOfCaches globalInput sk48RoundedInputs
    chi61InputQChi innerPair64Input
    leaf442InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf442LowerChecked :
    lowerCheck 24 leaf442Box leaf442Inputs = true := by
  rfl'

private theorem leaf442CoversExact : CoversExact 8
    leaf442Box leaf442Certificate leaf442InnerLog leaf442Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk48RoundedFacts chi61RoundedFacts
    innerPair64RoundedFacts leaf442RoundedFacts (by rfl)

private theorem leaf442FlatSound : Sound leaf442Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf442CertificateValid
    leaf442InnerLogValid leaf442CoversExact leaf442LowerChecked

private noncomputable def component10Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node0_sound : Sound component10Node0Box :=
  sound_of_literal_split component10Node0Box leaf387Box leaf388Box
    .k (57/32) (by rfl) (by rfl)
    leaf387FlatSound leaf388FlatSound

private noncomputable def component10Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node1_sound : Sound component10Node1Box :=
  sound_of_literal_split component10Node1Box leaf389Box leaf390Box
    .k (57/32) (by rfl) (by rfl)
    leaf389FlatSound leaf390FlatSound

private noncomputable def component10Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node2_sound : Sound component10Node2Box :=
  sound_of_literal_split component10Node2Box component10Node0Box component10Node1Box
    .chi (17/64) (by rfl) (by rfl)
    component10Node0_sound component10Node1_sound

private noncomputable def component10Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node3_sound : Sound component10Node3Box :=
  sound_of_literal_split component10Node3Box leaf391Box leaf392Box
    .k (59/32) (by rfl) (by rfl)
    leaf391FlatSound leaf392FlatSound

private noncomputable def component10Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node4_sound : Sound component10Node4Box :=
  sound_of_literal_split component10Node4Box leaf393Box leaf394Box
    .k (59/32) (by rfl) (by rfl)
    leaf393FlatSound leaf394FlatSound

private noncomputable def component10Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node5_sound : Sound component10Node5Box :=
  sound_of_literal_split component10Node5Box component10Node3Box component10Node4Box
    .chi (17/64) (by rfl) (by rfl)
    component10Node3_sound component10Node4_sound

private noncomputable def component10Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node6_sound : Sound component10Node6Box :=
  sound_of_literal_split component10Node6Box component10Node2Box component10Node5Box
    .k (29/16) (by rfl) (by rfl)
    component10Node2_sound component10Node5_sound

private noncomputable def component10Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node7_sound : Sound component10Node7Box :=
  sound_of_literal_split component10Node7Box leaf395Box leaf396Box
    .chi (19/64) (by rfl) (by rfl)
    leaf395FlatSound leaf396FlatSound

private noncomputable def component10Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node8_sound : Sound component10Node8Box :=
  sound_of_literal_split component10Node8Box leaf397Box leaf398Box
    .k (59/32) (by rfl) (by rfl)
    leaf397FlatSound leaf398FlatSound

private noncomputable def component10Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node9_sound : Sound component10Node9Box :=
  sound_of_literal_split component10Node9Box leaf399Box leaf400Box
    .k (59/32) (by rfl) (by rfl)
    leaf399FlatSound leaf400FlatSound

private noncomputable def component10Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node10_sound : Sound component10Node10Box :=
  sound_of_literal_split component10Node10Box component10Node8Box component10Node9Box
    .chi (19/64) (by rfl) (by rfl)
    component10Node8_sound component10Node9_sound

private noncomputable def component10Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node11_sound : Sound component10Node11Box :=
  sound_of_literal_split component10Node11Box component10Node7Box component10Node10Box
    .k (29/16) (by rfl) (by rfl)
    component10Node7_sound component10Node10_sound

private noncomputable def component10Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node12_sound : Sound component10Node12Box :=
  sound_of_literal_split component10Node12Box component10Node6Box component10Node11Box
    .chi (9/32) (by rfl) (by rfl)
    component10Node6_sound component10Node11_sound

private noncomputable def component10Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node13_sound : Sound component10Node13Box :=
  sound_of_literal_split component10Node13Box leaf401Box leaf402Box
    .k (61/32) (by rfl) (by rfl)
    leaf401FlatSound leaf402FlatSound

private noncomputable def component10Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node14_sound : Sound component10Node14Box :=
  sound_of_literal_split component10Node14Box leaf403Box leaf404Box
    .k (61/32) (by rfl) (by rfl)
    leaf403FlatSound leaf404FlatSound

private noncomputable def component10Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node15_sound : Sound component10Node15Box :=
  sound_of_literal_split component10Node15Box component10Node13Box component10Node14Box
    .chi (17/64) (by rfl) (by rfl)
    component10Node13_sound component10Node14_sound

private noncomputable def component10Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node16_sound : Sound component10Node16Box :=
  sound_of_literal_split component10Node16Box leaf405Box leaf406Box
    .k (63/32) (by rfl) (by rfl)
    leaf405FlatSound leaf406FlatSound

private noncomputable def component10Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node17_sound : Sound component10Node17Box :=
  sound_of_literal_split component10Node17Box leaf407Box leaf408Box
    .k (63/32) (by rfl) (by rfl)
    leaf407FlatSound leaf408FlatSound

private noncomputable def component10Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node18_sound : Sound component10Node18Box :=
  sound_of_literal_split component10Node18Box component10Node16Box component10Node17Box
    .chi (17/64) (by rfl) (by rfl)
    component10Node16_sound component10Node17_sound

private noncomputable def component10Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node19_sound : Sound component10Node19Box :=
  sound_of_literal_split component10Node19Box component10Node15Box component10Node18Box
    .k (31/16) (by rfl) (by rfl)
    component10Node15_sound component10Node18_sound

private noncomputable def component10Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node20_sound : Sound component10Node20Box :=
  sound_of_literal_split component10Node20Box leaf409Box leaf410Box
    .k (61/32) (by rfl) (by rfl)
    leaf409FlatSound leaf410FlatSound

private noncomputable def component10Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node21_sound : Sound component10Node21Box :=
  sound_of_literal_split component10Node21Box leaf411Box leaf412Box
    .k (61/32) (by rfl) (by rfl)
    leaf411FlatSound leaf412FlatSound

private noncomputable def component10Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node22_sound : Sound component10Node22Box :=
  sound_of_literal_split component10Node22Box component10Node20Box component10Node21Box
    .chi (19/64) (by rfl) (by rfl)
    component10Node20_sound component10Node21_sound

private noncomputable def component10Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (9/32), chiHi := (19/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node23_sound : Sound component10Node23Box :=
  sound_of_literal_split component10Node23Box leaf413Box leaf414Box
    .k (63/32) (by rfl) (by rfl)
    leaf413FlatSound leaf414FlatSound

private noncomputable def component10Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (19/64), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node24_sound : Sound component10Node24Box :=
  sound_of_literal_split component10Node24Box leaf415Box leaf416Box
    .k (63/32) (by rfl) (by rfl)
    leaf415FlatSound leaf416FlatSound

private noncomputable def component10Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node25_sound : Sound component10Node25Box :=
  sound_of_literal_split component10Node25Box component10Node23Box component10Node24Box
    .chi (19/64) (by rfl) (by rfl)
    component10Node23_sound component10Node24_sound

private noncomputable def component10Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node26_sound : Sound component10Node26Box :=
  sound_of_literal_split component10Node26Box component10Node22Box component10Node25Box
    .k (31/16) (by rfl) (by rfl)
    component10Node22_sound component10Node25_sound

private noncomputable def component10Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node27_sound : Sound component10Node27Box :=
  sound_of_literal_split component10Node27Box component10Node19Box component10Node26Box
    .chi (9/32) (by rfl) (by rfl)
    component10Node19_sound component10Node26_sound

private noncomputable def component10Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component10Node28_sound : Sound component10Node28Box :=
  sound_of_literal_split component10Node28Box component10Node12Box component10Node27Box
    .k (15/8) (by rfl) (by rfl)
    component10Node12_sound component10Node27_sound

private noncomputable def component10Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node29_sound : Sound component10Node29Box :=
  sound_of_literal_split component10Node29Box leaf417Box leaf418Box
    .chi (21/64) (by rfl) (by rfl)
    leaf417FlatSound leaf418FlatSound

private noncomputable def component10Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node30_sound : Sound component10Node30Box :=
  sound_of_literal_split component10Node30Box leaf419Box leaf420Box
    .k (59/32) (by rfl) (by rfl)
    leaf419FlatSound leaf420FlatSound

private noncomputable def component10Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node31_sound : Sound component10Node31Box :=
  sound_of_literal_split component10Node31Box leaf421Box leaf422Box
    .k (59/32) (by rfl) (by rfl)
    leaf421FlatSound leaf422FlatSound

private noncomputable def component10Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node32_sound : Sound component10Node32Box :=
  sound_of_literal_split component10Node32Box component10Node30Box component10Node31Box
    .chi (21/64) (by rfl) (by rfl)
    component10Node30_sound component10Node31_sound

private noncomputable def component10Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node33_sound : Sound component10Node33Box :=
  sound_of_literal_split component10Node33Box component10Node29Box component10Node32Box
    .k (29/16) (by rfl) (by rfl)
    component10Node29_sound component10Node32_sound

private noncomputable def component10Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node34_sound : Sound component10Node34Box :=
  sound_of_literal_split component10Node34Box leaf423Box leaf424Box
    .chi (23/64) (by rfl) (by rfl)
    leaf423FlatSound leaf424FlatSound

private noncomputable def component10Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node35_sound : Sound component10Node35Box :=
  sound_of_literal_split component10Node35Box leaf425Box leaf426Box
    .chi (23/64) (by rfl) (by rfl)
    leaf425FlatSound leaf426FlatSound

private noncomputable def component10Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node36_sound : Sound component10Node36Box :=
  sound_of_literal_split component10Node36Box component10Node34Box component10Node35Box
    .k (29/16) (by rfl) (by rfl)
    component10Node34_sound component10Node35_sound

private noncomputable def component10Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node37_sound : Sound component10Node37Box :=
  sound_of_literal_split component10Node37Box component10Node33Box component10Node36Box
    .chi (11/32) (by rfl) (by rfl)
    component10Node33_sound component10Node36_sound

private noncomputable def component10Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node38_sound : Sound component10Node38Box :=
  sound_of_literal_split component10Node38Box leaf427Box leaf428Box
    .k (61/32) (by rfl) (by rfl)
    leaf427FlatSound leaf428FlatSound

private noncomputable def component10Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node39_sound : Sound component10Node39Box :=
  sound_of_literal_split component10Node39Box leaf429Box leaf430Box
    .k (61/32) (by rfl) (by rfl)
    leaf429FlatSound leaf430FlatSound

private noncomputable def component10Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node40_sound : Sound component10Node40Box :=
  sound_of_literal_split component10Node40Box component10Node38Box component10Node39Box
    .chi (21/64) (by rfl) (by rfl)
    component10Node38_sound component10Node39_sound

private noncomputable def component10Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node41_sound : Sound component10Node41Box :=
  sound_of_literal_split component10Node41Box leaf431Box leaf432Box
    .k (63/32) (by rfl) (by rfl)
    leaf431FlatSound leaf432FlatSound

private noncomputable def component10Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node42_sound : Sound component10Node42Box :=
  sound_of_literal_split component10Node42Box leaf433Box leaf434Box
    .k (63/32) (by rfl) (by rfl)
    leaf433FlatSound leaf434FlatSound

private noncomputable def component10Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node43_sound : Sound component10Node43Box :=
  sound_of_literal_split component10Node43Box component10Node41Box component10Node42Box
    .chi (21/64) (by rfl) (by rfl)
    component10Node41_sound component10Node42_sound

private noncomputable def component10Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component10Node44_sound : Sound component10Node44Box :=
  sound_of_literal_split component10Node44Box component10Node40Box component10Node43Box
    .k (31/16) (by rfl) (by rfl)
    component10Node40_sound component10Node43_sound

private noncomputable def component10Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node45_sound : Sound component10Node45Box :=
  sound_of_literal_split component10Node45Box leaf435Box leaf436Box
    .k (61/32) (by rfl) (by rfl)
    leaf435FlatSound leaf436FlatSound

private noncomputable def component10Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node46_sound : Sound component10Node46Box :=
  sound_of_literal_split component10Node46Box leaf437Box leaf438Box
    .k (61/32) (by rfl) (by rfl)
    leaf437FlatSound leaf438FlatSound

private noncomputable def component10Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node47_sound : Sound component10Node47Box :=
  sound_of_literal_split component10Node47Box component10Node45Box component10Node46Box
    .chi (23/64) (by rfl) (by rfl)
    component10Node45_sound component10Node46_sound

private noncomputable def component10Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component10Node48_sound : Sound component10Node48Box :=
  sound_of_literal_split component10Node48Box leaf439Box leaf440Box
    .k (63/32) (by rfl) (by rfl)
    leaf439FlatSound leaf440FlatSound

private noncomputable def component10Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node49_sound : Sound component10Node49Box :=
  sound_of_literal_split component10Node49Box leaf441Box leaf442Box
    .k (63/32) (by rfl) (by rfl)
    leaf441FlatSound leaf442FlatSound

private noncomputable def component10Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node50_sound : Sound component10Node50Box :=
  sound_of_literal_split component10Node50Box component10Node48Box component10Node49Box
    .chi (23/64) (by rfl) (by rfl)
    component10Node48_sound component10Node49_sound

private noncomputable def component10Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node51_sound : Sound component10Node51Box :=
  sound_of_literal_split component10Node51Box component10Node47Box component10Node50Box
    .k (31/16) (by rfl) (by rfl)
    component10Node47_sound component10Node50_sound

private noncomputable def component10Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node52_sound : Sound component10Node52Box :=
  sound_of_literal_split component10Node52Box component10Node44Box component10Node51Box
    .chi (11/32) (by rfl) (by rfl)
    component10Node44_sound component10Node51_sound

private noncomputable def component10Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component10Node53_sound : Sound component10Node53Box :=
  sound_of_literal_split component10Node53Box component10Node37Box component10Node52Box
    .k (15/8) (by rfl) (by rfl)
    component10Node37_sound component10Node52_sound

noncomputable def component10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component10_sound : Sound component10Box :=
  sound_of_literal_split component10Box component10Node28Box component10Node53Box
    .chi (5/16) (by rfl) (by rfl)
    component10Node28_sound component10Node53_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
