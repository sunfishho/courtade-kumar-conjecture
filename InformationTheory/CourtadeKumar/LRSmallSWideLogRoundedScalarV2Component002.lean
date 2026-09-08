import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
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

private noncomputable def leaf71Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16), chiLo := (1/2), chiHi := (5/8) }

private noncomputable def leaf71Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388635/8388608) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10452839/8388608) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk6LogOuterCertificate, logK := sk6LogKCertificate, logChi := chi8LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194263/4194214) } }, logDArg := sk6LogDArgCertificate }

private noncomputable def leaf71InnerLog : WideLogData :=
  innerPair14Data

set_option maxRecDepth 1000000 in
private theorem leaf71LocalValidity :
    LeafFacts leaf71Box leaf71Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf71Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097107) }) = true
      norm_num [leaf71Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf71CertificateValid :
    WideCertificateValid leaf71Box leaf71Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk6ValidityFacts chi8ValidityFacts
    leaf71LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf71CoverageChecked :
    coverageCheck (innerAD leaf71Box) leaf71InnerLog = true := by
  rfl'

private theorem leaf71InnerLogValid :
    leaf71InnerLog.Valid 8 (innerAD leaf71Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint7PositiveFacts.valid leaf71CoverageChecked

private noncomputable def leaf71InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf71InputLogOnePlusV_eq :
    leaf71InputLogOnePlusV = outerEnclosure 24
      (leaf71Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf71RoundedFacts : LeafRoundedFacts 8
    leaf71Certificate.logOnePlusV leaf71InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf71InputLogOnePlusV_eq }

private noncomputable def leaf71Inputs : Inputs :=
  inputsOfCaches globalInput sk6RoundedInputs
    chi8InputQChi innerPair14Input
    leaf71InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf71LowerChecked :
    lowerCheck 24 leaf71Box leaf71Inputs = true := by
  rfl'

private theorem leaf71CoversExact : CoversExact 8
    leaf71Box leaf71Certificate leaf71InnerLog leaf71Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk6RoundedFacts chi8RoundedFacts
    innerPair14RoundedFacts leaf71RoundedFacts (by rfl)

private theorem leaf71FlatSound : Sound leaf71Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf71CertificateValid
    leaf71InnerLogValid leaf71CoversExact leaf71LowerChecked

private noncomputable def leaf72Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8), chiLo := (1/2), chiHi := (5/8) }

private noncomputable def leaf72Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388637/8388608) }, vSqrt := { lower := (32767/32768), upper := (349526/349517) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10714965/8388608) }, upper := { exponent := 0, mantissa := (89/64) } }, logOuter := sk7LogOuterCertificate, logK := sk7LogKCertificate, logChi := chi8LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (699043/699034) } }, logDArg := sk7LogDArgCertificate }

private noncomputable def leaf72InnerLog : WideLogData :=
  innerPair19Data

set_option maxRecDepth 1000000 in
private theorem leaf72LocalValidity :
    LeafFacts leaf72Box leaf72Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf72Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (349526/349517) }) = true
      norm_num [leaf72Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf72CertificateValid :
    WideCertificateValid leaf72Box leaf72Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk7ValidityFacts chi8ValidityFacts
    leaf72LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf72CoverageChecked :
    coverageCheck (innerAD leaf72Box) leaf72InnerLog = true := by
  rfl'

private theorem leaf72InnerLogValid :
    leaf72InnerLog.Valid 8 (innerAD leaf72Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint10PositiveFacts.valid leaf72CoverageChecked

private noncomputable def leaf72InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf72InputLogOnePlusV_eq :
    leaf72InputLogOnePlusV = outerEnclosure 24
      (leaf72Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf72RoundedFacts : LeafRoundedFacts 8
    leaf72Certificate.logOnePlusV leaf72InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf72InputLogOnePlusV_eq }

private noncomputable def leaf72Inputs : Inputs :=
  inputsOfCaches globalInput sk7RoundedInputs
    chi8InputQChi innerPair19Input
    leaf72InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf72LowerChecked :
    lowerCheck 24 leaf72Box leaf72Inputs = true := by
  rfl'

private theorem leaf72CoversExact : CoversExact 8
    leaf72Box leaf72Certificate leaf72InnerLog leaf72Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk7RoundedFacts chi8RoundedFacts
    innerPair19RoundedFacts leaf72RoundedFacts (by rfl)

private theorem leaf72FlatSound : Sound leaf72Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf72CertificateValid
    leaf72InnerLogValid leaf72CoversExact leaf72LowerChecked

private noncomputable def leaf73Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf73Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388637/8388608) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10977093/8388608) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk6LogOuterCertificate, logK := sk6LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097127/2097098) } }, logDArg := sk6LogDArgCertificate }

private noncomputable def leaf73InnerLog : WideLogData :=
  innerPair19Data

set_option maxRecDepth 1000000 in
private theorem leaf73LocalValidity :
    LeafFacts leaf73Box leaf73Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf73Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048549) }) = true
      norm_num [leaf73Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf73CertificateValid :
    WideCertificateValid leaf73Box leaf73Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk6ValidityFacts chi9ValidityFacts
    leaf73LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf73CoverageChecked :
    coverageCheck (innerAD leaf73Box) leaf73InnerLog = true := by
  rfl'

private theorem leaf73InnerLogValid :
    leaf73InnerLog.Valid 8 (innerAD leaf73Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint10PositiveFacts.valid leaf73CoverageChecked

private noncomputable def leaf73InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf73InputLogOnePlusV_eq :
    leaf73InputLogOnePlusV = outerEnclosure 24
      (leaf73Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf73RoundedFacts : LeafRoundedFacts 8
    leaf73Certificate.logOnePlusV leaf73InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf73InputLogOnePlusV_eq }

private noncomputable def leaf73Inputs : Inputs :=
  inputsOfCaches globalInput sk6RoundedInputs
    chi9InputQChi innerPair19Input
    leaf73InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf73LowerChecked :
    lowerCheck 24 leaf73Box leaf73Inputs = true := by
  rfl'

private theorem leaf73CoversExact : CoversExact 8
    leaf73Box leaf73Certificate leaf73InnerLog leaf73Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk6RoundedFacts chi9RoundedFacts
    innerPair19RoundedFacts leaf73RoundedFacts (by rfl)

private theorem leaf73FlatSound : Sound leaf73Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf73CertificateValid
    leaf73InnerLogValid leaf73CoversExact leaf73LowerChecked

private noncomputable def leaf74Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf74Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388639/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358755328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (11304751/8388608) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk7LogOuterCertificate, logK := sk7LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68718034943/68717510656) } }, logDArg := sk7LogDArgCertificate }

private noncomputable def leaf74InnerLog : WideLogData :=
  innerPair23Data

set_option maxRecDepth 1000000 in
private theorem leaf74LocalValidity :
    LeafFacts leaf74Box leaf74Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf74Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358755328) }) = true
      norm_num [leaf74Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf74CertificateValid :
    WideCertificateValid leaf74Box leaf74Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk7ValidityFacts chi9ValidityFacts
    leaf74LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf74CoverageChecked :
    coverageCheck (innerAD leaf74Box) leaf74InnerLog = true := by
  rfl'

private theorem leaf74InnerLogValid :
    leaf74InnerLog.Valid 8 (innerAD leaf74Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint11PositiveFacts.valid leaf74CoverageChecked

private noncomputable def leaf74InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf74InputLogOnePlusV_eq :
    leaf74InputLogOnePlusV = outerEnclosure 24
      (leaf74Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf74RoundedFacts : LeafRoundedFacts 8
    leaf74Certificate.logOnePlusV leaf74InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf74InputLogOnePlusV_eq }

private noncomputable def leaf74Inputs : Inputs :=
  inputsOfCaches globalInput sk7RoundedInputs
    chi9InputQChi innerPair23Input
    leaf74InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf74LowerChecked :
    lowerCheck 24 leaf74Box leaf74Inputs = true := by
  rfl'

private theorem leaf74CoversExact : CoversExact 8
    leaf74Box leaf74Certificate leaf74InnerLog leaf74Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk7RoundedFacts chi9RoundedFacts
    innerPair23RoundedFacts leaf74RoundedFacts (by rfl)

private theorem leaf74FlatSound : Sound leaf74Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf74CertificateValid
    leaf74InnerLogValid leaf74CoversExact leaf74LowerChecked

private noncomputable def leaf75Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (1/2), chiHi := (5/8) }

private noncomputable def leaf75Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388639/8388608) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10977091/8388608) }, upper := { exponent := 0, mantissa := (183/128) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi8LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194253/4194194) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf75InnerLog : WideLogData :=
  innerPair19Data

set_option maxRecDepth 1000000 in
private theorem leaf75LocalValidity :
    LeafFacts leaf75Box leaf75Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf75Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097097) }) = true
      norm_num [leaf75Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf75CertificateValid :
    WideCertificateValid leaf75Box leaf75Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi8ValidityFacts
    leaf75LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf75CoverageChecked :
    coverageCheck (innerAD leaf75Box) leaf75InnerLog = true := by
  rfl'

private theorem leaf75InnerLogValid :
    leaf75InnerLog.Valid 8 (innerAD leaf75Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint10PositiveFacts.valid leaf75CoverageChecked

private noncomputable def leaf75InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf75InputLogOnePlusV_eq :
    leaf75InputLogOnePlusV = outerEnclosure 24
      (leaf75Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf75RoundedFacts : LeafRoundedFacts 8
    leaf75Certificate.logOnePlusV leaf75InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf75InputLogOnePlusV_eq }

private noncomputable def leaf75Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi8InputQChi innerPair19Input
    leaf75InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf75LowerChecked :
    lowerCheck 24 leaf75Box leaf75Inputs = true := by
  rfl'

private theorem leaf75CoversExact : CoversExact 8
    leaf75Box leaf75Certificate leaf75InnerLog leaf75Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi8RoundedFacts
    innerPair19RoundedFacts leaf75RoundedFacts (by rfl)

private theorem leaf75FlatSound : Sound leaf75Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf75CertificateValid
    leaf75InnerLogValid leaf75CoversExact leaf75LowerChecked

private noncomputable def leaf76Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (1/2), chiHi := (5/8) }

private noncomputable def leaf76Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388641/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358755328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (11239217/8388608) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi8LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68718034943/68717510656) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf76InnerLog : WideLogData :=
  innerPair23Data

set_option maxRecDepth 1000000 in
private theorem leaf76LocalValidity :
    LeafFacts leaf76Box leaf76Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf76Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358755328) }) = true
      norm_num [leaf76Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf76CertificateValid :
    WideCertificateValid leaf76Box leaf76Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi8ValidityFacts
    leaf76LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf76CoverageChecked :
    coverageCheck (innerAD leaf76Box) leaf76InnerLog = true := by
  rfl'

private theorem leaf76InnerLogValid :
    leaf76InnerLog.Valid 8 (innerAD leaf76Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint11PositiveFacts.valid leaf76CoverageChecked

private noncomputable def leaf76InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf76InputLogOnePlusV_eq :
    leaf76InputLogOnePlusV = outerEnclosure 24
      (leaf76Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf76RoundedFacts : LeafRoundedFacts 8
    leaf76Certificate.logOnePlusV leaf76InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf76InputLogOnePlusV_eq }

private noncomputable def leaf76Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi8InputQChi innerPair23Input
    leaf76InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf76LowerChecked :
    lowerCheck 24 leaf76Box leaf76Inputs = true := by
  rfl'

private theorem leaf76CoversExact : CoversExact 8
    leaf76Box leaf76Certificate leaf76InnerLog leaf76Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi8RoundedFacts
    innerPair23RoundedFacts leaf76RoundedFacts (by rfl)

private theorem leaf76FlatSound : Sound leaf76Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf76CertificateValid
    leaf76InnerLogValid leaf76CoversExact leaf76LowerChecked

private noncomputable def leaf77Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf77Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388641/8388608) }, vSqrt := { lower := (32767/32768), upper := (2021134095/2021097472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (11632409/8388608) }, upper := { exponent := 0, mantissa := (97/64) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4042231567/4042194944) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf77InnerLog : WideLogData :=
  innerPair28Data

set_option maxRecDepth 1000000 in
private theorem leaf77LocalValidity :
    LeafFacts leaf77Box leaf77Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf77Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2021134095/2021097472) }) = true
      norm_num [leaf77Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf77CertificateValid :
    WideCertificateValid leaf77Box leaf77Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi9ValidityFacts
    leaf77LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf77CoverageChecked :
    coverageCheck (innerAD leaf77Box) leaf77InnerLog = true := by
  rfl'

private theorem leaf77InnerLogValid :
    leaf77InnerLog.Valid 8 (innerAD leaf77Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint13PositiveFacts.valid leaf77CoverageChecked

private noncomputable def leaf77InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf77InputLogOnePlusV_eq :
    leaf77InputLogOnePlusV = outerEnclosure 24
      (leaf77Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf77RoundedFacts : LeafRoundedFacts 8
    leaf77Certificate.logOnePlusV leaf77InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf77InputLogOnePlusV_eq }

private noncomputable def leaf77Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi9InputQChi innerPair28Input
    leaf77InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf77LowerChecked :
    lowerCheck 24 leaf77Box leaf77Inputs = true := by
  rfl'

private theorem leaf77CoversExact : CoversExact 8
    leaf77Box leaf77Certificate leaf77InnerLog leaf77Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi9RoundedFacts
    innerPair28RoundedFacts leaf77RoundedFacts (by rfl)

private theorem leaf77FlatSound : Sound leaf77Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf77CertificateValid
    leaf77InnerLogValid leaf77CoversExact leaf77LowerChecked

private noncomputable def leaf78Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf78Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388643/8388608) }, vSqrt := { lower := (32767/32768), upper := (6871855923/6871711744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (11960067/8388608) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (13743567667/13743423488) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf78InnerLog : WideLogData :=
  innerPair28Data

set_option maxRecDepth 1000000 in
private theorem leaf78LocalValidity :
    LeafFacts leaf78Box leaf78Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf78Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (6871855923/6871711744) }) = true
      norm_num [leaf78Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf78CertificateValid :
    WideCertificateValid leaf78Box leaf78Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi9ValidityFacts
    leaf78LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf78CoverageChecked :
    coverageCheck (innerAD leaf78Box) leaf78InnerLog = true := by
  rfl'

private theorem leaf78InnerLogValid :
    leaf78InnerLog.Valid 8 (innerAD leaf78Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint13PositiveFacts.valid leaf78CoverageChecked

private noncomputable def leaf78InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf78InputLogOnePlusV_eq :
    leaf78InputLogOnePlusV = outerEnclosure 24
      (leaf78Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf78RoundedFacts : LeafRoundedFacts 8
    leaf78Certificate.logOnePlusV leaf78InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf78InputLogOnePlusV_eq }

private noncomputable def leaf78Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi9InputQChi innerPair28Input
    leaf78InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf78LowerChecked :
    lowerCheck 24 leaf78Box leaf78Inputs = true := by
  rfl'

private theorem leaf78CoversExact : CoversExact 8
    leaf78Box leaf78Certificate leaf78InnerLog leaf78Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi9RoundedFacts
    innerPair28RoundedFacts leaf78RoundedFacts (by rfl)

private theorem leaf78FlatSound : Sound leaf78Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf78CertificateValid
    leaf78InnerLogValid leaf78CoversExact leaf78LowerChecked

private noncomputable def leaf79Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf79Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388639/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358706176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (11501347/8388608) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk6LogOuterCertificate, logK := sk6LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717985791/68717412352) } }, logDArg := sk6LogDArgCertificate }

private noncomputable def leaf79InnerLog : WideLogData :=
  innerPair23Data

set_option maxRecDepth 1000000 in
private theorem leaf79LocalValidity :
    LeafFacts leaf79Box leaf79Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf79Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358706176) }) = true
      norm_num [leaf79Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf79CertificateValid :
    WideCertificateValid leaf79Box leaf79Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk6ValidityFacts chi19ValidityFacts
    leaf79LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf79CoverageChecked :
    coverageCheck (innerAD leaf79Box) leaf79InnerLog = true := by
  rfl'

private theorem leaf79InnerLogValid :
    leaf79InnerLog.Valid 8 (innerAD leaf79Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint11PositiveFacts.valid leaf79CoverageChecked

private noncomputable def leaf79InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf79InputLogOnePlusV_eq :
    leaf79InputLogOnePlusV = outerEnclosure 24
      (leaf79Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf79RoundedFacts : LeafRoundedFacts 8
    leaf79Certificate.logOnePlusV leaf79InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf79InputLogOnePlusV_eq }

private noncomputable def leaf79Inputs : Inputs :=
  inputsOfCaches globalInput sk6RoundedInputs
    chi19InputQChi innerPair23Input
    leaf79InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf79LowerChecked :
    lowerCheck 24 leaf79Box leaf79Inputs = true := by
  rfl'

private theorem leaf79CoversExact : CoversExact 8
    leaf79Box leaf79Certificate leaf79InnerLog leaf79Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk6RoundedFacts chi19RoundedFacts
    innerPair23RoundedFacts leaf79RoundedFacts (by rfl)

private theorem leaf79FlatSound : Sound leaf79Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf79CertificateValid
    leaf79InnerLogValid leaf79CoversExact leaf79LowerChecked

private noncomputable def leaf80Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf80Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388641/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358591488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (11894537/8388608) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk7LogOuterCertificate, logK := sk7LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717871103/68717182976) } }, logDArg := sk7LogDArgCertificate }

private noncomputable def leaf80InnerLog : WideLogData :=
  innerPair28Data

set_option maxRecDepth 1000000 in
private theorem leaf80LocalValidity :
    LeafFacts leaf80Box leaf80Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf80Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358591488) }) = true
      norm_num [leaf80Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf80CertificateValid :
    WideCertificateValid leaf80Box leaf80Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk7ValidityFacts chi19ValidityFacts
    leaf80LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf80CoverageChecked :
    coverageCheck (innerAD leaf80Box) leaf80InnerLog = true := by
  rfl'

private theorem leaf80InnerLogValid :
    leaf80InnerLog.Valid 8 (innerAD leaf80Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint13PositiveFacts.valid leaf80CoverageChecked

private noncomputable def leaf80InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf80InputLogOnePlusV_eq :
    leaf80InputLogOnePlusV = outerEnclosure 24
      (leaf80Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf80RoundedFacts : LeafRoundedFacts 8
    leaf80Certificate.logOnePlusV leaf80InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf80InputLogOnePlusV_eq }

private noncomputable def leaf80Inputs : Inputs :=
  inputsOfCaches globalInput sk7RoundedInputs
    chi19InputQChi innerPair28Input
    leaf80InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf80LowerChecked :
    lowerCheck 24 leaf80Box leaf80Inputs = true := by
  rfl'

private theorem leaf80CoversExact : CoversExact 8
    leaf80Box leaf80Certificate leaf80InnerLog leaf80Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk7RoundedFacts chi19RoundedFacts
    innerPair28RoundedFacts leaf80RoundedFacts (by rfl)

private theorem leaf80FlatSound : Sound leaf80Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf80CertificateValid
    leaf80InnerLogValid leaf80CoversExact leaf80LowerChecked

private noncomputable def leaf81Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf81Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388641/8388608) }, vSqrt := { lower := (32767/32768), upper := (6871855923/6871711744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12025601/8388608) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk6LogOuterCertificate, logK := sk6LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (13743567667/13743423488) } }, logDArg := sk6LogDArgCertificate }

private noncomputable def leaf81InnerLog : WideLogData :=
  innerPair28Data

set_option maxRecDepth 1000000 in
private theorem leaf81LocalValidity :
    LeafFacts leaf81Box leaf81Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf81Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (6871855923/6871711744) }) = true
      norm_num [leaf81Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf81CertificateValid :
    WideCertificateValid leaf81Box leaf81Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk6ValidityFacts chi20ValidityFacts
    leaf81LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf81CoverageChecked :
    coverageCheck (innerAD leaf81Box) leaf81InnerLog = true := by
  rfl'

private theorem leaf81InnerLogValid :
    leaf81InnerLog.Valid 8 (innerAD leaf81Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint13PositiveFacts.valid leaf81CoverageChecked

private noncomputable def leaf81InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf81InputLogOnePlusV_eq :
    leaf81InputLogOnePlusV = outerEnclosure 24
      (leaf81Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf81RoundedFacts : LeafRoundedFacts 8
    leaf81Certificate.logOnePlusV leaf81InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf81InputLogOnePlusV_eq }

private noncomputable def leaf81Inputs : Inputs :=
  inputsOfCaches globalInput sk6RoundedInputs
    chi20InputQChi innerPair28Input
    leaf81InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf81LowerChecked :
    lowerCheck 24 leaf81Box leaf81Inputs = true := by
  rfl'

private theorem leaf81CoversExact : CoversExact 8
    leaf81Box leaf81Certificate leaf81InnerLog leaf81Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk6RoundedFacts chi20RoundedFacts
    innerPair28RoundedFacts leaf81RoundedFacts (by rfl)

private theorem leaf81FlatSound : Sound leaf81Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf81CertificateValid
    leaf81InnerLogValid leaf81CoversExact leaf81LowerChecked

private noncomputable def leaf82Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf82Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388643/8388608) }, vSqrt := { lower := (32767/32768), upper := (3817697735/3817603072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12484323/8388608) }, upper := { exponent := 0, mantissa := (13/8) } }, logOuter := sk7LogOuterCertificate, logK := sk7LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (7635300807/7635206144) } }, logDArg := sk7LogDArgCertificate }

private noncomputable def leaf82InnerLog : WideLogData :=
  innerPair36Data

set_option maxRecDepth 1000000 in
private theorem leaf82LocalValidity :
    LeafFacts leaf82Box leaf82Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf82Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (3817697735/3817603072) }) = true
      norm_num [leaf82Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf82CertificateValid :
    WideCertificateValid leaf82Box leaf82Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk7ValidityFacts chi20ValidityFacts
    leaf82LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf82CoverageChecked :
    coverageCheck (innerAD leaf82Box) leaf82InnerLog = true := by
  rfl'

private theorem leaf82InnerLogValid :
    leaf82InnerLog.Valid 8 (innerAD leaf82Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint14PositiveFacts.valid leaf82CoverageChecked

private noncomputable def leaf82InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf82InputLogOnePlusV_eq :
    leaf82InputLogOnePlusV = outerEnclosure 24
      (leaf82Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf82RoundedFacts : LeafRoundedFacts 8
    leaf82Certificate.logOnePlusV leaf82InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf82InputLogOnePlusV_eq }

private noncomputable def leaf82Inputs : Inputs :=
  inputsOfCaches globalInput sk7RoundedInputs
    chi20InputQChi innerPair36Input
    leaf82InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf82LowerChecked :
    lowerCheck 24 leaf82Box leaf82Inputs = true := by
  rfl'

private theorem leaf82CoversExact : CoversExact 8
    leaf82Box leaf82Certificate leaf82InnerLog leaf82Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk7RoundedFacts chi20RoundedFacts
    innerPair36RoundedFacts leaf82RoundedFacts (by rfl)

private theorem leaf82FlatSound : Sound leaf82Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf82CertificateValid
    leaf82InnerLogValid leaf82CoversExact leaf82LowerChecked

private noncomputable def leaf83Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf83Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388643/8388608) }, vSqrt := { lower := (32767/32768), upper := (2290618641/2290565120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12287727/8388608) }, upper := { exponent := 0, mantissa := (205/128) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4581183761/4581130240) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf83InnerLog : WideLogData :=
  innerPair36Data

set_option maxRecDepth 1000000 in
private theorem leaf83LocalValidity :
    LeafFacts leaf83Box leaf83Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf83Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2290618641/2290565120) }) = true
      norm_num [leaf83Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf83CertificateValid :
    WideCertificateValid leaf83Box leaf83Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi19ValidityFacts
    leaf83LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf83CoverageChecked :
    coverageCheck (innerAD leaf83Box) leaf83InnerLog = true := by
  rfl'

private theorem leaf83InnerLogValid :
    leaf83InnerLog.Valid 8 (innerAD leaf83Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint14PositiveFacts.valid leaf83CoverageChecked

private noncomputable def leaf83InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf83InputLogOnePlusV_eq :
    leaf83InputLogOnePlusV = outerEnclosure 24
      (leaf83Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf83RoundedFacts : LeafRoundedFacts 8
    leaf83Certificate.logOnePlusV leaf83InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf83InputLogOnePlusV_eq }

private noncomputable def leaf83Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi19InputQChi innerPair36Input
    leaf83InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf83LowerChecked :
    lowerCheck 24 leaf83Box leaf83Inputs = true := by
  rfl'

private theorem leaf83CoversExact : CoversExact 8
    leaf83Box leaf83Certificate leaf83InnerLog leaf83Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi19RoundedFacts
    innerPair36RoundedFacts leaf83RoundedFacts (by rfl)

private theorem leaf83FlatSound : Sound leaf83Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf83CertificateValid
    leaf83InnerLogValid leaf83CoversExact leaf83LowerChecked

private noncomputable def leaf84Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf84Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388645/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358362112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12680917/8388608) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717641727/68716724224) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf84InnerLog : WideLogData :=
  innerPair42Data

set_option maxRecDepth 1000000 in
private theorem leaf84LocalValidity :
    LeafFacts leaf84Box leaf84Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf84Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358362112) }) = true
      norm_num [leaf84Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf84CertificateValid :
    WideCertificateValid leaf84Box leaf84Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi19ValidityFacts
    leaf84LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf84CoverageChecked :
    coverageCheck (innerAD leaf84Box) leaf84InnerLog = true := by
  rfl'

private theorem leaf84InnerLogValid :
    leaf84InnerLog.Valid 8 (innerAD leaf84Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint15PositiveFacts.valid leaf84CoverageChecked

private noncomputable def leaf84InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf84InputLogOnePlusV_eq :
    leaf84InputLogOnePlusV = outerEnclosure 24
      (leaf84Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf84RoundedFacts : LeafRoundedFacts 8
    leaf84Certificate.logOnePlusV leaf84InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf84InputLogOnePlusV_eq }

private noncomputable def leaf84Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi19InputQChi innerPair42Input
    leaf84InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf84LowerChecked :
    lowerCheck 24 leaf84Box leaf84Inputs = true := by
  rfl'

private theorem leaf84CoversExact : CoversExact 8
    leaf84Box leaf84Certificate leaf84InnerLog leaf84Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi19RoundedFacts
    innerPair42RoundedFacts leaf84RoundedFacts (by rfl)

private theorem leaf84FlatSound : Sound leaf84Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf84CertificateValid
    leaf84InnerLogValid leaf84CoversExact leaf84LowerChecked

private noncomputable def leaf85Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf85Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388645/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358296576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12943045/8388608) }, upper := { exponent := 0, mantissa := (27/16) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717576191/68716593152) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf85InnerLog : WideLogData :=
  innerPair42Data

set_option maxRecDepth 1000000 in
private theorem leaf85LocalValidity :
    LeafFacts leaf85Box leaf85Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf85Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358296576) }) = true
      norm_num [leaf85Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf85CertificateValid :
    WideCertificateValid leaf85Box leaf85Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi20ValidityFacts
    leaf85LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf85CoverageChecked :
    coverageCheck (innerAD leaf85Box) leaf85InnerLog = true := by
  rfl'

private theorem leaf85InnerLogValid :
    leaf85InnerLog.Valid 8 (innerAD leaf85Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint15PositiveFacts.valid leaf85CoverageChecked

private noncomputable def leaf85InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf85InputLogOnePlusV_eq :
    leaf85InputLogOnePlusV = outerEnclosure 24
      (leaf85Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf85RoundedFacts : LeafRoundedFacts 8
    leaf85Certificate.logOnePlusV leaf85InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf85InputLogOnePlusV_eq }

private noncomputable def leaf85Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi20InputQChi innerPair42Input
    leaf85InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf85LowerChecked :
    lowerCheck 24 leaf85Box leaf85Inputs = true := by
  rfl'

private theorem leaf85CoversExact : CoversExact 8
    leaf85Box leaf85Certificate leaf85InnerLog leaf85Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi20RoundedFacts
    innerPair42RoundedFacts leaf85RoundedFacts (by rfl)

private theorem leaf85FlatSound : Sound leaf85Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf85CertificateValid
    leaf85InnerLogValid leaf85CoversExact leaf85LowerChecked

private noncomputable def leaf86Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf86Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388647/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358165504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (13401767/8388608) }, upper := { exponent := 0, mantissa := (7/4) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717445119/68716331008) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf86InnerLog : WideLogData :=
  innerPair52Data

set_option maxRecDepth 1000000 in
private theorem leaf86LocalValidity :
    LeafFacts leaf86Box leaf86Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf86Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358165504) }) = true
      norm_num [leaf86Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf86CertificateValid :
    WideCertificateValid leaf86Box leaf86Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi20ValidityFacts
    leaf86LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf86CoverageChecked :
    coverageCheck (innerAD leaf86Box) leaf86InnerLog = true := by
  rfl'

private theorem leaf86InnerLogValid :
    leaf86InnerLog.Valid 8 (innerAD leaf86Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint16PositiveFacts.valid leaf86CoverageChecked

private noncomputable def leaf86InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf86InputLogOnePlusV_eq :
    leaf86InputLogOnePlusV = outerEnclosure 24
      (leaf86Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf86RoundedFacts : LeafRoundedFacts 8
    leaf86Certificate.logOnePlusV leaf86InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf86InputLogOnePlusV_eq }

private noncomputable def leaf86Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi20InputQChi innerPair52Input
    leaf86InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf86LowerChecked :
    lowerCheck 24 leaf86Box leaf86Inputs = true := by
  rfl'

private theorem leaf86CoversExact : CoversExact 8
    leaf86Box leaf86Certificate leaf86InnerLog leaf86Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi20RoundedFacts
    innerPair52RoundedFacts leaf86RoundedFacts (by rfl)

private theorem leaf86FlatSound : Sound leaf86Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf86CertificateValid
    leaf86InnerLogValid leaf86CoversExact leaf86LowerChecked

private noncomputable def leaf87Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (1/2), chiHi := (5/8) }

private noncomputable def leaf87Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388643/8388608) }, vSqrt := { lower := (32767/32768), upper := (11453093205/11452891136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (11501343/8388608) }, upper := { exponent := 0, mantissa := (193/128) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi8LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (22905984341/22905782272) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf87InnerLog : WideLogData :=
  innerPair82Data

set_option maxRecDepth 1000000 in
private theorem leaf87LocalValidity :
    LeafFacts leaf87Box leaf87Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf87Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (11453093205/11452891136) }) = true
      norm_num [leaf87Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf87CertificateValid :
    WideCertificateValid leaf87Box leaf87Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi8ValidityFacts
    leaf87LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf87CoverageChecked :
    coverageCheck (innerAD leaf87Box) leaf87InnerLog = true := by
  rfl'

private theorem leaf87InnerLogValid :
    leaf87InnerLog.Valid 8 (innerAD leaf87Box) :=
  wideLogDataValid_of_cachedCheck endpoint17PositiveFacts
    endpoint18PositiveFacts.valid leaf87CoverageChecked

private noncomputable def leaf87InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf87InputLogOnePlusV_eq :
    leaf87InputLogOnePlusV = outerEnclosure 24
      (leaf87Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf87RoundedFacts : LeafRoundedFacts 8
    leaf87Certificate.logOnePlusV leaf87InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf87InputLogOnePlusV_eq }

private noncomputable def leaf87Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi8InputQChi innerPair82Input
    leaf87InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf87LowerChecked :
    lowerCheck 24 leaf87Box leaf87Inputs = true := by
  rfl'

private theorem leaf87CoversExact : CoversExact 8
    leaf87Box leaf87Certificate leaf87InnerLog leaf87Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi8RoundedFacts
    innerPair82RoundedFacts leaf87RoundedFacts (by rfl)

private theorem leaf87FlatSound : Sound leaf87Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf87CertificateValid
    leaf87InnerLogValid leaf87CoversExact leaf87LowerChecked

private noncomputable def leaf88Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (1/2), chiHi := (9/16) }

private noncomputable def leaf88Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777261/16777216) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358706176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (23559733/16777216) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi21LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717985791/68717412352) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf88InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf88LocalValidity :
    LeafFacts leaf88Box leaf88Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf88Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358706176) }) = true
      norm_num [leaf88Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf88CertificateValid :
    WideCertificateValid leaf88Box leaf88Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi21ValidityFacts
    leaf88LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf88CoverageChecked :
    coverageCheck (innerAD leaf88Box) leaf88InnerLog = true := by
  rfl'

private theorem leaf88InnerLogValid :
    leaf88InnerLog.Valid 8 (innerAD leaf88Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf88CoverageChecked

private noncomputable def leaf88InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf88InputLogOnePlusV_eq :
    leaf88InputLogOnePlusV = outerEnclosure 24
      (leaf88Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf88RoundedFacts : LeafRoundedFacts 8
    leaf88Certificate.logOnePlusV leaf88InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf88InputLogOnePlusV_eq }

private noncomputable def leaf88Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi21InputQChi innerPair27Input
    leaf88InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf88LowerChecked :
    lowerCheck 24 leaf88Box leaf88Inputs = true := by
  rfl'

private theorem leaf88CoversExact : CoversExact 8
    leaf88Box leaf88Certificate leaf88InnerLog leaf88Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi21RoundedFacts
    innerPair27RoundedFacts leaf88RoundedFacts (by rfl)

private theorem leaf88FlatSound : Sound leaf88Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf88CertificateValid
    leaf88InnerLogValid leaf88CoversExact leaf88LowerChecked

private noncomputable def leaf89Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf89Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777263/16777216) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358591488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (24411647/16777216) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717871103/68717182976) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf89InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf89LocalValidity :
    LeafFacts leaf89Box leaf89Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf89Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358591488) }) = true
      norm_num [leaf89Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf89CertificateValid :
    WideCertificateValid leaf89Box leaf89Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi22ValidityFacts
    leaf89LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf89CoverageChecked :
    coverageCheck (innerAD leaf89Box) leaf89InnerLog = true := by
  rfl'

private theorem leaf89InnerLogValid :
    leaf89InnerLog.Valid 8 (innerAD leaf89Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf89CoverageChecked

private noncomputable def leaf89InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf89InputLogOnePlusV_eq :
    leaf89InputLogOnePlusV = outerEnclosure 24
      (leaf89Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf89RoundedFacts : LeafRoundedFacts 8
    leaf89Certificate.logOnePlusV leaf89InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf89InputLogOnePlusV_eq }

private noncomputable def leaf89Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi22InputQChi innerPair35Input
    leaf89InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf89LowerChecked :
    lowerCheck 24 leaf89Box leaf89Inputs = true := by
  rfl'

private theorem leaf89CoversExact : CoversExact 8
    leaf89Box leaf89Certificate leaf89InnerLog leaf89Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi22RoundedFacts
    innerPair35RoundedFacts leaf89RoundedFacts (by rfl)

private theorem leaf89FlatSound : Sound leaf89Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf89CertificateValid
    leaf89InnerLogValid leaf89CoversExact leaf89LowerChecked

private noncomputable def leaf90Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf90Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388645/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358460416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12287725/8388608) }, upper := { exponent := 0, mantissa := (103/64) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717740031/68716920832) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf90InnerLog : WideLogData :=
  innerPair36Data

set_option maxRecDepth 1000000 in
private theorem leaf90LocalValidity :
    LeafFacts leaf90Box leaf90Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf90Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358460416) }) = true
      norm_num [leaf90Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf90CertificateValid :
    WideCertificateValid leaf90Box leaf90Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi9ValidityFacts
    leaf90LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf90CoverageChecked :
    coverageCheck (innerAD leaf90Box) leaf90InnerLog = true := by
  rfl'

private theorem leaf90InnerLogValid :
    leaf90InnerLog.Valid 8 (innerAD leaf90Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint14PositiveFacts.valid leaf90CoverageChecked

private noncomputable def leaf90InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf90InputLogOnePlusV_eq :
    leaf90InputLogOnePlusV = outerEnclosure 24
      (leaf90Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf90RoundedFacts : LeafRoundedFacts 8
    leaf90Certificate.logOnePlusV leaf90InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf90InputLogOnePlusV_eq }

private noncomputable def leaf90Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi9InputQChi innerPair36Input
    leaf90InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf90LowerChecked :
    lowerCheck 24 leaf90Box leaf90Inputs = true := by
  rfl'

private theorem leaf90CoversExact : CoversExact 8
    leaf90Box leaf90Certificate leaf90InnerLog leaf90Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi9RoundedFacts
    innerPair36RoundedFacts leaf90RoundedFacts (by rfl)

private theorem leaf90FlatSound : Sound leaf90Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf90CertificateValid
    leaf90InnerLogValid leaf90CoversExact leaf90LowerChecked

private noncomputable def leaf91Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf91Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388647/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358362112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12615383/8388608) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717641727/68716724224) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf91InnerLog : WideLogData :=
  innerPair42Data

set_option maxRecDepth 1000000 in
private theorem leaf91LocalValidity :
    LeafFacts leaf91Box leaf91Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf91Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358362112) }) = true
      norm_num [leaf91Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf91CertificateValid :
    WideCertificateValid leaf91Box leaf91Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi9ValidityFacts
    leaf91LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf91CoverageChecked :
    coverageCheck (innerAD leaf91Box) leaf91InnerLog = true := by
  rfl'

private theorem leaf91InnerLogValid :
    leaf91InnerLog.Valid 8 (innerAD leaf91Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint15PositiveFacts.valid leaf91CoverageChecked

private noncomputable def leaf91InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf91InputLogOnePlusV_eq :
    leaf91InputLogOnePlusV = outerEnclosure 24
      (leaf91Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf91RoundedFacts : LeafRoundedFacts 8
    leaf91Certificate.logOnePlusV leaf91InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf91InputLogOnePlusV_eq }

private noncomputable def leaf91Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi9InputQChi innerPair42Input
    leaf91InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf91LowerChecked :
    lowerCheck 24 leaf91Box leaf91Inputs = true := by
  rfl'

private theorem leaf91CoversExact : CoversExact 8
    leaf91Box leaf91Certificate leaf91InnerLog leaf91Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi9RoundedFacts
    innerPair42RoundedFacts leaf91RoundedFacts (by rfl)

private theorem leaf91FlatSound : Sound leaf91Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf91CertificateValid
    leaf91InnerLogValid leaf91CoversExact leaf91LowerChecked

private noncomputable def leaf92Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (1/2), chiHi := (9/16) }

private noncomputable def leaf92Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777263/16777216) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358632448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (24083987/16777216) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi21LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717912063/68717264896) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf92InnerLog : WideLogData :=
  innerPair28Data

set_option maxRecDepth 1000000 in
private theorem leaf92LocalValidity :
    LeafFacts leaf92Box leaf92Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf92Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358632448) }) = true
      norm_num [leaf92Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf92CertificateValid :
    WideCertificateValid leaf92Box leaf92Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi21ValidityFacts
    leaf92LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf92CoverageChecked :
    coverageCheck (innerAD leaf92Box) leaf92InnerLog = true := by
  rfl'

private theorem leaf92InnerLogValid :
    leaf92InnerLog.Valid 8 (innerAD leaf92Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint13PositiveFacts.valid leaf92CoverageChecked

private noncomputable def leaf92InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf92InputLogOnePlusV_eq :
    leaf92InputLogOnePlusV = outerEnclosure 24
      (leaf92Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf92RoundedFacts : LeafRoundedFacts 8
    leaf92Certificate.logOnePlusV leaf92InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf92InputLogOnePlusV_eq }

private noncomputable def leaf92Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi21InputQChi innerPair28Input
    leaf92InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf92LowerChecked :
    lowerCheck 24 leaf92Box leaf92Inputs = true := by
  rfl'

private theorem leaf92CoversExact : CoversExact 8
    leaf92Box leaf92Certificate leaf92InnerLog leaf92Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi21RoundedFacts
    innerPair28RoundedFacts leaf92RoundedFacts (by rfl)

private theorem leaf92FlatSound : Sound leaf92Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf92CertificateValid
    leaf92InnerLogValid leaf92CoversExact leaf92LowerChecked

private noncomputable def leaf93Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (1/2), chiHi := (9/16) }

private noncomputable def leaf93Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777265/16777216) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871711744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (24608241/16777216) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi21LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743567667/13743423488) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf93InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf93LocalValidity :
    LeafFacts leaf93Box leaf93Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf93Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871711744) }) = true
      norm_num [leaf93Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf93CertificateValid :
    WideCertificateValid leaf93Box leaf93Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi21ValidityFacts
    leaf93LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf93CoverageChecked :
    coverageCheck (innerAD leaf93Box) leaf93InnerLog = true := by
  rfl'

private theorem leaf93InnerLogValid :
    leaf93InnerLog.Valid 8 (innerAD leaf93Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf93CoverageChecked

private noncomputable def leaf93InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf93InputLogOnePlusV_eq :
    leaf93InputLogOnePlusV = outerEnclosure 24
      (leaf93Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf93RoundedFacts : LeafRoundedFacts 8
    leaf93Certificate.logOnePlusV leaf93InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf93InputLogOnePlusV_eq }

private noncomputable def leaf93Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi21InputQChi innerPair35Input
    leaf93InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf93LowerChecked :
    lowerCheck 24 leaf93Box leaf93Inputs = true := by
  rfl'

private theorem leaf93CoversExact : CoversExact 8
    leaf93Box leaf93Certificate leaf93InnerLog leaf93Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi21RoundedFacts
    innerPair35RoundedFacts leaf93RoundedFacts (by rfl)

private theorem leaf93FlatSound : Sound leaf93Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf93CertificateValid
    leaf93InnerLogValid leaf93CoversExact leaf93LowerChecked

private noncomputable def leaf94Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf94Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777265/16777216) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358509568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (25001433/16777216) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717789183/68717019136) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf94InnerLog : WideLogData :=
  innerPair36Data

set_option maxRecDepth 1000000 in
private theorem leaf94LocalValidity :
    LeafFacts leaf94Box leaf94Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf94Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358509568) }) = true
      norm_num [leaf94Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf94CertificateValid :
    WideCertificateValid leaf94Box leaf94Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi22ValidityFacts
    leaf94LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf94CoverageChecked :
    coverageCheck (innerAD leaf94Box) leaf94InnerLog = true := by
  rfl'

private theorem leaf94InnerLogValid :
    leaf94InnerLog.Valid 8 (innerAD leaf94Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint14PositiveFacts.valid leaf94CoverageChecked

private noncomputable def leaf94InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf94InputLogOnePlusV_eq :
    leaf94InputLogOnePlusV = outerEnclosure 24
      (leaf94Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf94RoundedFacts : LeafRoundedFacts 8
    leaf94Certificate.logOnePlusV leaf94InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf94InputLogOnePlusV_eq }

private noncomputable def leaf94Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi22InputQChi innerPair36Input
    leaf94InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf94LowerChecked :
    lowerCheck 24 leaf94Box leaf94Inputs = true := by
  rfl'

private theorem leaf94CoversExact : CoversExact 8
    leaf94Box leaf94Certificate leaf94InnerLog leaf94Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi22RoundedFacts
    innerPair36RoundedFacts leaf94RoundedFacts (by rfl)

private theorem leaf94FlatSound : Sound leaf94Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf94CertificateValid
    leaf94InnerLogValid leaf94CoversExact leaf94LowerChecked

private noncomputable def leaf95Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf95Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777267/16777216) }, vSqrt := { lower := (65533/65536), upper := (3817697735/3817603072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (25591219/16777216) }, upper := { exponent := 0, mantissa := (13/8) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (7635300807/7635206144) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf95InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf95LocalValidity :
    LeafFacts leaf95Box leaf95Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf95Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (3817697735/3817603072) }) = true
      norm_num [leaf95Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf95CertificateValid :
    WideCertificateValid leaf95Box leaf95Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi22ValidityFacts
    leaf95LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf95CoverageChecked :
    coverageCheck (innerAD leaf95Box) leaf95InnerLog = true := by
  rfl'

private theorem leaf95InnerLogValid :
    leaf95InnerLog.Valid 8 (innerAD leaf95Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf95CoverageChecked

private noncomputable def leaf95InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf95InputLogOnePlusV_eq :
    leaf95InputLogOnePlusV = outerEnclosure 24
      (leaf95Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf95RoundedFacts : LeafRoundedFacts 8
    leaf95Certificate.logOnePlusV leaf95InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf95InputLogOnePlusV_eq }

private noncomputable def leaf95Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi22InputQChi innerPair41Input
    leaf95InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf95LowerChecked :
    lowerCheck 24 leaf95Box leaf95Inputs = true := by
  rfl'

private theorem leaf95CoversExact : CoversExact 8
    leaf95Box leaf95Certificate leaf95InnerLog leaf95Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi22RoundedFacts
    innerPair41RoundedFacts leaf95RoundedFacts (by rfl)

private theorem leaf95FlatSound : Sound leaf95Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf95CertificateValid
    leaf95InnerLogValid leaf95CoversExact leaf95LowerChecked

private noncomputable def leaf96Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (5/8), chiHi := (3/4) }

private noncomputable def leaf96Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388649/8388608) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358263808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (12943041/8388608) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi9LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717543423/68716527616) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf96InnerLog : WideLogData :=
  innerPair84Data

set_option maxRecDepth 1000000 in
private theorem leaf96LocalValidity :
    LeafFacts leaf96Box leaf96Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf96Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358263808) }) = true
      norm_num [leaf96Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf96CertificateValid :
    WideCertificateValid leaf96Box leaf96Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi9ValidityFacts
    leaf96LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf96CoverageChecked :
    coverageCheck (innerAD leaf96Box) leaf96InnerLog = true := by
  rfl'

private theorem leaf96InnerLogValid :
    leaf96InnerLog.Valid 8 (innerAD leaf96Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint20PositiveFacts.valid leaf96CoverageChecked

private noncomputable def leaf96InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf96InputLogOnePlusV_eq :
    leaf96InputLogOnePlusV = outerEnclosure 24
      (leaf96Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf96RoundedFacts : LeafRoundedFacts 8
    leaf96Certificate.logOnePlusV leaf96InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf96InputLogOnePlusV_eq }

private noncomputable def leaf96Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi9InputQChi innerPair84Input
    leaf96InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf96LowerChecked :
    lowerCheck 24 leaf96Box leaf96Inputs = true := by
  rfl'

private theorem leaf96CoversExact : CoversExact 8
    leaf96Box leaf96Certificate leaf96InnerLog leaf96Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi9RoundedFacts
    innerPair84RoundedFacts leaf96RoundedFacts (by rfl)

private theorem leaf96FlatSound : Sound leaf96Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf96CertificateValid
    leaf96InnerLogValid leaf96CoversExact leaf96LowerChecked

private noncomputable def leaf97Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf97Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777269/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358296576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (26574197/16777216) }, upper := { exponent := 0, mantissa := (27/16) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717576191/68716593152) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf97InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf97LocalValidity :
    LeafFacts leaf97Box leaf97Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf97Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358296576) }) = true
      norm_num [leaf97Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf97CertificateValid :
    WideCertificateValid leaf97Box leaf97Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi23ValidityFacts
    leaf97LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf97CoverageChecked :
    coverageCheck (innerAD leaf97Box) leaf97InnerLog = true := by
  rfl'

private theorem leaf97InnerLogValid :
    leaf97InnerLog.Valid 8 (innerAD leaf97Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf97CoverageChecked

private noncomputable def leaf97InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf97InputLogOnePlusV_eq :
    leaf97InputLogOnePlusV = outerEnclosure 24
      (leaf97Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf97RoundedFacts : LeafRoundedFacts 8
    leaf97Certificate.logOnePlusV leaf97InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf97InputLogOnePlusV_eq }

private noncomputable def leaf97Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi23InputQChi innerPair51Input
    leaf97InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf97LowerChecked :
    lowerCheck 24 leaf97Box leaf97Inputs = true := by
  rfl'

private theorem leaf97CoversExact : CoversExact 8
    leaf97Box leaf97Certificate leaf97InnerLog leaf97Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi23RoundedFacts
    innerPair51RoundedFacts leaf97RoundedFacts (by rfl)

private theorem leaf97FlatSound : Sound leaf97Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf97CertificateValid
    leaf97InnerLogValid leaf97CoversExact leaf97LowerChecked

private noncomputable def leaf98Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf98Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777271/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358165504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (27557175/16777216) }, upper := { exponent := 0, mantissa := (7/4) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717445119/68716331008) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf98InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf98LocalValidity :
    LeafFacts leaf98Box leaf98Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf98Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358165504) }) = true
      norm_num [leaf98Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf98CertificateValid :
    WideCertificateValid leaf98Box leaf98Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi24ValidityFacts
    leaf98LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf98CoverageChecked :
    coverageCheck (innerAD leaf98Box) leaf98InnerLog = true := by
  rfl'

private theorem leaf98InnerLogValid :
    leaf98InnerLog.Valid 8 (innerAD leaf98Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf98CoverageChecked

private noncomputable def leaf98InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf98InputLogOnePlusV_eq :
    leaf98InputLogOnePlusV = outerEnclosure 24
      (leaf98Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf98RoundedFacts : LeafRoundedFacts 8
    leaf98Certificate.logOnePlusV leaf98InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf98InputLogOnePlusV_eq }

private noncomputable def leaf98Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi24InputQChi innerPair57Input
    leaf98InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf98LowerChecked :
    lowerCheck 24 leaf98Box leaf98Inputs = true := by
  rfl'

private theorem leaf98CoversExact : CoversExact 8
    leaf98Box leaf98Certificate leaf98InnerLog leaf98Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi24RoundedFacts
    innerPair57RoundedFacts leaf98RoundedFacts (by rfl)

private theorem leaf98FlatSound : Sound leaf98Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf98CertificateValid
    leaf98InnerLogValid leaf98CoversExact leaf98LowerChecked

private noncomputable def leaf99Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf99Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388647/8388608) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358247424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (13074107/8388608) }, upper := { exponent := 0, mantissa := (219/128) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68717527039/68716494848) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf99InnerLog : WideLogData :=
  innerPair43Data

set_option maxRecDepth 1000000 in
private theorem leaf99LocalValidity :
    LeafFacts leaf99Box leaf99Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf99Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358247424) }) = true
      norm_num [leaf99Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf99CertificateValid :
    WideCertificateValid leaf99Box leaf99Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi19ValidityFacts
    leaf99LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf99CoverageChecked :
    coverageCheck (innerAD leaf99Box) leaf99InnerLog = true := by
  rfl'

private theorem leaf99InnerLogValid :
    leaf99InnerLog.Valid 8 (innerAD leaf99Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint16PositiveFacts.valid leaf99CoverageChecked

private noncomputable def leaf99InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf99InputLogOnePlusV_eq :
    leaf99InputLogOnePlusV = outerEnclosure 24
      (leaf99Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf99RoundedFacts : LeafRoundedFacts 8
    leaf99Certificate.logOnePlusV leaf99InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf99InputLogOnePlusV_eq }

private noncomputable def leaf99Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi19InputQChi innerPair43Input
    leaf99InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf99LowerChecked :
    lowerCheck 24 leaf99Box leaf99Inputs = true := by
  rfl'

private theorem leaf99CoversExact : CoversExact 8
    leaf99Box leaf99Certificate leaf99InnerLog leaf99Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi19RoundedFacts
    innerPair43RoundedFacts leaf99RoundedFacts (by rfl)

private theorem leaf99FlatSound : Sound leaf99Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf99CertificateValid
    leaf99InnerLogValid leaf99CoversExact leaf99LowerChecked

private noncomputable def leaf100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388649/8388608) }, vSqrt := { lower := (32767/32768), upper := (3817697735/3817570304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (13467297/8388608) }, upper := { exponent := 0, mantissa := (113/64) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (7635268039/7635140608) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf100InnerLog : WideLogData :=
  innerPair53Data

set_option maxRecDepth 1000000 in
private theorem leaf100LocalValidity :
    LeafFacts leaf100Box leaf100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (3817697735/3817570304) }) = true
      norm_num [leaf100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf100CertificateValid :
    WideCertificateValid leaf100Box leaf100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi19ValidityFacts
    leaf100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf100CoverageChecked :
    coverageCheck (innerAD leaf100Box) leaf100InnerLog = true := by
  rfl'

private theorem leaf100InnerLogValid :
    leaf100InnerLog.Valid 8 (innerAD leaf100Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint21PositiveFacts.valid leaf100CoverageChecked

private noncomputable def leaf100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf100InputLogOnePlusV_eq :
    leaf100InputLogOnePlusV = outerEnclosure 24
      (leaf100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf100RoundedFacts : LeafRoundedFacts 8
    leaf100Certificate.logOnePlusV leaf100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf100InputLogOnePlusV_eq }

private noncomputable def leaf100Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi19InputQChi innerPair53Input
    leaf100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf100LowerChecked :
    lowerCheck 24 leaf100Box leaf100Inputs = true := by
  rfl'

private theorem leaf100CoversExact : CoversExact 8
    leaf100Box leaf100Certificate leaf100InnerLog leaf100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi19RoundedFacts
    innerPair53RoundedFacts leaf100RoundedFacts (by rfl)

private theorem leaf100FlatSound : Sound leaf100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf100CertificateValid
    leaf100InnerLogValid leaf100CoversExact leaf100LowerChecked

private noncomputable def leaf101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388649/8388608) }, vSqrt := { lower := (32767/32768), upper := (11453093205/11452678144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (13860489/8388608) }, upper := { exponent := 0, mantissa := (29/16) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (22905771349/22905356288) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf101InnerLog : WideLogData :=
  innerPair59Data

set_option maxRecDepth 1000000 in
private theorem leaf101LocalValidity :
    LeafFacts leaf101Box leaf101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (11453093205/11452678144) }) = true
      norm_num [leaf101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf101CertificateValid :
    WideCertificateValid leaf101Box leaf101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi20ValidityFacts
    leaf101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf101CoverageChecked :
    coverageCheck (innerAD leaf101Box) leaf101InnerLog = true := by
  rfl'

private theorem leaf101InnerLogValid :
    leaf101InnerLog.Valid 8 (innerAD leaf101Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint21PositiveFacts.valid leaf101CoverageChecked

private noncomputable def leaf101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf101InputLogOnePlusV_eq :
    leaf101InputLogOnePlusV = outerEnclosure 24
      (leaf101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf101RoundedFacts : LeafRoundedFacts 8
    leaf101Certificate.logOnePlusV leaf101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf101InputLogOnePlusV_eq }

private noncomputable def leaf101Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi20InputQChi innerPair59Input
    leaf101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf101LowerChecked :
    lowerCheck 24 leaf101Box leaf101Inputs = true := by
  rfl'

private theorem leaf101CoversExact : CoversExact 8
    leaf101Box leaf101Certificate leaf101InnerLog leaf101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi20RoundedFacts
    innerPair59RoundedFacts leaf101RoundedFacts (by rfl)

private theorem leaf101FlatSound : Sound leaf101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf101CertificateValid
    leaf101InnerLogValid leaf101CoversExact leaf101LowerChecked

private noncomputable def leaf102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388651/8388608) }, vSqrt := { lower := (32767/32768), upper := (6871855923/6871580672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (14319211/8388608) }, upper := { exponent := 0, mantissa := (15/8) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (13743436595/13743161344) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf102InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf102LocalValidity :
    LeafFacts leaf102Box leaf102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (6871855923/6871580672) }) = true
      norm_num [leaf102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf102CertificateValid :
    WideCertificateValid leaf102Box leaf102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi20ValidityFacts
    leaf102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf102CoverageChecked :
    coverageCheck (innerAD leaf102Box) leaf102InnerLog = true := by
  rfl'

private theorem leaf102InnerLogValid :
    leaf102InnerLog.Valid 8 (innerAD leaf102Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf102CoverageChecked

private noncomputable def leaf102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf102InputLogOnePlusV_eq :
    leaf102InputLogOnePlusV = outerEnclosure 24
      (leaf102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf102RoundedFacts : LeafRoundedFacts 8
    leaf102Certificate.logOnePlusV leaf102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf102InputLogOnePlusV_eq }

private noncomputable def leaf102Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi20InputQChi innerPair67Input
    leaf102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf102LowerChecked :
    lowerCheck 24 leaf102Box leaf102Inputs = true := by
  rfl'

private theorem leaf102CoversExact : CoversExact 8
    leaf102Box leaf102Certificate leaf102InnerLog leaf102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi20RoundedFacts
    innerPair67RoundedFacts leaf102RoundedFacts (by rfl)

private theorem leaf102FlatSound : Sound leaf102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf102CertificateValid
    leaf102InnerLogValid leaf102CoversExact leaf102LowerChecked

private noncomputable def leaf103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388651/8388608) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358018048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (13860487/8388608) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717297663/68716036096) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf103InnerLog : WideLogData :=
  innerPair60Data

set_option maxRecDepth 1000000 in
private theorem leaf103LocalValidity :
    LeafFacts leaf103Box leaf103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358018048) }) = true
      norm_num [leaf103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf103CertificateValid :
    WideCertificateValid leaf103Box leaf103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi19ValidityFacts
    leaf103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf103CoverageChecked :
    coverageCheck (innerAD leaf103Box) leaf103InnerLog = true := by
  rfl'

private theorem leaf103InnerLogValid :
    leaf103InnerLog.Valid 8 (innerAD leaf103Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint22PositiveFacts.valid leaf103CoverageChecked

private noncomputable def leaf103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf103InputLogOnePlusV_eq :
    leaf103InputLogOnePlusV = outerEnclosure 24
      (leaf103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf103RoundedFacts : LeafRoundedFacts 8
    leaf103Certificate.logOnePlusV leaf103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf103InputLogOnePlusV_eq }

private noncomputable def leaf103Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi19InputQChi innerPair60Input
    leaf103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf103LowerChecked :
    lowerCheck 24 leaf103Box leaf103Inputs = true := by
  rfl'

private theorem leaf103CoversExact : CoversExact 8
    leaf103Box leaf103Certificate leaf103InnerLog leaf103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi19RoundedFacts
    innerPair60RoundedFacts leaf103RoundedFacts (by rfl)

private theorem leaf103FlatSound : Sound leaf103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf103CertificateValid
    leaf103InnerLogValid leaf103CoversExact leaf103LowerChecked

private noncomputable def leaf104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (3/4), chiHi := (7/8) }

private noncomputable def leaf104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388653/8388608) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871580672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (14253677/8388608) }, upper := { exponent := 0, mantissa := (15/8) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi19LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743436595/13743161344) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf104InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf104LocalValidity :
    LeafFacts leaf104Box leaf104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871580672) }) = true
      norm_num [leaf104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf104CertificateValid :
    WideCertificateValid leaf104Box leaf104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi19ValidityFacts
    leaf104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf104CoverageChecked :
    coverageCheck (innerAD leaf104Box) leaf104InnerLog = true := by
  rfl'

private theorem leaf104InnerLogValid :
    leaf104InnerLog.Valid 8 (innerAD leaf104Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf104CoverageChecked

private noncomputable def leaf104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf104InputLogOnePlusV_eq :
    leaf104InputLogOnePlusV = outerEnclosure 24
      (leaf104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf104RoundedFacts : LeafRoundedFacts 8
    leaf104Certificate.logOnePlusV leaf104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf104InputLogOnePlusV_eq }

private noncomputable def leaf104Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi19InputQChi innerPair67Input
    leaf104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf104LowerChecked :
    lowerCheck 24 leaf104Box leaf104Inputs = true := by
  rfl'

private theorem leaf104CoversExact : CoversExact 8
    leaf104Box leaf104Certificate leaf104InnerLog leaf104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi19RoundedFacts
    innerPair67RoundedFacts leaf104RoundedFacts (by rfl)

private theorem leaf104FlatSound : Sound leaf104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf104CertificateValid
    leaf104InnerLogValid leaf104CoversExact leaf104LowerChecked

private noncomputable def leaf105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (8388653/8388608) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357772288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (14777933/8388608) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717051903/68715544576) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf105InnerLog : WideLogData :=
  innerPair73Data

set_option maxRecDepth 1000000 in
private theorem leaf105LocalValidity :
    LeafFacts leaf105Box leaf105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357772288) }) = true
      norm_num [leaf105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf105CertificateValid :
    WideCertificateValid leaf105Box leaf105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi20ValidityFacts
    leaf105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf105CoverageChecked :
    coverageCheck (innerAD leaf105Box) leaf105InnerLog = true := by
  rfl'

private theorem leaf105InnerLogValid :
    leaf105InnerLog.Valid 8 (innerAD leaf105Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint23PositiveFacts.valid leaf105CoverageChecked

private noncomputable def leaf105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf105InputLogOnePlusV_eq :
    leaf105InputLogOnePlusV = outerEnclosure 24
      (leaf105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf105RoundedFacts : LeafRoundedFacts 8
    leaf105Certificate.logOnePlusV leaf105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf105InputLogOnePlusV_eq }

private noncomputable def leaf105Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi20InputQChi innerPair73Input
    leaf105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf105LowerChecked :
    lowerCheck 24 leaf105Box leaf105Inputs = true := by
  rfl'

private theorem leaf105CoversExact : CoversExact 8
    leaf105Box leaf105Certificate leaf105InnerLog leaf105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi20RoundedFacts
    innerPair73RoundedFacts leaf105RoundedFacts (by rfl)

private theorem leaf105FlatSound : Sound leaf105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf105CertificateValid
    leaf105InnerLogValid leaf105CoversExact leaf105LowerChecked

private noncomputable def leaf106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (7/8), chiHi := (1) }

private noncomputable def leaf106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (8388655/8388608) }, vSqrt := { lower := (65533/65536), upper := (5726459221/5726273536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (15236655/8388608) }, upper := { exponent := 1, mantissa := (1) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi20LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (11452732757/11452547072) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf106InnerLog : WideLogData :=
  innerPair93Data

set_option maxRecDepth 1000000 in
private theorem leaf106LocalValidity :
    LeafFacts leaf106Box leaf106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (5726459221/5726273536) }) = true
      norm_num [leaf106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf106CertificateValid :
    WideCertificateValid leaf106Box leaf106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi20ValidityFacts
    leaf106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf106CoverageChecked :
    coverageCheck (innerAD leaf106Box) leaf106InnerLog = true := by
  rfl'

private theorem leaf106InnerLogValid :
    leaf106InnerLog.Valid 8 (innerAD leaf106Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint24PositiveFacts.valid leaf106CoverageChecked

private noncomputable def leaf106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf106InputLogOnePlusV_eq :
    leaf106InputLogOnePlusV = outerEnclosure 24
      (leaf106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf106RoundedFacts : LeafRoundedFacts 8
    leaf106Certificate.logOnePlusV leaf106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf106InputLogOnePlusV_eq }

private noncomputable def leaf106Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi20InputQChi innerPair93Input
    leaf106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf106LowerChecked :
    lowerCheck 24 leaf106Box leaf106Inputs = true := by
  rfl'

private theorem leaf106CoversExact : CoversExact 8
    leaf106Box leaf106Certificate leaf106InnerLog leaf106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi20RoundedFacts
    innerPair93RoundedFacts leaf106RoundedFacts (by rfl)

private theorem leaf106FlatSound : Sound leaf106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf106CertificateValid
    leaf106InnerLogValid leaf106CoversExact leaf106LowerChecked

private noncomputable def component2Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node0_sound : Sound component2Node0Box :=
  sound_of_literal_split component2Node0Box leaf71Box leaf72Box
    .k (9/16) (by rfl) (by rfl)
    leaf71FlatSound leaf72FlatSound

private noncomputable def component2Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node1_sound : Sound component2Node1Box :=
  sound_of_literal_split component2Node1Box leaf73Box leaf74Box
    .k (9/16) (by rfl) (by rfl)
    leaf73FlatSound leaf74FlatSound

private noncomputable def component2Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node2_sound : Sound component2Node2Box :=
  sound_of_literal_split component2Node2Box component2Node0Box component2Node1Box
    .chi (5/8) (by rfl) (by rfl)
    component2Node0_sound component2Node1_sound

private noncomputable def component2Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node3_sound : Sound component2Node3Box :=
  sound_of_literal_split component2Node3Box leaf75Box leaf76Box
    .k (11/16) (by rfl) (by rfl)
    leaf75FlatSound leaf76FlatSound

private noncomputable def component2Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node4_sound : Sound component2Node4Box :=
  sound_of_literal_split component2Node4Box leaf77Box leaf78Box
    .k (11/16) (by rfl) (by rfl)
    leaf77FlatSound leaf78FlatSound

private noncomputable def component2Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node5_sound : Sound component2Node5Box :=
  sound_of_literal_split component2Node5Box component2Node3Box component2Node4Box
    .chi (5/8) (by rfl) (by rfl)
    component2Node3_sound component2Node4_sound

private noncomputable def component2Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (3/4), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node6_sound : Sound component2Node6Box :=
  sound_of_literal_split component2Node6Box component2Node2Box component2Node5Box
    .k (5/8) (by rfl) (by rfl)
    component2Node2_sound component2Node5_sound

private noncomputable def component2Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node7_sound : Sound component2Node7Box :=
  sound_of_literal_split component2Node7Box leaf79Box leaf80Box
    .k (9/16) (by rfl) (by rfl)
    leaf79FlatSound leaf80FlatSound

private noncomputable def component2Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node8_sound : Sound component2Node8Box :=
  sound_of_literal_split component2Node8Box leaf81Box leaf82Box
    .k (9/16) (by rfl) (by rfl)
    leaf81FlatSound leaf82FlatSound

private noncomputable def component2Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node9_sound : Sound component2Node9Box :=
  sound_of_literal_split component2Node9Box component2Node7Box component2Node8Box
    .chi (7/8) (by rfl) (by rfl)
    component2Node7_sound component2Node8_sound

private noncomputable def component2Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node10_sound : Sound component2Node10Box :=
  sound_of_literal_split component2Node10Box leaf83Box leaf84Box
    .k (11/16) (by rfl) (by rfl)
    leaf83FlatSound leaf84FlatSound

private noncomputable def component2Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node11_sound : Sound component2Node11Box :=
  sound_of_literal_split component2Node11Box leaf85Box leaf86Box
    .k (11/16) (by rfl) (by rfl)
    leaf85FlatSound leaf86FlatSound

private noncomputable def component2Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node12_sound : Sound component2Node12Box :=
  sound_of_literal_split component2Node12Box component2Node10Box component2Node11Box
    .chi (7/8) (by rfl) (by rfl)
    component2Node10_sound component2Node11_sound

private noncomputable def component2Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (3/4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node13_sound : Sound component2Node13Box :=
  sound_of_literal_split component2Node13Box component2Node9Box component2Node12Box
    .k (5/8) (by rfl) (by rfl)
    component2Node9_sound component2Node12_sound

private noncomputable def component2Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (3/4), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node14_sound : Sound component2Node14Box :=
  sound_of_literal_split component2Node14Box component2Node6Box component2Node13Box
    .chi (3/4) (by rfl) (by rfl)
    component2Node6_sound component2Node13_sound

private noncomputable def component2Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node15_sound : Sound component2Node15Box :=
  sound_of_literal_split component2Node15Box leaf88Box leaf89Box
    .chi (9/16) (by rfl) (by rfl)
    leaf88FlatSound leaf89FlatSound

private noncomputable def component2Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node16_sound : Sound component2Node16Box :=
  sound_of_literal_split component2Node16Box leaf87Box component2Node15Box
    .k (13/16) (by rfl) (by rfl)
    leaf87FlatSound component2Node15_sound

private noncomputable def component2Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node17_sound : Sound component2Node17Box :=
  sound_of_literal_split component2Node17Box leaf90Box leaf91Box
    .k (13/16) (by rfl) (by rfl)
    leaf90FlatSound leaf91FlatSound

private noncomputable def component2Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node18_sound : Sound component2Node18Box :=
  sound_of_literal_split component2Node18Box component2Node16Box component2Node17Box
    .chi (5/8) (by rfl) (by rfl)
    component2Node16_sound component2Node17_sound

private noncomputable def component2Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component2Node19_sound : Sound component2Node19Box :=
  sound_of_literal_split component2Node19Box leaf92Box leaf93Box
    .k (15/16) (by rfl) (by rfl)
    leaf92FlatSound leaf93FlatSound

private noncomputable def component2Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node20_sound : Sound component2Node20Box :=
  sound_of_literal_split component2Node20Box leaf94Box leaf95Box
    .k (15/16) (by rfl) (by rfl)
    leaf94FlatSound leaf95FlatSound

private noncomputable def component2Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node21_sound : Sound component2Node21Box :=
  sound_of_literal_split component2Node21Box component2Node19Box component2Node20Box
    .chi (9/16) (by rfl) (by rfl)
    component2Node19_sound component2Node20_sound

private noncomputable def component2Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node22_sound : Sound component2Node22Box :=
  sound_of_literal_split component2Node22Box leaf97Box leaf98Box
    .chi (11/16) (by rfl) (by rfl)
    leaf97FlatSound leaf98FlatSound

private noncomputable def component2Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node23_sound : Sound component2Node23Box :=
  sound_of_literal_split component2Node23Box leaf96Box component2Node22Box
    .k (15/16) (by rfl) (by rfl)
    leaf96FlatSound component2Node22_sound

private noncomputable def component2Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node24_sound : Sound component2Node24Box :=
  sound_of_literal_split component2Node24Box component2Node21Box component2Node23Box
    .chi (5/8) (by rfl) (by rfl)
    component2Node21_sound component2Node23_sound

private noncomputable def component2Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component2Node25_sound : Sound component2Node25Box :=
  sound_of_literal_split component2Node25Box component2Node18Box component2Node24Box
    .k (7/8) (by rfl) (by rfl)
    component2Node18_sound component2Node24_sound

private noncomputable def component2Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node26_sound : Sound component2Node26Box :=
  sound_of_literal_split component2Node26Box leaf99Box leaf100Box
    .k (13/16) (by rfl) (by rfl)
    leaf99FlatSound leaf100FlatSound

private noncomputable def component2Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node27_sound : Sound component2Node27Box :=
  sound_of_literal_split component2Node27Box leaf101Box leaf102Box
    .k (13/16) (by rfl) (by rfl)
    leaf101FlatSound leaf102FlatSound

private noncomputable def component2Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node28_sound : Sound component2Node28Box :=
  sound_of_literal_split component2Node28Box component2Node26Box component2Node27Box
    .chi (7/8) (by rfl) (by rfl)
    component2Node26_sound component2Node27_sound

private noncomputable def component2Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component2Node29_sound : Sound component2Node29Box :=
  sound_of_literal_split component2Node29Box leaf103Box leaf104Box
    .k (15/16) (by rfl) (by rfl)
    leaf103FlatSound leaf104FlatSound

private noncomputable def component2Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node30_sound : Sound component2Node30Box :=
  sound_of_literal_split component2Node30Box leaf105Box leaf106Box
    .k (15/16) (by rfl) (by rfl)
    leaf105FlatSound leaf106FlatSound

private noncomputable def component2Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node31_sound : Sound component2Node31Box :=
  sound_of_literal_split component2Node31Box component2Node29Box component2Node30Box
    .chi (7/8) (by rfl) (by rfl)
    component2Node29_sound component2Node30_sound

private noncomputable def component2Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node32_sound : Sound component2Node32Box :=
  sound_of_literal_split component2Node32Box component2Node28Box component2Node31Box
    .k (7/8) (by rfl) (by rfl)
    component2Node28_sound component2Node31_sound

private noncomputable def component2Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component2Node33_sound : Sound component2Node33Box :=
  sound_of_literal_split component2Node33Box component2Node25Box component2Node32Box
    .chi (3/4) (by rfl) (by rfl)
    component2Node25_sound component2Node32_sound

noncomputable def component2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (1), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component2_sound : Sound component2Box :=
  sound_of_literal_split component2Box component2Node14Box component2Node33Box
    .k (3/4) (by rfl) (by rfl)
    component2Node14_sound component2Node33_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
