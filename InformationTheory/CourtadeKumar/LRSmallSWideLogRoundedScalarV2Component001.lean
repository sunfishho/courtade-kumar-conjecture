import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (0), chiHi := (1/8) }

private noncomputable def leaf21Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194315/4194304) }, vSqrt := { lower := (32767/32768), upper := (1048580/1048571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (4161527/2097152) }, upper := { exponent := 0, mantissa := (69/64) } }, logOuter := sk5LogOuterCertificate, logK := sk5LogKCertificate, logChi := chi1LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097151/2097142) } }, logDArg := sk5LogDArgCertificate }

private noncomputable def leaf21InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf21LocalValidity :
    LeafFacts leaf21Box leaf21Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf21Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048580/1048571) }) = true
      norm_num [leaf21Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf21CertificateValid :
    WideCertificateValid leaf21Box leaf21Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk5ValidityFacts chi1ValidityFacts
    leaf21LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf21CoverageChecked :
    coverageCheck (innerAD leaf21Box) leaf21InnerLog = true := by
  rfl'

private theorem leaf21InnerLogValid :
    leaf21InnerLog.Valid 8 (innerAD leaf21Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf21CoverageChecked

private noncomputable def leaf21InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf21InputLogOnePlusV_eq :
    leaf21InputLogOnePlusV = outerEnclosure 24
      (leaf21Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf21RoundedFacts : LeafRoundedFacts 8
    leaf21Certificate.logOnePlusV leaf21InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf21InputLogOnePlusV_eq }

private noncomputable def leaf21Inputs : Inputs :=
  inputsOfCaches globalInput sk5RoundedInputs
    chi1InputQChi innerPair0Input
    leaf21InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf21LowerChecked :
    lowerCheck 24 leaf21Box leaf21Inputs = true := by
  rfl'

private theorem leaf21CoversExact : CoversExact 8
    leaf21Box leaf21Certificate leaf21InnerLog leaf21Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk5RoundedFacts chi1RoundedFacts
    innerPair0RoundedFacts leaf21RoundedFacts (by rfl)

private theorem leaf21FlatSound : Sound leaf21Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf21CertificateValid
    leaf21InnerLogValid leaf21CoversExact leaf21LowerChecked

private noncomputable def leaf22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16), chiLo := (1/8), chiHi := (1/4) }

private noncomputable def leaf22Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388629/8388608) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (8880077/8388608) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk6LogOuterCertificate, logK := sk6LogKCertificate, logChi := chi2LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk6LogDArgCertificate }

private noncomputable def leaf22InnerLog : WideLogData :=
  innerPair11Data

set_option maxRecDepth 1000000 in
private theorem leaf22LocalValidity :
    LeafFacts leaf22Box leaf22Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf22Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048567) }) = true
      norm_num [leaf22Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf22CertificateValid :
    WideCertificateValid leaf22Box leaf22Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk6ValidityFacts chi2ValidityFacts
    leaf22LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf22CoverageChecked :
    coverageCheck (innerAD leaf22Box) leaf22InnerLog = true := by
  rfl'

private theorem leaf22InnerLogValid :
    leaf22InnerLog.Valid 8 (innerAD leaf22Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint4PositiveFacts.valid leaf22CoverageChecked

private noncomputable def leaf22InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf22InputLogOnePlusV_eq :
    leaf22InputLogOnePlusV = outerEnclosure 24
      (leaf22Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf22RoundedFacts : LeafRoundedFacts 8
    leaf22Certificate.logOnePlusV leaf22InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf22InputLogOnePlusV_eq }

private noncomputable def leaf22Inputs : Inputs :=
  inputsOfCaches globalInput sk6RoundedInputs
    chi2InputQChi innerPair11Input
    leaf22InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf22LowerChecked :
    lowerCheck 24 leaf22Box leaf22Inputs = true := by
  rfl'

private theorem leaf22CoversExact : CoversExact 8
    leaf22Box leaf22Certificate leaf22InnerLog leaf22Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk6RoundedFacts chi2RoundedFacts
    innerPair11RoundedFacts leaf22RoundedFacts (by rfl)

private theorem leaf22FlatSound : Sound leaf22Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf22CertificateValid
    leaf22InnerLogValid leaf22CoversExact leaf22LowerChecked

private noncomputable def leaf23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8), chiLo := (1/8), chiHi := (1/4) }

private noncomputable def leaf23Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388631/8388608) }, vSqrt := { lower := (32767/32768), upper := (174763/174761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (8945607/8388608) }, upper := { exponent := 0, mantissa := (37/32) } }, logOuter := sk7LogOuterCertificate, logK := sk7LogKCertificate, logChi := chi2LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (174762/174761) } }, logDArg := sk7LogDArgCertificate }

private noncomputable def leaf23InnerLog : WideLogData :=
  innerPair8Data

set_option maxRecDepth 1000000 in
private theorem leaf23LocalValidity :
    LeafFacts leaf23Box leaf23Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf23Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (174763/174761) }) = true
      norm_num [leaf23Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf23CertificateValid :
    WideCertificateValid leaf23Box leaf23Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk7ValidityFacts chi2ValidityFacts
    leaf23LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf23CoverageChecked :
    coverageCheck (innerAD leaf23Box) leaf23InnerLog = true := by
  rfl'

private theorem leaf23InnerLogValid :
    leaf23InnerLog.Valid 8 (innerAD leaf23Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint12PositiveFacts.valid leaf23CoverageChecked

private noncomputable def leaf23InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629177/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf23InputLogOnePlusV_eq :
    leaf23InputLogOnePlusV = outerEnclosure 24
      (leaf23Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf23RoundedFacts : LeafRoundedFacts 8
    leaf23Certificate.logOnePlusV leaf23InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf23InputLogOnePlusV_eq }

private noncomputable def leaf23Inputs : Inputs :=
  inputsOfCaches globalInput sk7RoundedInputs
    chi2InputQChi innerPair8Input
    leaf23InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf23LowerChecked :
    lowerCheck 24 leaf23Box leaf23Inputs = true := by
  rfl'

private theorem leaf23CoversExact : CoversExact 8
    leaf23Box leaf23Certificate leaf23InnerLog leaf23Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk7RoundedFacts chi2RoundedFacts
    innerPair8RoundedFacts leaf23RoundedFacts (by rfl)

private theorem leaf23FlatSound : Sound leaf23Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf23CertificateValid
    leaf23InnerLogValid leaf23CoversExact leaf23LowerChecked

private noncomputable def leaf24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (0), chiHi := (1/8) }

private noncomputable def leaf24Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (4194317/4194304) }, vSqrt := { lower := (32767/32768), upper := (104858/104857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (4161525/2097152) }, upper := { exponent := 0, mantissa := (35/32) } }, logOuter := sk8LogOuterCertificate, logK := sk8LogKCertificate, logChi := chi1LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (209715/209714) } }, logDArg := sk8LogDArgCertificate }

private noncomputable def leaf24InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf24LocalValidity :
    LeafFacts leaf24Box leaf24Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf24Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (104858/104857) }) = true
      norm_num [leaf24Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf24CertificateValid :
    WideCertificateValid leaf24Box leaf24Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk8ValidityFacts chi1ValidityFacts
    leaf24LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf24CoverageChecked :
    coverageCheck (innerAD leaf24Box) leaf24InnerLog = true := by
  rfl'

private theorem leaf24InnerLogValid :
    leaf24InnerLog.Valid 8 (innerAD leaf24Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf24CoverageChecked

private noncomputable def leaf24InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf24InputLogOnePlusV_eq :
    leaf24InputLogOnePlusV = outerEnclosure 24
      (leaf24Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf24RoundedFacts : LeafRoundedFacts 8
    leaf24Certificate.logOnePlusV leaf24InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf24InputLogOnePlusV_eq }

private noncomputable def leaf24Inputs : Inputs :=
  inputsOfCaches globalInput sk8RoundedInputs
    chi1InputQChi innerPair0Input
    leaf24InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf24LowerChecked :
    lowerCheck 24 leaf24Box leaf24Inputs = true := by
  rfl'

private theorem leaf24CoversExact : CoversExact 8
    leaf24Box leaf24Certificate leaf24InnerLog leaf24Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk8RoundedFacts chi1RoundedFacts
    innerPair0RoundedFacts leaf24RoundedFacts (by rfl)

private theorem leaf24FlatSound : Sound leaf24Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf24CertificateValid
    leaf24InnerLogValid leaf24CoversExact leaf24LowerChecked

private noncomputable def leaf25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (1/8), chiHi := (3/16) }

private noncomputable def leaf25Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777243/16777216) }, vSqrt := { lower := (32767/32768), upper := (4194312/4194271) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18055063/16777216) }, upper := { exponent := 0, mantissa := (289/256) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi10LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (8388583/8388542) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf25InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf25LocalValidity :
    LeafFacts leaf25Box leaf25Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf25Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (4194312/4194271) }) = true
      norm_num [leaf25Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf25CertificateValid :
    WideCertificateValid leaf25Box leaf25Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi10ValidityFacts
    leaf25LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf25CoverageChecked :
    coverageCheck (innerAD leaf25Box) leaf25InnerLog = true := by
  rfl'

private theorem leaf25InnerLogValid :
    leaf25InnerLog.Valid 8 (innerAD leaf25Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf25CoverageChecked

private noncomputable def leaf25InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf25InputLogOnePlusV_eq :
    leaf25InputLogOnePlusV = outerEnclosure 24
      (leaf25Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf25RoundedFacts : LeafRoundedFacts 8
    leaf25Certificate.logOnePlusV leaf25InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf25InputLogOnePlusV_eq }

private noncomputable def leaf25Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi10InputQChi innerPair6Input
    leaf25InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf25LowerChecked :
    lowerCheck 24 leaf25Box leaf25Inputs = true := by
  rfl'

private theorem leaf25CoversExact : CoversExact 8
    leaf25Box leaf25Certificate leaf25InnerLog leaf25Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi10RoundedFacts
    innerPair6RoundedFacts leaf25RoundedFacts (by rfl)

private theorem leaf25FlatSound : Sound leaf25Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf25CertificateValid
    leaf25InnerLogValid leaf25CoversExact leaf25LowerChecked

private noncomputable def leaf26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (1/8), chiHi := (3/16) }

private noncomputable def leaf26Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777245/16777216) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18186125/16777216) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi10LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf26InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf26LocalValidity :
    LeafFacts leaf26Box leaf26Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf26Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048567) }) = true
      norm_num [leaf26Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf26CertificateValid :
    WideCertificateValid leaf26Box leaf26Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi10ValidityFacts
    leaf26LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf26CoverageChecked :
    coverageCheck (innerAD leaf26Box) leaf26InnerLog = true := by
  rfl'

private theorem leaf26InnerLogValid :
    leaf26InnerLog.Valid 8 (innerAD leaf26Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf26CoverageChecked

private noncomputable def leaf26InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf26InputLogOnePlusV_eq :
    leaf26InputLogOnePlusV = outerEnclosure 24
      (leaf26Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf26RoundedFacts : LeafRoundedFacts 8
    leaf26Certificate.logOnePlusV leaf26InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf26InputLogOnePlusV_eq }

private noncomputable def leaf26Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi10InputQChi innerPair6Input
    leaf26InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf26LowerChecked :
    lowerCheck 24 leaf26Box leaf26Inputs = true := by
  rfl'

private theorem leaf26CoversExact : CoversExact 8
    leaf26Box leaf26Certificate leaf26InnerLog leaf26Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi10RoundedFacts
    innerPair6RoundedFacts leaf26RoundedFacts (by rfl)

private theorem leaf26FlatSound : Sound leaf26Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf26CertificateValid
    leaf26InnerLogValid leaf26CoversExact leaf26LowerChecked

private noncomputable def leaf27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (3/16), chiHi := (1/4) }

private noncomputable def leaf27Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777245/16777216) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048565) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18710381/16777216) }, upper := { exponent := 0, mantissa := (75/64) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi11LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097143/2097130) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf27InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf27LocalValidity :
    LeafFacts leaf27Box leaf27Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf27Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048565) }) = true
      norm_num [leaf27Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf27CertificateValid :
    WideCertificateValid leaf27Box leaf27Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi11ValidityFacts
    leaf27LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf27CoverageChecked :
    coverageCheck (innerAD leaf27Box) leaf27InnerLog = true := by
  rfl'

private theorem leaf27InnerLogValid :
    leaf27InnerLog.Valid 8 (innerAD leaf27Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf27CoverageChecked

private noncomputable def leaf27InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf27InputLogOnePlusV_eq :
    leaf27InputLogOnePlusV = outerEnclosure 24
      (leaf27Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf27RoundedFacts : LeafRoundedFacts 8
    leaf27Certificate.logOnePlusV leaf27InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf27InputLogOnePlusV_eq }

private noncomputable def leaf27Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi11InputQChi innerPair6Input
    leaf27InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf27LowerChecked :
    lowerCheck 24 leaf27Box leaf27Inputs = true := by
  rfl'

private theorem leaf27CoversExact : CoversExact 8
    leaf27Box leaf27Certificate leaf27InnerLog leaf27Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi11RoundedFacts
    innerPair6RoundedFacts leaf27RoundedFacts (by rfl)

private theorem leaf27FlatSound : Sound leaf27Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf27CertificateValid
    leaf27InnerLogValid leaf27CoversExact leaf27LowerChecked

private noncomputable def leaf28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (3/16), chiHi := (1/4) }

private noncomputable def leaf28Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777247/16777216) }, vSqrt := { lower := (32767/32768), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18906975/16777216) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi11LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf28InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf28LocalValidity :
    LeafFacts leaf28Box leaf28Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf28Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524282) }) = true
      norm_num [leaf28Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf28CertificateValid :
    WideCertificateValid leaf28Box leaf28Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi11ValidityFacts
    leaf28LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf28CoverageChecked :
    coverageCheck (innerAD leaf28Box) leaf28InnerLog = true := by
  rfl'

private theorem leaf28InnerLogValid :
    leaf28InnerLog.Valid 8 (innerAD leaf28Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf28CoverageChecked

private noncomputable def leaf28InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf28InputLogOnePlusV_eq :
    leaf28InputLogOnePlusV = outerEnclosure 24
      (leaf28Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf28RoundedFacts : LeafRoundedFacts 8
    leaf28Certificate.logOnePlusV leaf28InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf28InputLogOnePlusV_eq }

private noncomputable def leaf28Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi11InputQChi innerPair2Input
    leaf28InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf28LowerChecked :
    lowerCheck 24 leaf28Box leaf28Inputs = true := by
  rfl'

private theorem leaf28CoversExact : CoversExact 8
    leaf28Box leaf28Certificate leaf28InnerLog leaf28Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi11RoundedFacts
    innerPair2RoundedFacts leaf28RoundedFacts (by rfl)

private theorem leaf28FlatSound : Sound leaf28Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf28CertificateValid
    leaf28InnerLogValid leaf28CoversExact leaf28LowerChecked

private noncomputable def leaf29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (0), chiHi := (1/16) }

private noncomputable def leaf29Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388623/8388608) }, vSqrt := { lower := (32767/32768), upper := (419432/419429) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (8355827/4194304) }, upper := { exponent := 0, mantissa := (135/128) } }, logOuter := sk11LogOuterCertificate, logK := sk11LogKCertificate, logChi := chi12LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (838861/838858) } }, logDArg := sk11LogDArgCertificate }

private noncomputable def leaf29InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf29LocalValidity :
    LeafFacts leaf29Box leaf29Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf29Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (419432/419429) }) = true
      norm_num [leaf29Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf29CertificateValid :
    WideCertificateValid leaf29Box leaf29Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk11ValidityFacts chi12ValidityFacts
    leaf29LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf29CoverageChecked :
    coverageCheck (innerAD leaf29Box) leaf29InnerLog = true := by
  rfl'

private theorem leaf29InnerLogValid :
    leaf29InnerLog.Valid 8 (innerAD leaf29Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf29CoverageChecked

private noncomputable def leaf29InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629141/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf29InputLogOnePlusV_eq :
    leaf29InputLogOnePlusV = outerEnclosure 24
      (leaf29Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf29RoundedFacts : LeafRoundedFacts 8
    leaf29Certificate.logOnePlusV leaf29InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf29InputLogOnePlusV_eq }

private noncomputable def leaf29Inputs : Inputs :=
  inputsOfCaches globalInput sk11RoundedInputs
    chi12InputQChi innerPair1Input
    leaf29InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf29LowerChecked :
    lowerCheck 24 leaf29Box leaf29Inputs = true := by
  rfl'

private theorem leaf29CoversExact : CoversExact 8
    leaf29Box leaf29Certificate leaf29InnerLog leaf29Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk11RoundedFacts chi12RoundedFacts
    innerPair1RoundedFacts leaf29RoundedFacts (by rfl)

private theorem leaf29FlatSound : Sound leaf29Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf29CertificateValid
    leaf29InnerLogValid leaf29CoversExact leaf29LowerChecked

private noncomputable def leaf30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf30Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777235/16777216) }, vSqrt := { lower := (32767/32768), upper := (113360/113359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (17530815/16777216) }, upper := { exponent := 0, mantissa := (277/256) } }, logOuter := sk11LogOuterCertificate, logK := sk11LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (226719/226718) } }, logDArg := sk11LogDArgCertificate }

private noncomputable def leaf30InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf30LocalValidity :
    LeafFacts leaf30Box leaf30Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf30Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (113360/113359) }) = true
      norm_num [leaf30Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf30CertificateValid :
    WideCertificateValid leaf30Box leaf30Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk11ValidityFacts chi13ValidityFacts
    leaf30LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf30CoverageChecked :
    coverageCheck (innerAD leaf30Box) leaf30InnerLog = true := by
  rfl'

private theorem leaf30InnerLogValid :
    leaf30InnerLog.Valid 8 (innerAD leaf30Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf30CoverageChecked

private noncomputable def leaf30InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf30InputLogOnePlusV_eq :
    leaf30InputLogOnePlusV = outerEnclosure 24
      (leaf30Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf30RoundedFacts : LeafRoundedFacts 8
    leaf30Certificate.logOnePlusV leaf30InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf30InputLogOnePlusV_eq }

private noncomputable def leaf30Inputs : Inputs :=
  inputsOfCaches globalInput sk11RoundedInputs
    chi13InputQChi innerPair9Input
    leaf30InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf30LowerChecked :
    lowerCheck 24 leaf30Box leaf30Inputs = true := by
  rfl'

private theorem leaf30CoversExact : CoversExact 8
    leaf30Box leaf30Certificate leaf30InnerLog leaf30Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk11RoundedFacts chi13RoundedFacts
    innerPair9RoundedFacts leaf30RoundedFacts (by rfl)

private theorem leaf30FlatSound : Sound leaf30Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf30CertificateValid
    leaf30InnerLogValid leaf30CoversExact leaf30LowerChecked

private noncomputable def leaf31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf31Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777237/16777216) }, vSqrt := { lower := (32767/32768), upper := (1048580/1048569) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (17924005/16777216) }, upper := { exponent := 0, mantissa := (71/64) } }, logOuter := sk11LogOuterCertificate, logK := sk11LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097149/2097138) } }, logDArg := sk11LogDArgCertificate }

private noncomputable def leaf31InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf31LocalValidity :
    LeafFacts leaf31Box leaf31Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf31Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048580/1048569) }) = true
      norm_num [leaf31Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf31CertificateValid :
    WideCertificateValid leaf31Box leaf31Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk11ValidityFacts chi14ValidityFacts
    leaf31LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf31CoverageChecked :
    coverageCheck (innerAD leaf31Box) leaf31InnerLog = true := by
  rfl'

private theorem leaf31InnerLogValid :
    leaf31InnerLog.Valid 8 (innerAD leaf31Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf31CoverageChecked

private noncomputable def leaf31InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf31InputLogOnePlusV_eq :
    leaf31InputLogOnePlusV = outerEnclosure 24
      (leaf31Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf31RoundedFacts : LeafRoundedFacts 8
    leaf31Certificate.logOnePlusV leaf31InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf31InputLogOnePlusV_eq }

private noncomputable def leaf31Inputs : Inputs :=
  inputsOfCaches globalInput sk11RoundedInputs
    chi14InputQChi innerPair5Input
    leaf31InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf31LowerChecked :
    lowerCheck 24 leaf31Box leaf31Inputs = true := by
  rfl'

private theorem leaf31CoversExact : CoversExact 8
    leaf31Box leaf31Certificate leaf31InnerLog leaf31Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk11RoundedFacts chi14RoundedFacts
    innerPair5RoundedFacts leaf31RoundedFacts (by rfl)

private theorem leaf31FlatSound : Sound leaf31Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf31CertificateValid
    leaf31InnerLogValid leaf31CoversExact leaf31LowerChecked

private noncomputable def leaf32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (0), chiHi := (1/16) }

private noncomputable def leaf32Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388625/8388608) }, vSqrt := { lower := (65533/65536), upper := (262145/262143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (8355825/4194304) }, upper := { exponent := 0, mantissa := (17/16) } }, logOuter := sk12LogOuterCertificate, logK := sk12LogKCertificate, logChi := chi12LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (262144/262143) } }, logDArg := sk12LogDArgCertificate }

private noncomputable def leaf32InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf32LocalValidity :
    LeafFacts leaf32Box leaf32Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf32Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (262145/262143) }) = true
      norm_num [leaf32Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf32CertificateValid :
    WideCertificateValid leaf32Box leaf32Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk12ValidityFacts chi12ValidityFacts
    leaf32LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf32CoverageChecked :
    coverageCheck (innerAD leaf32Box) leaf32InnerLog = true := by
  rfl'

private theorem leaf32InnerLogValid :
    leaf32InnerLog.Valid 8 (innerAD leaf32Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf32CoverageChecked

private noncomputable def leaf32InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629145/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf32InputLogOnePlusV_eq :
    leaf32InputLogOnePlusV = outerEnclosure 24
      (leaf32Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf32RoundedFacts : LeafRoundedFacts 8
    leaf32Certificate.logOnePlusV leaf32InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf32InputLogOnePlusV_eq }

private noncomputable def leaf32Inputs : Inputs :=
  inputsOfCaches globalInput sk12RoundedInputs
    chi12InputQChi innerPair1Input
    leaf32InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf32LowerChecked :
    lowerCheck 24 leaf32Box leaf32Inputs = true := by
  rfl'

private theorem leaf32CoversExact : CoversExact 8
    leaf32Box leaf32Certificate leaf32InnerLog leaf32Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk12RoundedFacts chi12RoundedFacts
    innerPair1RoundedFacts leaf32RoundedFacts (by rfl)

private theorem leaf32FlatSound : Sound leaf32Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf32CertificateValid
    leaf32InnerLogValid leaf32CoversExact leaf32LowerChecked

private noncomputable def leaf33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/16), chiHi := (3/32) }

private noncomputable def leaf33Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777237/16777216) }, vSqrt := { lower := (65533/65536), upper := (104858/104857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (17661877/16777216) }, upper := { exponent := 0, mantissa := (35/32) } }, logOuter := sk12LogOuterCertificate, logK := sk12LogKCertificate, logChi := chi13LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (209715/209714) } }, logDArg := sk12LogDArgCertificate }

private noncomputable def leaf33InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf33LocalValidity :
    LeafFacts leaf33Box leaf33Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf33Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (104858/104857) }) = true
      norm_num [leaf33Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf33CertificateValid :
    WideCertificateValid leaf33Box leaf33Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk12ValidityFacts chi13ValidityFacts
    leaf33LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf33CoverageChecked :
    coverageCheck (innerAD leaf33Box) leaf33InnerLog = true := by
  rfl'

private theorem leaf33InnerLogValid :
    leaf33InnerLog.Valid 8 (innerAD leaf33Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf33CoverageChecked

private noncomputable def leaf33InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf33InputLogOnePlusV_eq :
    leaf33InputLogOnePlusV = outerEnclosure 24
      (leaf33Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf33RoundedFacts : LeafRoundedFacts 8
    leaf33Certificate.logOnePlusV leaf33InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf33InputLogOnePlusV_eq }

private noncomputable def leaf33Inputs : Inputs :=
  inputsOfCaches globalInput sk12RoundedInputs
    chi13InputQChi innerPair9Input
    leaf33InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf33LowerChecked :
    lowerCheck 24 leaf33Box leaf33Inputs = true := by
  rfl'

private theorem leaf33CoversExact : CoversExact 8
    leaf33Box leaf33Certificate leaf33InnerLog leaf33Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk12RoundedFacts chi13RoundedFacts
    innerPair9RoundedFacts leaf33RoundedFacts (by rfl)

private theorem leaf33FlatSound : Sound leaf33Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf33CertificateValid
    leaf33InnerLogValid leaf33CoversExact leaf33LowerChecked

private noncomputable def leaf34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf34Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554469/33554432) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36273973/33554432) }, upper := { exponent := 0, mantissa := (143/128) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194293/4194274) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf34InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf34LocalValidity :
    LeafFacts leaf34Box leaf34Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf34Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097137) }) = true
      norm_num [leaf34Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf34CertificateValid :
    WideCertificateValid leaf34Box leaf34Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi14ValidityFacts
    leaf34LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf34CoverageChecked :
    coverageCheck (innerAD leaf34Box) leaf34InnerLog = true := by
  rfl'

private theorem leaf34InnerLogValid :
    leaf34InnerLog.Valid 8 (innerAD leaf34Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf34CoverageChecked

private noncomputable def leaf34InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf34InputLogOnePlusV_eq :
    leaf34InputLogOnePlusV = outerEnclosure 24
      (leaf34Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf34RoundedFacts : LeafRoundedFacts 8
    leaf34Certificate.logOnePlusV leaf34InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf34InputLogOnePlusV_eq }

private noncomputable def leaf34Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi14InputQChi innerPair5Input
    leaf34InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf34LowerChecked :
    lowerCheck 24 leaf34Box leaf34Inputs = true := by
  rfl'

private theorem leaf34CoversExact : CoversExact 8
    leaf34Box leaf34Certificate leaf34InnerLog leaf34Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi14RoundedFacts
    innerPair5RoundedFacts leaf34RoundedFacts (by rfl)

private theorem leaf34FlatSound : Sound leaf34Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf34CertificateValid
    leaf34InnerLogValid leaf34CoversExact leaf34LowerChecked

private noncomputable def leaf35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf35Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554471/33554432) }, vSqrt := { lower := (65533/65536), upper := (524289/524284) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (36470567/33554432) }, upper := { exponent := 0, mantissa := (9/8) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1048573/1048568) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf35InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf35LocalValidity :
    LeafFacts leaf35Box leaf35Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf35Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (524289/524284) }) = true
      norm_num [leaf35Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf35CertificateValid :
    WideCertificateValid leaf35Box leaf35Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi14ValidityFacts
    leaf35LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf35CoverageChecked :
    coverageCheck (innerAD leaf35Box) leaf35InnerLog = true := by
  rfl'

private theorem leaf35InnerLogValid :
    leaf35InnerLog.Valid 8 (innerAD leaf35Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf35CoverageChecked

private noncomputable def leaf35InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf35InputLogOnePlusV_eq :
    leaf35InputLogOnePlusV = outerEnclosure 24
      (leaf35Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf35RoundedFacts : LeafRoundedFacts 8
    leaf35Certificate.logOnePlusV leaf35InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf35InputLogOnePlusV_eq }

private noncomputable def leaf35Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi14InputQChi innerPair5Input
    leaf35InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf35LowerChecked :
    lowerCheck 24 leaf35Box leaf35Inputs = true := by
  rfl'

private theorem leaf35CoversExact : CoversExact 8
    leaf35Box leaf35Certificate leaf35InnerLog leaf35Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi14RoundedFacts
    innerPair5RoundedFacts leaf35RoundedFacts (by rfl)

private theorem leaf35FlatSound : Sound leaf35Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf35CertificateValid
    leaf35InnerLogValid leaf35CoversExact leaf35LowerChecked

private noncomputable def leaf36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (1/8), chiHi := (3/16) }

private noncomputable def leaf36Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777247/16777216) }, vSqrt := { lower := (32767/32768), upper := (4194312/4194265) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18317187/16777216) }, upper := { exponent := 0, mantissa := (295/256) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi10LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (8388577/8388530) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf36InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf36LocalValidity :
    LeafFacts leaf36Box leaf36Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf36Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (4194312/4194265) }) = true
      norm_num [leaf36Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf36CertificateValid :
    WideCertificateValid leaf36Box leaf36Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi10ValidityFacts
    leaf36LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf36CoverageChecked :
    coverageCheck (innerAD leaf36Box) leaf36InnerLog = true := by
  rfl'

private theorem leaf36InnerLogValid :
    leaf36InnerLog.Valid 8 (innerAD leaf36Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf36CoverageChecked

private noncomputable def leaf36InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629175/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf36InputLogOnePlusV_eq :
    leaf36InputLogOnePlusV = outerEnclosure 24
      (leaf36Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf36RoundedFacts : LeafRoundedFacts 8
    leaf36Certificate.logOnePlusV leaf36InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf36InputLogOnePlusV_eq }

private noncomputable def leaf36Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi10InputQChi innerPair6Input
    leaf36InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf36LowerChecked :
    lowerCheck 24 leaf36Box leaf36Inputs = true := by
  rfl'

private theorem leaf36CoversExact : CoversExact 8
    leaf36Box leaf36Certificate leaf36InnerLog leaf36Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi10RoundedFacts
    innerPair6RoundedFacts leaf36RoundedFacts (by rfl)

private theorem leaf36FlatSound : Sound leaf36Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf36CertificateValid
    leaf36InnerLogValid leaf36CoversExact leaf36LowerChecked

private noncomputable def leaf37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (1/8), chiHi := (3/16) }

private noncomputable def leaf37Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777249/16777216) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18448249/16777216) }, upper := { exponent := 0, mantissa := (149/128) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi10LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194287/4194262) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf37InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf37LocalValidity :
    LeafFacts leaf37Box leaf37Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf37Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097131) }) = true
      norm_num [leaf37Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf37CertificateValid :
    WideCertificateValid leaf37Box leaf37Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi10ValidityFacts
    leaf37LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf37CoverageChecked :
    coverageCheck (innerAD leaf37Box) leaf37InnerLog = true := by
  rfl'

private theorem leaf37InnerLogValid :
    leaf37InnerLog.Valid 8 (innerAD leaf37Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf37CoverageChecked

private noncomputable def leaf37InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf37InputLogOnePlusV_eq :
    leaf37InputLogOnePlusV = outerEnclosure 24
      (leaf37Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf37RoundedFacts : LeafRoundedFacts 8
    leaf37Certificate.logOnePlusV leaf37InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf37InputLogOnePlusV_eq }

private noncomputable def leaf37Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi10InputQChi innerPair6Input
    leaf37InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf37LowerChecked :
    lowerCheck 24 leaf37Box leaf37Inputs = true := by
  rfl'

private theorem leaf37CoversExact : CoversExact 8
    leaf37Box leaf37Certificate leaf37InnerLog leaf37Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi10RoundedFacts
    innerPair6RoundedFacts leaf37RoundedFacts (by rfl)

private theorem leaf37FlatSound : Sound leaf37Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf37CertificateValid
    leaf37InnerLogValid leaf37CoversExact leaf37LowerChecked

private noncomputable def leaf38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (3/16), chiHi := (1/4) }

private noncomputable def leaf38Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777249/16777216) }, vSqrt := { lower := (32767/32768), upper := (349526/349521) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (19103569/16777216) }, upper := { exponent := 0, mantissa := (77/64) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi11LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (699047/699042) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf38InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf38LocalValidity :
    LeafFacts leaf38Box leaf38Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf38Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (349526/349521) }) = true
      norm_num [leaf38Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf38CertificateValid :
    WideCertificateValid leaf38Box leaf38Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi11ValidityFacts
    leaf38LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf38CoverageChecked :
    coverageCheck (innerAD leaf38Box) leaf38InnerLog = true := by
  rfl'

private theorem leaf38InnerLogValid :
    leaf38InnerLog.Valid 8 (innerAD leaf38Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf38CoverageChecked

private noncomputable def leaf38InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629201/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf38InputLogOnePlusV_eq :
    leaf38InputLogOnePlusV = outerEnclosure 24
      (leaf38Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf38RoundedFacts : LeafRoundedFacts 8
    leaf38Certificate.logOnePlusV leaf38InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf38InputLogOnePlusV_eq }

private noncomputable def leaf38Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi11InputQChi innerPair3Input
    leaf38InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf38LowerChecked :
    lowerCheck 24 leaf38Box leaf38Inputs = true := by
  rfl'

private theorem leaf38CoversExact : CoversExact 8
    leaf38Box leaf38Certificate leaf38InnerLog leaf38Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi11RoundedFacts
    innerPair3RoundedFacts leaf38RoundedFacts (by rfl)

private theorem leaf38FlatSound : Sound leaf38Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf38CertificateValid
    leaf38InnerLogValid leaf38CoversExact leaf38LowerChecked

private noncomputable def leaf39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (3/16), chiHi := (1/4) }

private noncomputable def leaf39Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777251/16777216) }, vSqrt := { lower := (32767/32768), upper := (524289/524281) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (19300163/16777216) }, upper := { exponent := 0, mantissa := (39/32) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi11LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (524285/524281) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf39InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf39LocalValidity :
    LeafFacts leaf39Box leaf39Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf39Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524281) }) = true
      norm_num [leaf39Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf39CertificateValid :
    WideCertificateValid leaf39Box leaf39Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi11ValidityFacts
    leaf39LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf39CoverageChecked :
    coverageCheck (innerAD leaf39Box) leaf39InnerLog = true := by
  rfl'

private theorem leaf39InnerLogValid :
    leaf39InnerLog.Valid 8 (innerAD leaf39Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf39CoverageChecked

private noncomputable def leaf39InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf39InputLogOnePlusV_eq :
    leaf39InputLogOnePlusV = outerEnclosure 24
      (leaf39Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf39RoundedFacts : LeafRoundedFacts 8
    leaf39Certificate.logOnePlusV leaf39InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf39InputLogOnePlusV_eq }

private noncomputable def leaf39Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi11InputQChi innerPair3Input
    leaf39InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf39LowerChecked :
    lowerCheck 24 leaf39Box leaf39Inputs = true := by
  rfl'

private theorem leaf39CoversExact : CoversExact 8
    leaf39Box leaf39Certificate leaf39InnerLog leaf39Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi11RoundedFacts
    innerPair3RoundedFacts leaf39RoundedFacts (by rfl)

private theorem leaf39FlatSound : Sound leaf39Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf39CertificateValid
    leaf39InnerLogValid leaf39CoversExact leaf39LowerChecked

private noncomputable def leaf40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (1/8), chiHi := (3/16) }

private noncomputable def leaf40Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777251/16777216) }, vSqrt := { lower := (32767/32768), upper := (4194312/4194259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18579311/16777216) }, upper := { exponent := 0, mantissa := (301/256) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi10LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (8388571/8388518) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf40InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf40LocalValidity :
    LeafFacts leaf40Box leaf40Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf40Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (4194312/4194259) }) = true
      norm_num [leaf40Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf40CertificateValid :
    WideCertificateValid leaf40Box leaf40Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi10ValidityFacts
    leaf40LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf40CoverageChecked :
    coverageCheck (innerAD leaf40Box) leaf40InnerLog = true := by
  rfl'

private theorem leaf40InnerLogValid :
    leaf40InnerLog.Valid 8 (innerAD leaf40Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf40CoverageChecked

private noncomputable def leaf40InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629187/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf40InputLogOnePlusV_eq :
    leaf40InputLogOnePlusV = outerEnclosure 24
      (leaf40Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf40RoundedFacts : LeafRoundedFacts 8
    leaf40Certificate.logOnePlusV leaf40InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf40InputLogOnePlusV_eq }

private noncomputable def leaf40Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi10InputQChi innerPair6Input
    leaf40InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf40LowerChecked :
    lowerCheck 24 leaf40Box leaf40Inputs = true := by
  rfl'

private theorem leaf40CoversExact : CoversExact 8
    leaf40Box leaf40Certificate leaf40InnerLog leaf40Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi10RoundedFacts
    innerPair6RoundedFacts leaf40RoundedFacts (by rfl)

private theorem leaf40FlatSound : Sound leaf40Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf40CertificateValid
    leaf40InnerLogValid leaf40CoversExact leaf40LowerChecked

private noncomputable def leaf41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (1/8), chiHi := (3/16) }

private noncomputable def leaf41Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777253/16777216) }, vSqrt := { lower := (65533/65536), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (18710373/16777216) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi10LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf41InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf41LocalValidity :
    LeafFacts leaf41Box leaf41Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf41Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (524289/524282) }) = true
      norm_num [leaf41Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf41CertificateValid :
    WideCertificateValid leaf41Box leaf41Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi10ValidityFacts
    leaf41LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf41CoverageChecked :
    coverageCheck (innerAD leaf41Box) leaf41InnerLog = true := by
  rfl'

private theorem leaf41InnerLogValid :
    leaf41InnerLog.Valid 8 (innerAD leaf41Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf41CoverageChecked

private noncomputable def leaf41InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf41InputLogOnePlusV_eq :
    leaf41InputLogOnePlusV = outerEnclosure 24
      (leaf41Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf41RoundedFacts : LeafRoundedFacts 8
    leaf41Certificate.logOnePlusV leaf41InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf41InputLogOnePlusV_eq }

private noncomputable def leaf41Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi10InputQChi innerPair6Input
    leaf41InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf41LowerChecked :
    lowerCheck 24 leaf41Box leaf41Inputs = true := by
  rfl'

private theorem leaf41CoversExact : CoversExact 8
    leaf41Box leaf41Certificate leaf41InnerLog leaf41Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi10RoundedFacts
    innerPair6RoundedFacts leaf41RoundedFacts (by rfl)

private theorem leaf41FlatSound : Sound leaf41Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf41CertificateValid
    leaf41InnerLogValid leaf41CoversExact leaf41LowerChecked

private noncomputable def leaf42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (3/16), chiHi := (1/4) }

private noncomputable def leaf42Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777253/16777216) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (19496757/16777216) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi11LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf42InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf42LocalValidity :
    LeafFacts leaf42Box leaf42Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf42Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048561) }) = true
      norm_num [leaf42Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf42CertificateValid :
    WideCertificateValid leaf42Box leaf42Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi11ValidityFacts
    leaf42LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf42CoverageChecked :
    coverageCheck (innerAD leaf42Box) leaf42InnerLog = true := by
  rfl'

private theorem leaf42InnerLogValid :
    leaf42InnerLog.Valid 8 (innerAD leaf42Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf42CoverageChecked

private noncomputable def leaf42InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf42InputLogOnePlusV_eq :
    leaf42InputLogOnePlusV = outerEnclosure 24
      (leaf42Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf42RoundedFacts : LeafRoundedFacts 8
    leaf42Certificate.logOnePlusV leaf42InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf42InputLogOnePlusV_eq }

private noncomputable def leaf42Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi11InputQChi innerPair3Input
    leaf42InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf42LowerChecked :
    lowerCheck 24 leaf42Box leaf42Inputs = true := by
  rfl'

private theorem leaf42CoversExact : CoversExact 8
    leaf42Box leaf42Certificate leaf42InnerLog leaf42Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi11RoundedFacts
    innerPair3RoundedFacts leaf42RoundedFacts (by rfl)

private theorem leaf42FlatSound : Sound leaf42Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf42CertificateValid
    leaf42InnerLogValid leaf42CoversExact leaf42LowerChecked

private noncomputable def leaf43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (3/16), chiHi := (1/4) }

private noncomputable def leaf43Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777255/16777216) }, vSqrt := { lower := (65533/65536), upper := (174763/174760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (19693351/16777216) }, upper := { exponent := 0, mantissa := (5/4) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi11LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (349523/349520) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf43InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf43LocalValidity :
    LeafFacts leaf43Box leaf43Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf43Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (174763/174760) }) = true
      norm_num [leaf43Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf43CertificateValid :
    WideCertificateValid leaf43Box leaf43Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi11ValidityFacts
    leaf43LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf43CoverageChecked :
    coverageCheck (innerAD leaf43Box) leaf43InnerLog = true := by
  rfl'

private theorem leaf43InnerLogValid :
    leaf43InnerLog.Valid 8 (innerAD leaf43Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf43CoverageChecked

private noncomputable def leaf43InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf43InputLogOnePlusV_eq :
    leaf43InputLogOnePlusV = outerEnclosure 24
      (leaf43Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf43RoundedFacts : LeafRoundedFacts 8
    leaf43Certificate.logOnePlusV leaf43InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf43InputLogOnePlusV_eq }

private noncomputable def leaf43Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi11InputQChi innerPair3Input
    leaf43InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf43LowerChecked :
    lowerCheck 24 leaf43Box leaf43Inputs = true := by
  rfl'

private theorem leaf43CoversExact : CoversExact 8
    leaf43Box leaf43Certificate leaf43InnerLog leaf43Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi11RoundedFacts
    innerPair3RoundedFacts leaf43RoundedFacts (by rfl)

private theorem leaf43FlatSound : Sound leaf43Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf43CertificateValid
    leaf43InnerLogValid leaf43CoversExact leaf43LowerChecked

private noncomputable def leaf44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16), chiLo := (1/4), chiHi := (3/8) }

private noncomputable def leaf44Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388631/8388608) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097125) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9404331/8388608) }, upper := { exponent := 0, mantissa := (155/128) } }, logOuter := sk6LogOuterCertificate, logK := sk6LogKCertificate, logChi := chi4LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194281/4194250) } }, logDArg := sk6LogDArgCertificate }

private noncomputable def leaf44InnerLog : WideLogData :=
  innerPair7Data

set_option maxRecDepth 1000000 in
private theorem leaf44LocalValidity :
    LeafFacts leaf44Box leaf44Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf44Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097125) }) = true
      norm_num [leaf44Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf44CertificateValid :
    WideCertificateValid leaf44Box leaf44Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk6ValidityFacts chi4ValidityFacts
    leaf44LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf44CoverageChecked :
    coverageCheck (innerAD leaf44Box) leaf44InnerLog = true := by
  rfl'

private theorem leaf44InnerLogValid :
    leaf44InnerLog.Valid 8 (innerAD leaf44Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint5PositiveFacts.valid leaf44CoverageChecked

private noncomputable def leaf44InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf44InputLogOnePlusV_eq :
    leaf44InputLogOnePlusV = outerEnclosure 24
      (leaf44Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf44RoundedFacts : LeafRoundedFacts 8
    leaf44Certificate.logOnePlusV leaf44InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf44InputLogOnePlusV_eq }

private noncomputable def leaf44Inputs : Inputs :=
  inputsOfCaches globalInput sk6RoundedInputs
    chi4InputQChi innerPair7Input
    leaf44InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf44LowerChecked :
    lowerCheck 24 leaf44Box leaf44Inputs = true := by
  rfl'

private theorem leaf44CoversExact : CoversExact 8
    leaf44Box leaf44Certificate leaf44InnerLog leaf44Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk6RoundedFacts chi4RoundedFacts
    innerPair7RoundedFacts leaf44RoundedFacts (by rfl)

private theorem leaf44FlatSound : Sound leaf44Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf44CertificateValid
    leaf44InnerLogValid leaf44CoversExact leaf44LowerChecked

private noncomputable def leaf45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8), chiLo := (1/4), chiHi := (3/8) }

private noncomputable def leaf45Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388633/8388608) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9535393/8388608) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk7LogOuterCertificate, logK := sk7LogKCertificate, logChi := chi4LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk7LogDArgCertificate }

private noncomputable def leaf45InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf45LocalValidity :
    LeafFacts leaf45Box leaf45Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf45Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048561) }) = true
      norm_num [leaf45Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf45CertificateValid :
    WideCertificateValid leaf45Box leaf45Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk7ValidityFacts chi4ValidityFacts
    leaf45LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf45CoverageChecked :
    coverageCheck (innerAD leaf45Box) leaf45InnerLog = true := by
  rfl'

private theorem leaf45InnerLogValid :
    leaf45InnerLog.Valid 8 (innerAD leaf45Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf45CoverageChecked

private noncomputable def leaf45InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf45InputLogOnePlusV_eq :
    leaf45InputLogOnePlusV = outerEnclosure 24
      (leaf45Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf45RoundedFacts : LeafRoundedFacts 8
    leaf45Certificate.logOnePlusV leaf45InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf45InputLogOnePlusV_eq }

private noncomputable def leaf45Inputs : Inputs :=
  inputsOfCaches globalInput sk7RoundedInputs
    chi4InputQChi innerPair3Input
    leaf45InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf45LowerChecked :
    lowerCheck 24 leaf45Box leaf45Inputs = true := by
  rfl'

private theorem leaf45CoversExact : CoversExact 8
    leaf45Box leaf45Certificate leaf45InnerLog leaf45Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk7RoundedFacts chi4RoundedFacts
    innerPair3RoundedFacts leaf45RoundedFacts (by rfl)

private theorem leaf45FlatSound : Sound leaf45Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf45CertificateValid
    leaf45InnerLogValid leaf45CoversExact leaf45LowerChecked

private noncomputable def leaf46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (9/16), chiLo := (3/8), chiHi := (1/2) }

private noncomputable def leaf46Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388633/8388608) }, vSqrt := { lower := (32767/32768), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (9928585/8388608) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk6LogOuterCertificate, logK := sk6LogKCertificate, logChi := chi5LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk6LogDArgCertificate }

private noncomputable def leaf46InnerLog : WideLogData :=
  innerPair4Data

set_option maxRecDepth 1000000 in
private theorem leaf46LocalValidity :
    LeafFacts leaf46Box leaf46Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf46Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524279) }) = true
      norm_num [leaf46Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf46CertificateValid :
    WideCertificateValid leaf46Box leaf46Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk6ValidityFacts chi5ValidityFacts
    leaf46LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf46CoverageChecked :
    coverageCheck (innerAD leaf46Box) leaf46InnerLog = true := by
  rfl'

private theorem leaf46InnerLogValid :
    leaf46InnerLog.Valid 8 (innerAD leaf46Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint6PositiveFacts.valid leaf46CoverageChecked

private noncomputable def leaf46InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf46InputLogOnePlusV_eq :
    leaf46InputLogOnePlusV = outerEnclosure 24
      (leaf46Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf46RoundedFacts : LeafRoundedFacts 8
    leaf46Certificate.logOnePlusV leaf46InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf46InputLogOnePlusV_eq }

private noncomputable def leaf46Inputs : Inputs :=
  inputsOfCaches globalInput sk6RoundedInputs
    chi5InputQChi innerPair4Input
    leaf46InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf46LowerChecked :
    lowerCheck 24 leaf46Box leaf46Inputs = true := by
  rfl'

private theorem leaf46CoversExact : CoversExact 8
    leaf46Box leaf46Certificate leaf46InnerLog leaf46Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk6RoundedFacts chi5RoundedFacts
    innerPair4RoundedFacts leaf46RoundedFacts (by rfl)

private theorem leaf46FlatSound : Sound leaf46Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf46CertificateValid
    leaf46InnerLogValid leaf46CoversExact leaf46LowerChecked

private noncomputable def leaf47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/16), kHi := (5/8), chiLo := (3/8), chiHi := (1/2) }

private noncomputable def leaf47Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388635/8388608) }, vSqrt := { lower := (32767/32768), upper := (524289/524278) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10125179/8388608) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk7LogOuterCertificate, logK := sk7LogKCertificate, logChi := chi5LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1048567/1048556) } }, logDArg := sk7LogDArgCertificate }

private noncomputable def leaf47InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf47LocalValidity :
    LeafFacts leaf47Box leaf47Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf47Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524278) }) = true
      norm_num [leaf47Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf47CertificateValid :
    WideCertificateValid leaf47Box leaf47Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk7ValidityFacts chi5ValidityFacts
    leaf47LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf47CoverageChecked :
    coverageCheck (innerAD leaf47Box) leaf47InnerLog = true := by
  rfl'

private theorem leaf47InnerLogValid :
    leaf47InnerLog.Valid 8 (innerAD leaf47Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf47CoverageChecked

private noncomputable def leaf47InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf47InputLogOnePlusV_eq :
    leaf47InputLogOnePlusV = outerEnclosure 24
      (leaf47Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf47RoundedFacts : LeafRoundedFacts 8
    leaf47Certificate.logOnePlusV leaf47InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf47InputLogOnePlusV_eq }

private noncomputable def leaf47Inputs : Inputs :=
  inputsOfCaches globalInput sk7RoundedInputs
    chi5InputQChi innerPair13Input
    leaf47InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf47LowerChecked :
    lowerCheck 24 leaf47Box leaf47Inputs = true := by
  rfl'

private theorem leaf47CoversExact : CoversExact 8
    leaf47Box leaf47Certificate leaf47InnerLog leaf47Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk7RoundedFacts chi5RoundedFacts
    innerPair13RoundedFacts leaf47RoundedFacts (by rfl)

private theorem leaf47FlatSound : Sound leaf47Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf47CertificateValid
    leaf47InnerLogValid leaf47CoversExact leaf47LowerChecked

private noncomputable def leaf48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (1/4), chiHi := (5/16) }

private noncomputable def leaf48Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777247/16777216) }, vSqrt := { lower := (32767/32768), upper := (1398104/1398083) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (19365699/16777216) }, upper := { exponent := 0, mantissa := (311/256) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi15LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2796187/2796166) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf48InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf48LocalValidity :
    LeafFacts leaf48Box leaf48Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf48Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1398104/1398083) }) = true
      norm_num [leaf48Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf48CertificateValid :
    WideCertificateValid leaf48Box leaf48Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi15ValidityFacts
    leaf48LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf48CoverageChecked :
    coverageCheck (innerAD leaf48Box) leaf48InnerLog = true := by
  rfl'

private theorem leaf48InnerLogValid :
    leaf48InnerLog.Valid 8 (innerAD leaf48Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf48CoverageChecked

private noncomputable def leaf48InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf48InputLogOnePlusV_eq :
    leaf48InputLogOnePlusV = outerEnclosure 24
      (leaf48Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf48RoundedFacts : LeafRoundedFacts 8
    leaf48Certificate.logOnePlusV leaf48InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf48InputLogOnePlusV_eq }

private noncomputable def leaf48Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi15InputQChi innerPair3Input
    leaf48InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf48LowerChecked :
    lowerCheck 24 leaf48Box leaf48Inputs = true := by
  rfl'

private theorem leaf48CoversExact : CoversExact 8
    leaf48Box leaf48Certificate leaf48InnerLog leaf48Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi15RoundedFacts
    innerPair3RoundedFacts leaf48RoundedFacts (by rfl)

private theorem leaf48FlatSound : Sound leaf48Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf48CertificateValid
    leaf48InnerLogValid leaf48CoversExact leaf48LowerChecked

private noncomputable def leaf49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (5/16), chiHi := (3/8) }

private noncomputable def leaf49Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777249/16777216) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097119) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (20021017/16777216) }, upper := { exponent := 0, mantissa := (161/128) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi16LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194275/4194238) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf49InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf49LocalValidity :
    LeafFacts leaf49Box leaf49Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf49Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097119) }) = true
      norm_num [leaf49Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf49CertificateValid :
    WideCertificateValid leaf49Box leaf49Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi16ValidityFacts
    leaf49LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf49CoverageChecked :
    coverageCheck (innerAD leaf49Box) leaf49InnerLog = true := by
  rfl'

private theorem leaf49InnerLogValid :
    leaf49InnerLog.Valid 8 (innerAD leaf49Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf49CoverageChecked

private noncomputable def leaf49InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf49InputLogOnePlusV_eq :
    leaf49InputLogOnePlusV = outerEnclosure 24
      (leaf49Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf49RoundedFacts : LeafRoundedFacts 8
    leaf49Certificate.logOnePlusV leaf49InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf49InputLogOnePlusV_eq }

private noncomputable def leaf49Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi16InputQChi innerPair13Input
    leaf49InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf49LowerChecked :
    lowerCheck 24 leaf49Box leaf49Inputs = true := by
  rfl'

private theorem leaf49CoversExact : CoversExact 8
    leaf49Box leaf49Certificate leaf49InnerLog leaf49Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi16RoundedFacts
    innerPair13RoundedFacts leaf49RoundedFacts (by rfl)

private theorem leaf49FlatSound : Sound leaf49Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf49CertificateValid
    leaf49InnerLogValid leaf49CoversExact leaf49LowerChecked

private noncomputable def leaf50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (1/4), chiHi := (5/16) }

private noncomputable def leaf50Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777249/16777216) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (19627825/16777216) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi15LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf50InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf50LocalValidity :
    LeafFacts leaf50Box leaf50Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf50Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048561) }) = true
      norm_num [leaf50Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf50CertificateValid :
    WideCertificateValid leaf50Box leaf50Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi15ValidityFacts
    leaf50LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf50CoverageChecked :
    coverageCheck (innerAD leaf50Box) leaf50InnerLog = true := by
  rfl'

private theorem leaf50InnerLogValid :
    leaf50InnerLog.Valid 8 (innerAD leaf50Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf50CoverageChecked

private noncomputable def leaf50InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf50InputLogOnePlusV_eq :
    leaf50InputLogOnePlusV = outerEnclosure 24
      (leaf50Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf50RoundedFacts : LeafRoundedFacts 8
    leaf50Certificate.logOnePlusV leaf50InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf50InputLogOnePlusV_eq }

private noncomputable def leaf50Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi15InputQChi innerPair3Input
    leaf50InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf50LowerChecked :
    lowerCheck 24 leaf50Box leaf50Inputs = true := by
  rfl'

private theorem leaf50CoversExact : CoversExact 8
    leaf50Box leaf50Certificate leaf50InnerLog leaf50Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi15RoundedFacts
    innerPair3RoundedFacts leaf50RoundedFacts (by rfl)

private theorem leaf50FlatSound : Sound leaf50Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf50CertificateValid
    leaf50InnerLogValid leaf50CoversExact leaf50LowerChecked

private noncomputable def leaf51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (5/16), chiHi := (3/8) }

private noncomputable def leaf51Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777251/16777216) }, vSqrt := { lower := (32767/32768), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (20348675/16777216) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi16LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf51InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf51LocalValidity :
    LeafFacts leaf51Box leaf51Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf51Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524279) }) = true
      norm_num [leaf51Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf51CertificateValid :
    WideCertificateValid leaf51Box leaf51Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi16ValidityFacts
    leaf51LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf51CoverageChecked :
    coverageCheck (innerAD leaf51Box) leaf51InnerLog = true := by
  rfl'

private theorem leaf51InnerLogValid :
    leaf51InnerLog.Valid 8 (innerAD leaf51Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf51CoverageChecked

private noncomputable def leaf51InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf51InputLogOnePlusV_eq :
    leaf51InputLogOnePlusV = outerEnclosure 24
      (leaf51Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf51RoundedFacts : LeafRoundedFacts 8
    leaf51Certificate.logOnePlusV leaf51InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf51InputLogOnePlusV_eq }

private noncomputable def leaf51Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi16InputQChi innerPair13Input
    leaf51InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf51LowerChecked :
    lowerCheck 24 leaf51Box leaf51Inputs = true := by
  rfl'

private theorem leaf51CoversExact : CoversExact 8
    leaf51Box leaf51Certificate leaf51InnerLog leaf51Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi16RoundedFacts
    innerPair13RoundedFacts leaf51RoundedFacts (by rfl)

private theorem leaf51FlatSound : Sound leaf51Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf51CertificateValid
    leaf51InnerLogValid leaf51CoversExact leaf51LowerChecked

private noncomputable def leaf52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (3/8), chiHi := (1/2) }

private noncomputable def leaf52Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (8388637/8388608) }, vSqrt := { lower := (32767/32768), upper := (174763/174759) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (10321773/8388608) }, upper := { exponent := 0, mantissa := (43/32) } }, logOuter := sk9LogOuterCertificate, logK := sk9LogKCertificate, logChi := chi5LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (174761/174759) } }, logDArg := sk9LogDArgCertificate }

private noncomputable def leaf52InnerLog : WideLogData :=
  innerPair14Data

set_option maxRecDepth 1000000 in
private theorem leaf52LocalValidity :
    LeafFacts leaf52Box leaf52Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf52Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (174763/174759) }) = true
      norm_num [leaf52Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf52CertificateValid :
    WideCertificateValid leaf52Box leaf52Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk9ValidityFacts chi5ValidityFacts
    leaf52LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf52CoverageChecked :
    coverageCheck (innerAD leaf52Box) leaf52InnerLog = true := by
  rfl'

private theorem leaf52InnerLogValid :
    leaf52InnerLog.Valid 8 (innerAD leaf52Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint7PositiveFacts.valid leaf52CoverageChecked

private noncomputable def leaf52InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf52InputLogOnePlusV_eq :
    leaf52InputLogOnePlusV = outerEnclosure 24
      (leaf52Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf52RoundedFacts : LeafRoundedFacts 8
    leaf52Certificate.logOnePlusV leaf52InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf52InputLogOnePlusV_eq }

private noncomputable def leaf52Inputs : Inputs :=
  inputsOfCaches globalInput sk9RoundedInputs
    chi5InputQChi innerPair14Input
    leaf52InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf52LowerChecked :
    lowerCheck 24 leaf52Box leaf52Inputs = true := by
  rfl'

private theorem leaf52CoversExact : CoversExact 8
    leaf52Box leaf52Certificate leaf52InnerLog leaf52Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk9RoundedFacts chi5RoundedFacts
    innerPair14RoundedFacts leaf52RoundedFacts (by rfl)

private theorem leaf52FlatSound : Sound leaf52Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf52CertificateValid
    leaf52InnerLogValid leaf52CoversExact leaf52LowerChecked

private noncomputable def leaf53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (3/8), chiHi := (7/16) }

private noncomputable def leaf53Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777253/16777216) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (21069525/16777216) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi17LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097133/2097110) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf53InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf53LocalValidity :
    LeafFacts leaf53Box leaf53Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf53Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048555) }) = true
      norm_num [leaf53Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf53CertificateValid :
    WideCertificateValid leaf53Box leaf53Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi17ValidityFacts
    leaf53LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf53CoverageChecked :
    coverageCheck (innerAD leaf53Box) leaf53InnerLog = true := by
  rfl'

private theorem leaf53InnerLogValid :
    leaf53InnerLog.Valid 8 (innerAD leaf53Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf53CoverageChecked

private noncomputable def leaf53InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf53InputLogOnePlusV_eq :
    leaf53InputLogOnePlusV = outerEnclosure 24
      (leaf53Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf53RoundedFacts : LeafRoundedFacts 8
    leaf53Certificate.logOnePlusV leaf53InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf53InputLogOnePlusV_eq }

private noncomputable def leaf53Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi17InputQChi innerPair17Input
    leaf53InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf53LowerChecked :
    lowerCheck 24 leaf53Box leaf53Inputs = true := by
  rfl'

private theorem leaf53CoversExact : CoversExact 8
    leaf53Box leaf53Certificate leaf53InnerLog leaf53Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi17RoundedFacts
    innerPair17RoundedFacts leaf53RoundedFacts (by rfl)

private theorem leaf53FlatSound : Sound leaf53Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf53CertificateValid
    leaf53InnerLogValid leaf53CoversExact leaf53LowerChecked

private noncomputable def leaf54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (7/16), chiHi := (1/2) }

private noncomputable def leaf54Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777255/16777216) }, vSqrt := { lower := (32767/32768), upper := (524289/524276) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (21790375/16777216) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk10LogOuterCertificate, logK := sk10LogKCertificate, logChi := chi18LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1048565/1048552) } }, logDArg := sk10LogDArgCertificate }

private noncomputable def leaf54InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf54LocalValidity :
    LeafFacts leaf54Box leaf54Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf54Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524276) }) = true
      norm_num [leaf54Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf54CertificateValid :
    WideCertificateValid leaf54Box leaf54Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk10ValidityFacts chi18ValidityFacts
    leaf54LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf54CoverageChecked :
    coverageCheck (innerAD leaf54Box) leaf54InnerLog = true := by
  rfl'

private theorem leaf54InnerLogValid :
    leaf54InnerLog.Valid 8 (innerAD leaf54Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf54CoverageChecked

private noncomputable def leaf54InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf54InputLogOnePlusV_eq :
    leaf54InputLogOnePlusV = outerEnclosure 24
      (leaf54Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf54RoundedFacts : LeafRoundedFacts 8
    leaf54Certificate.logOnePlusV leaf54InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf54InputLogOnePlusV_eq }

private noncomputable def leaf54Inputs : Inputs :=
  inputsOfCaches globalInput sk10RoundedInputs
    chi18InputQChi innerPair17Input
    leaf54InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf54LowerChecked :
    lowerCheck 24 leaf54Box leaf54Inputs = true := by
  rfl'

private theorem leaf54CoversExact : CoversExact 8
    leaf54Box leaf54Certificate leaf54InnerLog leaf54Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk10RoundedFacts chi18RoundedFacts
    innerPair17RoundedFacts leaf54RoundedFacts (by rfl)

private theorem leaf54FlatSound : Sound leaf54Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf54CertificateValid
    leaf54InnerLogValid leaf54CoversExact leaf54LowerChecked

private noncomputable def leaf55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (1/4), chiHi := (5/16) }

private noncomputable def leaf55Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777251/16777216) }, vSqrt := { lower := (32767/32768), upper := (4194312/4194239) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (19889951/16777216) }, upper := { exponent := 0, mantissa := (321/256) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi15LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (8388551/8388478) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf55InnerLog : WideLogData :=
  innerPair4Data

set_option maxRecDepth 1000000 in
private theorem leaf55LocalValidity :
    LeafFacts leaf55Box leaf55Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf55Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (4194312/4194239) }) = true
      norm_num [leaf55Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf55CertificateValid :
    WideCertificateValid leaf55Box leaf55Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi15ValidityFacts
    leaf55LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf55CoverageChecked :
    coverageCheck (innerAD leaf55Box) leaf55InnerLog = true := by
  rfl'

private theorem leaf55InnerLogValid :
    leaf55InnerLog.Valid 8 (innerAD leaf55Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint6PositiveFacts.valid leaf55CoverageChecked

private noncomputable def leaf55InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf55InputLogOnePlusV_eq :
    leaf55InputLogOnePlusV = outerEnclosure 24
      (leaf55Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf55RoundedFacts : LeafRoundedFacts 8
    leaf55Certificate.logOnePlusV leaf55InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf55InputLogOnePlusV_eq }

private noncomputable def leaf55Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi15InputQChi innerPair4Input
    leaf55InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf55LowerChecked :
    lowerCheck 24 leaf55Box leaf55Inputs = true := by
  rfl'

private theorem leaf55CoversExact : CoversExact 8
    leaf55Box leaf55Certificate leaf55InnerLog leaf55Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi15RoundedFacts
    innerPair4RoundedFacts leaf55RoundedFacts (by rfl)

private theorem leaf55FlatSound : Sound leaf55Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf55CertificateValid
    leaf55InnerLogValid leaf55CoversExact leaf55LowerChecked

private noncomputable def leaf56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (5/16), chiHi := (3/8) }

private noncomputable def leaf56Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777253/16777216) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (20676333/16777216) }, upper := { exponent := 0, mantissa := (167/128) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi16LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194269/4194226) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf56InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf56LocalValidity :
    LeafFacts leaf56Box leaf56Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf56Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097113) }) = true
      norm_num [leaf56Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf56CertificateValid :
    WideCertificateValid leaf56Box leaf56Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi16ValidityFacts
    leaf56LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf56CoverageChecked :
    coverageCheck (innerAD leaf56Box) leaf56InnerLog = true := by
  rfl'

private theorem leaf56InnerLogValid :
    leaf56InnerLog.Valid 8 (innerAD leaf56Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf56CoverageChecked

private noncomputable def leaf56InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf56InputLogOnePlusV_eq :
    leaf56InputLogOnePlusV = outerEnclosure 24
      (leaf56Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf56RoundedFacts : LeafRoundedFacts 8
    leaf56Certificate.logOnePlusV leaf56InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf56InputLogOnePlusV_eq }

private noncomputable def leaf56Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi16InputQChi innerPair13Input
    leaf56InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf56LowerChecked :
    lowerCheck 24 leaf56Box leaf56Inputs = true := by
  rfl'

private theorem leaf56CoversExact : CoversExact 8
    leaf56Box leaf56Certificate leaf56InnerLog leaf56Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi16RoundedFacts
    innerPair13RoundedFacts leaf56RoundedFacts (by rfl)

private theorem leaf56FlatSound : Sound leaf56Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf56CertificateValid
    leaf56InnerLogValid leaf56CoversExact leaf56LowerChecked

private noncomputable def leaf57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (1/4), chiHi := (5/16) }

private noncomputable def leaf57Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777253/16777216) }, vSqrt := { lower := (32767/32768), upper := (699052/699039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (20152077/16777216) }, upper := { exponent := 0, mantissa := (163/128) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi15LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (1398091/1398078) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf57InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf57LocalValidity :
    LeafFacts leaf57Box leaf57Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf57Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (699052/699039) }) = true
      norm_num [leaf57Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf57CertificateValid :
    WideCertificateValid leaf57Box leaf57Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi15ValidityFacts
    leaf57LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf57CoverageChecked :
    coverageCheck (innerAD leaf57Box) leaf57InnerLog = true := by
  rfl'

private theorem leaf57InnerLogValid :
    leaf57InnerLog.Valid 8 (innerAD leaf57Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf57CoverageChecked

private noncomputable def leaf57InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf57InputLogOnePlusV_eq :
    leaf57InputLogOnePlusV = outerEnclosure 24
      (leaf57Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf57RoundedFacts : LeafRoundedFacts 8
    leaf57Certificate.logOnePlusV leaf57InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf57InputLogOnePlusV_eq }

private noncomputable def leaf57Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi15InputQChi innerPair13Input
    leaf57InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf57LowerChecked :
    lowerCheck 24 leaf57Box leaf57Inputs = true := by
  rfl'

private theorem leaf57CoversExact : CoversExact 8
    leaf57Box leaf57Certificate leaf57InnerLog leaf57Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi15RoundedFacts
    innerPair13RoundedFacts leaf57RoundedFacts (by rfl)

private theorem leaf57FlatSound : Sound leaf57Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf57CertificateValid
    leaf57InnerLogValid leaf57CoversExact leaf57LowerChecked

private noncomputable def leaf58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (5/16), chiHi := (3/8) }

private noncomputable def leaf58Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777255/16777216) }, vSqrt := { lower := (32767/32768), upper := (1048578/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (21003991/16777216) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi16LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2097133/2097110) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf58InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf58LocalValidity :
    LeafFacts leaf58Box leaf58Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf58Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1048578/1048555) }) = true
      norm_num [leaf58Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf58CertificateValid :
    WideCertificateValid leaf58Box leaf58Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi16ValidityFacts
    leaf58LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf58CoverageChecked :
    coverageCheck (innerAD leaf58Box) leaf58InnerLog = true := by
  rfl'

private theorem leaf58InnerLogValid :
    leaf58InnerLog.Valid 8 (innerAD leaf58Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf58CoverageChecked

private noncomputable def leaf58InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf58InputLogOnePlusV_eq :
    leaf58InputLogOnePlusV = outerEnclosure 24
      (leaf58Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf58RoundedFacts : LeafRoundedFacts 8
    leaf58Certificate.logOnePlusV leaf58InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf58InputLogOnePlusV_eq }

private noncomputable def leaf58Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi16InputQChi innerPair17Input
    leaf58InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf58LowerChecked :
    lowerCheck 24 leaf58Box leaf58Inputs = true := by
  rfl'

private theorem leaf58CoversExact : CoversExact 8
    leaf58Box leaf58Certificate leaf58InnerLog leaf58Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi16RoundedFacts
    innerPair17RoundedFacts leaf58RoundedFacts (by rfl)

private theorem leaf58FlatSound : Sound leaf58Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf58CertificateValid
    leaf58InnerLogValid leaf58CoversExact leaf58LowerChecked

private noncomputable def leaf59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (1/4), chiHi := (5/16) }

private noncomputable def leaf59Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777255/16777216) }, vSqrt := { lower := (32767/32768), upper := (4194312/4194229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (20414203/16777216) }, upper := { exponent := 0, mantissa := (331/256) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi15LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (8388541/8388458) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf59InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf59LocalValidity :
    LeafFacts leaf59Box leaf59Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf59Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (4194312/4194229) }) = true
      norm_num [leaf59Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf59CertificateValid :
    WideCertificateValid leaf59Box leaf59Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi15ValidityFacts
    leaf59LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf59CoverageChecked :
    coverageCheck (innerAD leaf59Box) leaf59InnerLog = true := by
  rfl'

private theorem leaf59InnerLogValid :
    leaf59InnerLog.Valid 8 (innerAD leaf59Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf59CoverageChecked

private noncomputable def leaf59InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf59InputLogOnePlusV_eq :
    leaf59InputLogOnePlusV = outerEnclosure 24
      (leaf59Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf59RoundedFacts : LeafRoundedFacts 8
    leaf59Certificate.logOnePlusV leaf59InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf59InputLogOnePlusV_eq }

private noncomputable def leaf59Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi15InputQChi innerPair13Input
    leaf59InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf59LowerChecked :
    lowerCheck 24 leaf59Box leaf59Inputs = true := by
  rfl'

private theorem leaf59CoversExact : CoversExact 8
    leaf59Box leaf59Certificate leaf59InnerLog leaf59Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi15RoundedFacts
    innerPair13RoundedFacts leaf59RoundedFacts (by rfl)

private theorem leaf59FlatSound : Sound leaf59Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf59CertificateValid
    leaf59InnerLogValid leaf59CoversExact leaf59LowerChecked

private noncomputable def leaf60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (1/4), chiHi := (5/16) }

private noncomputable def leaf60Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777257/16777216) }, vSqrt := { lower := (65533/65536), upper := (524289/524278) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (20676329/16777216) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi15LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1048567/1048556) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf60InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf60LocalValidity :
    LeafFacts leaf60Box leaf60Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf60Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (524289/524278) }) = true
      norm_num [leaf60Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf60CertificateValid :
    WideCertificateValid leaf60Box leaf60Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi15ValidityFacts
    leaf60LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf60CoverageChecked :
    coverageCheck (innerAD leaf60Box) leaf60InnerLog = true := by
  rfl'

private theorem leaf60InnerLogValid :
    leaf60InnerLog.Valid 8 (innerAD leaf60Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf60CoverageChecked

private noncomputable def leaf60InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf60InputLogOnePlusV_eq :
    leaf60InputLogOnePlusV = outerEnclosure 24
      (leaf60Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf60RoundedFacts : LeafRoundedFacts 8
    leaf60Certificate.logOnePlusV leaf60InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf60InputLogOnePlusV_eq }

private noncomputable def leaf60Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi15InputQChi innerPair13Input
    leaf60InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf60LowerChecked :
    lowerCheck 24 leaf60Box leaf60Inputs = true := by
  rfl'

private theorem leaf60CoversExact : CoversExact 8
    leaf60Box leaf60Certificate leaf60InnerLog leaf60Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi15RoundedFacts
    innerPair13RoundedFacts leaf60RoundedFacts (by rfl)

private theorem leaf60FlatSound : Sound leaf60Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf60CertificateValid
    leaf60InnerLogValid leaf60CoversExact leaf60LowerChecked

private noncomputable def leaf61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (5/16), chiHi := (3/8) }

private noncomputable def leaf61Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777257/16777216) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (21331649/16777216) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi16LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194263/4194214) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf61InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf61LocalValidity :
    LeafFacts leaf61Box leaf61Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf61Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097107) }) = true
      norm_num [leaf61Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf61CertificateValid :
    WideCertificateValid leaf61Box leaf61Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi16ValidityFacts
    leaf61LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf61CoverageChecked :
    coverageCheck (innerAD leaf61Box) leaf61InnerLog = true := by
  rfl'

private theorem leaf61InnerLogValid :
    leaf61InnerLog.Valid 8 (innerAD leaf61Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf61CoverageChecked

private noncomputable def leaf61InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf61InputLogOnePlusV_eq :
    leaf61InputLogOnePlusV = outerEnclosure 24
      (leaf61Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf61RoundedFacts : LeafRoundedFacts 8
    leaf61Certificate.logOnePlusV leaf61InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf61InputLogOnePlusV_eq }

private noncomputable def leaf61Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi16InputQChi innerPair17Input
    leaf61InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf61LowerChecked :
    lowerCheck 24 leaf61Box leaf61Inputs = true := by
  rfl'

private theorem leaf61CoversExact : CoversExact 8
    leaf61Box leaf61Certificate leaf61InnerLog leaf61Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi16RoundedFacts
    innerPair17RoundedFacts leaf61RoundedFacts (by rfl)

private theorem leaf61FlatSound : Sound leaf61Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf61CertificateValid
    leaf61InnerLogValid leaf61CoversExact leaf61LowerChecked

private noncomputable def leaf62Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (5/16), chiHi := (3/8) }

private noncomputable def leaf62Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777259/16777216) }, vSqrt := { lower := (65533/65536), upper := (524289/524276) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (21659307/16777216) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi16LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1048565/1048552) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf62InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf62LocalValidity :
    LeafFacts leaf62Box leaf62Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf62Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (524289/524276) }) = true
      norm_num [leaf62Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf62CertificateValid :
    WideCertificateValid leaf62Box leaf62Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi16ValidityFacts
    leaf62LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf62CoverageChecked :
    coverageCheck (innerAD leaf62Box) leaf62InnerLog = true := by
  rfl'

private theorem leaf62InnerLogValid :
    leaf62InnerLog.Valid 8 (innerAD leaf62Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf62CoverageChecked

private noncomputable def leaf62InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf62InputLogOnePlusV_eq :
    leaf62InputLogOnePlusV = outerEnclosure 24
      (leaf62Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf62RoundedFacts : LeafRoundedFacts 8
    leaf62Certificate.logOnePlusV leaf62InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf62InputLogOnePlusV_eq }

private noncomputable def leaf62Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi16InputQChi innerPair17Input
    leaf62InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf62LowerChecked :
    lowerCheck 24 leaf62Box leaf62Inputs = true := by
  rfl'

private theorem leaf62CoversExact : CoversExact 8
    leaf62Box leaf62Certificate leaf62InnerLog leaf62Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi16RoundedFacts
    innerPair17RoundedFacts leaf62RoundedFacts (by rfl)

private theorem leaf62FlatSound : Sound leaf62Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf62CertificateValid
    leaf62InnerLogValid leaf62CoversExact leaf62LowerChecked

private noncomputable def leaf63Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (3/8), chiHi := (7/16) }

private noncomputable def leaf63Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777255/16777216) }, vSqrt := { lower := (32767/32768), upper := (1398104/1398071) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (21462715/16777216) }, upper := { exponent := 0, mantissa := (347/256) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi17LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (2796175/2796142) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf63InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf63LocalValidity :
    LeafFacts leaf63Box leaf63Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf63Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (1398104/1398071) }) = true
      norm_num [leaf63Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf63CertificateValid :
    WideCertificateValid leaf63Box leaf63Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi17ValidityFacts
    leaf63LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf63CoverageChecked :
    coverageCheck (innerAD leaf63Box) leaf63InnerLog = true := by
  rfl'

private theorem leaf63InnerLogValid :
    leaf63InnerLog.Valid 8 (innerAD leaf63Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf63CoverageChecked

private noncomputable def leaf63InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf63InputLogOnePlusV_eq :
    leaf63InputLogOnePlusV = outerEnclosure 24
      (leaf63Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf63RoundedFacts : LeafRoundedFacts 8
    leaf63Certificate.logOnePlusV leaf63InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf63InputLogOnePlusV_eq }

private noncomputable def leaf63Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi17InputQChi innerPair17Input
    leaf63InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf63LowerChecked :
    lowerCheck 24 leaf63Box leaf63Inputs = true := by
  rfl'

private theorem leaf63CoversExact : CoversExact 8
    leaf63Box leaf63Certificate leaf63InnerLog leaf63Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi17RoundedFacts
    innerPair17RoundedFacts leaf63RoundedFacts (by rfl)

private theorem leaf63FlatSound : Sound leaf63Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf63CertificateValid
    leaf63InnerLogValid leaf63CoversExact leaf63LowerChecked

private noncomputable def leaf64Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (7/16), chiHi := (1/2) }

private noncomputable def leaf64Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777257/16777216) }, vSqrt := { lower := (32767/32768), upper := (524289/524275) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (22249097/16777216) }, upper := { exponent := 0, mantissa := (45/32) } }, logOuter := sk15LogOuterCertificate, logK := sk15LogKCertificate, logChi := chi18LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (524282/524275) } }, logDArg := sk15LogDArgCertificate }

private noncomputable def leaf64InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf64LocalValidity :
    LeafFacts leaf64Box leaf64Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf64Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (524289/524275) }) = true
      norm_num [leaf64Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf64CertificateValid :
    WideCertificateValid leaf64Box leaf64Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk15ValidityFacts chi18ValidityFacts
    leaf64LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf64CoverageChecked :
    coverageCheck (innerAD leaf64Box) leaf64InnerLog = true := by
  rfl'

private theorem leaf64InnerLogValid :
    leaf64InnerLog.Valid 8 (innerAD leaf64Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf64CoverageChecked

private noncomputable def leaf64InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf64InputLogOnePlusV_eq :
    leaf64InputLogOnePlusV = outerEnclosure 24
      (leaf64Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf64RoundedFacts : LeafRoundedFacts 8
    leaf64Certificate.logOnePlusV leaf64InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf64InputLogOnePlusV_eq }

private noncomputable def leaf64Inputs : Inputs :=
  inputsOfCaches globalInput sk15RoundedInputs
    chi18InputQChi innerPair22Input
    leaf64InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf64LowerChecked :
    lowerCheck 24 leaf64Box leaf64Inputs = true := by
  rfl'

private theorem leaf64CoversExact : CoversExact 8
    leaf64Box leaf64Certificate leaf64InnerLog leaf64Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk15RoundedFacts chi18RoundedFacts
    innerPair22RoundedFacts leaf64RoundedFacts (by rfl)

private theorem leaf64FlatSound : Sound leaf64Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf64CertificateValid
    leaf64InnerLogValid leaf64CoversExact leaf64LowerChecked

private noncomputable def leaf65Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (3/8), chiHi := (7/16) }

private noncomputable def leaf65Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777257/16777216) }, vSqrt := { lower := (32767/32768), upper := (2097156/2097103) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (21855905/16777216) }, upper := { exponent := 0, mantissa := (177/128) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi17LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (4194259/4194206) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf65InnerLog : WideLogData :=
  innerPair19Data

set_option maxRecDepth 1000000 in
private theorem leaf65LocalValidity :
    LeafFacts leaf65Box leaf65Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf65Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (2097156/2097103) }) = true
      norm_num [leaf65Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf65CertificateValid :
    WideCertificateValid leaf65Box leaf65Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi17ValidityFacts
    leaf65LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf65CoverageChecked :
    coverageCheck (innerAD leaf65Box) leaf65InnerLog = true := by
  rfl'

private theorem leaf65InnerLogValid :
    leaf65InnerLog.Valid 8 (innerAD leaf65Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint10PositiveFacts.valid leaf65CoverageChecked

private noncomputable def leaf65InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf65InputLogOnePlusV_eq :
    leaf65InputLogOnePlusV = outerEnclosure 24
      (leaf65Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf65RoundedFacts : LeafRoundedFacts 8
    leaf65Certificate.logOnePlusV leaf65InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf65InputLogOnePlusV_eq }

private noncomputable def leaf65Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi17InputQChi innerPair19Input
    leaf65InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf65LowerChecked :
    lowerCheck 24 leaf65Box leaf65Inputs = true := by
  rfl'

private theorem leaf65CoversExact : CoversExact 8
    leaf65Box leaf65Certificate leaf65InnerLog leaf65Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi17RoundedFacts
    innerPair19RoundedFacts leaf65RoundedFacts (by rfl)

private theorem leaf65FlatSound : Sound leaf65Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf65CertificateValid
    leaf65InnerLogValid leaf65CoversExact leaf65LowerChecked

private noncomputable def leaf66Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (7/16), chiHi := (1/2) }

private noncomputable def leaf66Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777259/16777216) }, vSqrt := { lower := (32767/32768), upper := (174763/174758) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (22707819/16777216) }, upper := { exponent := 0, mantissa := (23/16) } }, logOuter := sk16LogOuterCertificate, logK := sk16LogKCertificate, logChi := chi18LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (349521/349516) } }, logDArg := sk16LogDArgCertificate }

private noncomputable def leaf66InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf66LocalValidity :
    LeafFacts leaf66Box leaf66Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf66Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (174763/174758) }) = true
      norm_num [leaf66Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf66CertificateValid :
    WideCertificateValid leaf66Box leaf66Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk16ValidityFacts chi18ValidityFacts
    leaf66LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf66CoverageChecked :
    coverageCheck (innerAD leaf66Box) leaf66InnerLog = true := by
  rfl'

private theorem leaf66InnerLogValid :
    leaf66InnerLog.Valid 8 (innerAD leaf66Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf66CoverageChecked

private noncomputable def leaf66InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf66InputLogOnePlusV_eq :
    leaf66InputLogOnePlusV = outerEnclosure 24
      (leaf66Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf66RoundedFacts : LeafRoundedFacts 8
    leaf66Certificate.logOnePlusV leaf66InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf66InputLogOnePlusV_eq }

private noncomputable def leaf66Inputs : Inputs :=
  inputsOfCaches globalInput sk16RoundedInputs
    chi18InputQChi innerPair22Input
    leaf66InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf66LowerChecked :
    lowerCheck 24 leaf66Box leaf66Inputs = true := by
  rfl'

private theorem leaf66CoversExact : CoversExact 8
    leaf66Box leaf66Certificate leaf66InnerLog leaf66Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk16RoundedFacts chi18RoundedFacts
    innerPair22RoundedFacts leaf66RoundedFacts (by rfl)

private theorem leaf66FlatSound : Sound leaf66Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf66CertificateValid
    leaf66InnerLogValid leaf66CoversExact leaf66LowerChecked

private noncomputable def leaf67Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (3/8), chiHi := (7/16) }

private noncomputable def leaf67Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777259/16777216) }, vSqrt := { lower := (32767/32768), upper := (4194312/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (22249095/16777216) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi17LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (8388511/8388398) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf67InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf67LocalValidity :
    LeafFacts leaf67Box leaf67Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf67Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (4194312/4194199) }) = true
      norm_num [leaf67Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf67CertificateValid :
    WideCertificateValid leaf67Box leaf67Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi17ValidityFacts
    leaf67LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf67CoverageChecked :
    coverageCheck (innerAD leaf67Box) leaf67InnerLog = true := by
  rfl'

private theorem leaf67InnerLogValid :
    leaf67InnerLog.Valid 8 (innerAD leaf67Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf67CoverageChecked

private noncomputable def leaf67InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf67InputLogOnePlusV_eq :
    leaf67InputLogOnePlusV = outerEnclosure 24
      (leaf67Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf67RoundedFacts : LeafRoundedFacts 8
    leaf67Certificate.logOnePlusV leaf67InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf67InputLogOnePlusV_eq }

private noncomputable def leaf67Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi17InputQChi innerPair22Input
    leaf67InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf67LowerChecked :
    lowerCheck 24 leaf67Box leaf67Inputs = true := by
  rfl'

private theorem leaf67CoversExact : CoversExact 8
    leaf67Box leaf67Certificate leaf67InnerLog leaf67Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi17RoundedFacts
    innerPair22RoundedFacts leaf67RoundedFacts (by rfl)

private theorem leaf67FlatSound : Sound leaf67Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf67CertificateValid
    leaf67InnerLogValid leaf67CoversExact leaf67LowerChecked

private noncomputable def leaf68Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (3/8), chiHi := (7/16) }

private noncomputable def leaf68Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777261/16777216) }, vSqrt := { lower := (65533/65536), upper := (174763/174758) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (22642285/16777216) }, upper := { exponent := 0, mantissa := (23/16) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi17LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (349521/349516) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf68InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf68LocalValidity :
    LeafFacts leaf68Box leaf68Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf68Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (174763/174758) }) = true
      norm_num [leaf68Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf68CertificateValid :
    WideCertificateValid leaf68Box leaf68Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi17ValidityFacts
    leaf68LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf68CoverageChecked :
    coverageCheck (innerAD leaf68Box) leaf68InnerLog = true := by
  rfl'

private theorem leaf68InnerLogValid :
    leaf68InnerLog.Valid 8 (innerAD leaf68Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf68CoverageChecked

private noncomputable def leaf68InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf68InputLogOnePlusV_eq :
    leaf68InputLogOnePlusV = outerEnclosure 24
      (leaf68Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf68RoundedFacts : LeafRoundedFacts 8
    leaf68Certificate.logOnePlusV leaf68InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf68InputLogOnePlusV_eq }

private noncomputable def leaf68Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi17InputQChi innerPair22Input
    leaf68InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf68LowerChecked :
    lowerCheck 24 leaf68Box leaf68Inputs = true := by
  rfl'

private theorem leaf68CoversExact : CoversExact 8
    leaf68Box leaf68Certificate leaf68InnerLog leaf68Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi17RoundedFacts
    innerPair22RoundedFacts leaf68RoundedFacts (by rfl)

private theorem leaf68FlatSound : Sound leaf68Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf68CertificateValid
    leaf68InnerLogValid leaf68CoversExact leaf68LowerChecked

private noncomputable def leaf69Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (15/16), chiLo := (7/16), chiHi := (1/2) }

private noncomputable def leaf69Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777261/16777216) }, vSqrt := { lower := (32767/32768), upper := (34359279615/34358755328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (23166541/16777216) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk13LogOuterCertificate, logK := sk13LogKCertificate, logChi := chi18LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65535/32768) }, upper := { exponent := 1, mantissa := (68718034943/68717510656) } }, logDArg := sk13LogDArgCertificate }

private noncomputable def leaf69InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf69LocalValidity :
    LeafFacts leaf69Box leaf69Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf69Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32767/32768), upper := (34359279615/34358755328) }) = true
      norm_num [leaf69Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf69CertificateValid :
    WideCertificateValid leaf69Box leaf69Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk13ValidityFacts chi18ValidityFacts
    leaf69LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf69CoverageChecked :
    coverageCheck (innerAD leaf69Box) leaf69InnerLog = true := by
  rfl'

private theorem leaf69InnerLogValid :
    leaf69InnerLog.Valid 8 (innerAD leaf69Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf69CoverageChecked

private noncomputable def leaf69InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628823/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf69InputLogOnePlusV_eq :
    leaf69InputLogOnePlusV = outerEnclosure 24
      (leaf69Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf69RoundedFacts : LeafRoundedFacts 8
    leaf69Certificate.logOnePlusV leaf69InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf69InputLogOnePlusV_eq }

private noncomputable def leaf69Inputs : Inputs :=
  inputsOfCaches globalInput sk13RoundedInputs
    chi18InputQChi innerPair27Input
    leaf69InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf69LowerChecked :
    lowerCheck 24 leaf69Box leaf69Inputs = true := by
  rfl'

private theorem leaf69CoversExact : CoversExact 8
    leaf69Box leaf69Certificate leaf69InnerLog leaf69Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk13RoundedFacts chi18RoundedFacts
    innerPair27RoundedFacts leaf69RoundedFacts (by rfl)

private theorem leaf69FlatSound : Sound leaf69Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf69CertificateValid
    leaf69InnerLogValid leaf69CoversExact leaf69LowerChecked

private noncomputable def leaf70Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/16), kHi := (1), chiLo := (7/16), chiHi := (1/2) }

private noncomputable def leaf70Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777263/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358689792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (23625263/16777216) }, upper := { exponent := 0, mantissa := (3/2) } }, logOuter := sk14LogOuterCertificate, logK := sk14LogKCertificate, logChi := chi18LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717969407/68717379584) } }, logDArg := sk14LogDArgCertificate }

private noncomputable def leaf70InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf70LocalValidity :
    LeafFacts leaf70Box leaf70Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf70Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358689792) }) = true
      norm_num [leaf70Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf70CertificateValid :
    WideCertificateValid leaf70Box leaf70Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk14ValidityFacts chi18ValidityFacts
    leaf70LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf70CoverageChecked :
    coverageCheck (innerAD leaf70Box) leaf70InnerLog = true := by
  rfl'

private theorem leaf70InnerLogValid :
    leaf70InnerLog.Valid 8 (innerAD leaf70Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf70CoverageChecked

private noncomputable def leaf70InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf70InputLogOnePlusV_eq :
    leaf70InputLogOnePlusV = outerEnclosure 24
      (leaf70Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf70RoundedFacts : LeafRoundedFacts 8
    leaf70Certificate.logOnePlusV leaf70InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf70InputLogOnePlusV_eq }

private noncomputable def leaf70Inputs : Inputs :=
  inputsOfCaches globalInput sk14RoundedInputs
    chi18InputQChi innerPair27Input
    leaf70InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf70LowerChecked :
    lowerCheck 24 leaf70Box leaf70Inputs = true := by
  rfl'

private theorem leaf70CoversExact : CoversExact 8
    leaf70Box leaf70Certificate leaf70InnerLog leaf70Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk14RoundedFacts chi18RoundedFacts
    innerPair27RoundedFacts leaf70RoundedFacts (by rfl)

private theorem leaf70FlatSound : Sound leaf70Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf70CertificateValid
    leaf70InnerLogValid leaf70CoversExact leaf70LowerChecked

private noncomputable def component1Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node0_sound : Sound component1Node0Box :=
  sound_of_literal_split component1Node0Box leaf22Box leaf23Box
    .k (9/16) (by rfl) (by rfl)
    leaf22FlatSound leaf23FlatSound

private noncomputable def component1Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node1_sound : Sound component1Node1Box :=
  sound_of_literal_split component1Node1Box leaf21Box component1Node0Box
    .chi (1/8) (by rfl) (by rfl)
    leaf21FlatSound component1Node0_sound

private noncomputable def component1Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component1Node2_sound : Sound component1Node2Box :=
  sound_of_literal_split component1Node2Box leaf25Box leaf26Box
    .k (11/16) (by rfl) (by rfl)
    leaf25FlatSound leaf26FlatSound

private noncomputable def component1Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node3_sound : Sound component1Node3Box :=
  sound_of_literal_split component1Node3Box leaf27Box leaf28Box
    .k (11/16) (by rfl) (by rfl)
    leaf27FlatSound leaf28FlatSound

private noncomputable def component1Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node4_sound : Sound component1Node4Box :=
  sound_of_literal_split component1Node4Box component1Node2Box component1Node3Box
    .chi (3/16) (by rfl) (by rfl)
    component1Node2_sound component1Node3_sound

private noncomputable def component1Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node5_sound : Sound component1Node5Box :=
  sound_of_literal_split component1Node5Box leaf24Box component1Node4Box
    .chi (1/8) (by rfl) (by rfl)
    leaf24FlatSound component1Node4_sound

private noncomputable def component1Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (3/4), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node6_sound : Sound component1Node6Box :=
  sound_of_literal_split component1Node6Box component1Node1Box component1Node5Box
    .k (5/8) (by rfl) (by rfl)
    component1Node1_sound component1Node5_sound

private noncomputable def component1Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node7_sound : Sound component1Node7Box :=
  sound_of_literal_split component1Node7Box leaf30Box leaf31Box
    .chi (3/32) (by rfl) (by rfl)
    leaf30FlatSound leaf31FlatSound

private noncomputable def component1Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node8_sound : Sound component1Node8Box :=
  sound_of_literal_split component1Node8Box leaf29Box component1Node7Box
    .chi (1/16) (by rfl) (by rfl)
    leaf29FlatSound component1Node7_sound

private noncomputable def component1Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node9_sound : Sound component1Node9Box :=
  sound_of_literal_split component1Node9Box leaf34Box leaf35Box
    .k (15/16) (by rfl) (by rfl)
    leaf34FlatSound leaf35FlatSound

private noncomputable def component1Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node10_sound : Sound component1Node10Box :=
  sound_of_literal_split component1Node10Box leaf33Box component1Node9Box
    .chi (3/32) (by rfl) (by rfl)
    leaf33FlatSound component1Node9_sound

private noncomputable def component1Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node11_sound : Sound component1Node11Box :=
  sound_of_literal_split component1Node11Box leaf32Box component1Node10Box
    .chi (1/16) (by rfl) (by rfl)
    leaf32FlatSound component1Node10_sound

private noncomputable def component1Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node12_sound : Sound component1Node12Box :=
  sound_of_literal_split component1Node12Box component1Node8Box component1Node11Box
    .k (7/8) (by rfl) (by rfl)
    component1Node8_sound component1Node11_sound

private noncomputable def component1Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component1Node13_sound : Sound component1Node13Box :=
  sound_of_literal_split component1Node13Box leaf36Box leaf37Box
    .k (13/16) (by rfl) (by rfl)
    leaf36FlatSound leaf37FlatSound

private noncomputable def component1Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node14_sound : Sound component1Node14Box :=
  sound_of_literal_split component1Node14Box leaf38Box leaf39Box
    .k (13/16) (by rfl) (by rfl)
    leaf38FlatSound leaf39FlatSound

private noncomputable def component1Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node15_sound : Sound component1Node15Box :=
  sound_of_literal_split component1Node15Box component1Node13Box component1Node14Box
    .chi (3/16) (by rfl) (by rfl)
    component1Node13_sound component1Node14_sound

private noncomputable def component1Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component1Node16_sound : Sound component1Node16Box :=
  sound_of_literal_split component1Node16Box leaf40Box leaf41Box
    .k (15/16) (by rfl) (by rfl)
    leaf40FlatSound leaf41FlatSound

private noncomputable def component1Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node17_sound : Sound component1Node17Box :=
  sound_of_literal_split component1Node17Box leaf42Box leaf43Box
    .k (15/16) (by rfl) (by rfl)
    leaf42FlatSound leaf43FlatSound

private noncomputable def component1Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node18_sound : Sound component1Node18Box :=
  sound_of_literal_split component1Node18Box component1Node16Box component1Node17Box
    .chi (3/16) (by rfl) (by rfl)
    component1Node16_sound component1Node17_sound

private noncomputable def component1Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node19_sound : Sound component1Node19Box :=
  sound_of_literal_split component1Node19Box component1Node15Box component1Node18Box
    .k (7/8) (by rfl) (by rfl)
    component1Node15_sound component1Node18_sound

private noncomputable def component1Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node20_sound : Sound component1Node20Box :=
  sound_of_literal_split component1Node20Box component1Node12Box component1Node19Box
    .chi (1/8) (by rfl) (by rfl)
    component1Node12_sound component1Node19_sound

private noncomputable def component1Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (1), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component1Node21_sound : Sound component1Node21Box :=
  sound_of_literal_split component1Node21Box component1Node6Box component1Node20Box
    .k (3/4) (by rfl) (by rfl)
    component1Node6_sound component1Node20_sound

private noncomputable def component1Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node22_sound : Sound component1Node22Box :=
  sound_of_literal_split component1Node22Box leaf44Box leaf45Box
    .k (9/16) (by rfl) (by rfl)
    leaf44FlatSound leaf45FlatSound

private noncomputable def component1Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node23_sound : Sound component1Node23Box :=
  sound_of_literal_split component1Node23Box leaf46Box leaf47Box
    .k (9/16) (by rfl) (by rfl)
    leaf46FlatSound leaf47FlatSound

private noncomputable def component1Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (5/8), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node24_sound : Sound component1Node24Box :=
  sound_of_literal_split component1Node24Box component1Node22Box component1Node23Box
    .chi (3/8) (by rfl) (by rfl)
    component1Node22_sound component1Node23_sound

private noncomputable def component1Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (11/16), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node25_sound : Sound component1Node25Box :=
  sound_of_literal_split component1Node25Box leaf48Box leaf49Box
    .chi (5/16) (by rfl) (by rfl)
    leaf48FlatSound leaf49FlatSound

private noncomputable def component1Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node26_sound : Sound component1Node26Box :=
  sound_of_literal_split component1Node26Box leaf50Box leaf51Box
    .chi (5/16) (by rfl) (by rfl)
    leaf50FlatSound leaf51FlatSound

private noncomputable def component1Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node27_sound : Sound component1Node27Box :=
  sound_of_literal_split component1Node27Box component1Node25Box component1Node26Box
    .k (11/16) (by rfl) (by rfl)
    component1Node25_sound component1Node26_sound

private noncomputable def component1Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/16), kHi := (3/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node28_sound : Sound component1Node28Box :=
  sound_of_literal_split component1Node28Box leaf53Box leaf54Box
    .chi (7/16) (by rfl) (by rfl)
    leaf53FlatSound leaf54FlatSound

private noncomputable def component1Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node29_sound : Sound component1Node29Box :=
  sound_of_literal_split component1Node29Box leaf52Box component1Node28Box
    .k (11/16) (by rfl) (by rfl)
    leaf52FlatSound component1Node28_sound

private noncomputable def component1Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/8), kHi := (3/4), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node30_sound : Sound component1Node30Box :=
  sound_of_literal_split component1Node30Box component1Node27Box component1Node29Box
    .chi (3/8) (by rfl) (by rfl)
    component1Node27_sound component1Node29_sound

private noncomputable def component1Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (3/4), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node31_sound : Sound component1Node31Box :=
  sound_of_literal_split component1Node31Box component1Node24Box component1Node30Box
    .k (5/8) (by rfl) (by rfl)
    component1Node24_sound component1Node30_sound

private noncomputable def component1Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node32_sound : Sound component1Node32Box :=
  sound_of_literal_split component1Node32Box leaf55Box leaf56Box
    .chi (5/16) (by rfl) (by rfl)
    leaf55FlatSound leaf56FlatSound

private noncomputable def component1Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node33_sound : Sound component1Node33Box :=
  sound_of_literal_split component1Node33Box leaf57Box leaf58Box
    .chi (5/16) (by rfl) (by rfl)
    leaf57FlatSound leaf58FlatSound

private noncomputable def component1Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node34_sound : Sound component1Node34Box :=
  sound_of_literal_split component1Node34Box component1Node32Box component1Node33Box
    .k (13/16) (by rfl) (by rfl)
    component1Node32_sound component1Node33_sound

private noncomputable def component1Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component1Node35_sound : Sound component1Node35Box :=
  sound_of_literal_split component1Node35Box leaf59Box leaf60Box
    .k (15/16) (by rfl) (by rfl)
    leaf59FlatSound leaf60FlatSound

private noncomputable def component1Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node36_sound : Sound component1Node36Box :=
  sound_of_literal_split component1Node36Box leaf61Box leaf62Box
    .k (15/16) (by rfl) (by rfl)
    leaf61FlatSound leaf62FlatSound

private noncomputable def component1Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node37_sound : Sound component1Node37Box :=
  sound_of_literal_split component1Node37Box component1Node35Box component1Node36Box
    .chi (5/16) (by rfl) (by rfl)
    component1Node35_sound component1Node36_sound

private noncomputable def component1Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component1Node38_sound : Sound component1Node38Box :=
  sound_of_literal_split component1Node38Box component1Node34Box component1Node37Box
    .k (7/8) (by rfl) (by rfl)
    component1Node34_sound component1Node37_sound

private noncomputable def component1Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (13/16), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node39_sound : Sound component1Node39Box :=
  sound_of_literal_split component1Node39Box leaf63Box leaf64Box
    .chi (7/16) (by rfl) (by rfl)
    leaf63FlatSound leaf64FlatSound

private noncomputable def component1Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/16), kHi := (7/8), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node40_sound : Sound component1Node40Box :=
  sound_of_literal_split component1Node40Box leaf65Box leaf66Box
    .chi (7/16) (by rfl) (by rfl)
    leaf65FlatSound leaf66FlatSound

private noncomputable def component1Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (7/8), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node41_sound : Sound component1Node41Box :=
  sound_of_literal_split component1Node41Box component1Node39Box component1Node40Box
    .k (13/16) (by rfl) (by rfl)
    component1Node39_sound component1Node40_sound

private noncomputable def component1Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component1Node42_sound : Sound component1Node42Box :=
  sound_of_literal_split component1Node42Box leaf67Box leaf68Box
    .k (15/16) (by rfl) (by rfl)
    leaf67FlatSound leaf68FlatSound

private noncomputable def component1Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node43_sound : Sound component1Node43Box :=
  sound_of_literal_split component1Node43Box leaf69Box leaf70Box
    .k (15/16) (by rfl) (by rfl)
    leaf69FlatSound leaf70FlatSound

private noncomputable def component1Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/8), kHi := (1), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node44_sound : Sound component1Node44Box :=
  sound_of_literal_split component1Node44Box component1Node42Box component1Node43Box
    .chi (7/16) (by rfl) (by rfl)
    component1Node42_sound component1Node43_sound

private noncomputable def component1Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node45_sound : Sound component1Node45Box :=
  sound_of_literal_split component1Node45Box component1Node41Box component1Node44Box
    .k (7/8) (by rfl) (by rfl)
    component1Node41_sound component1Node44_sound

private noncomputable def component1Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/4), kHi := (1), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node46_sound : Sound component1Node46Box :=
  sound_of_literal_split component1Node46Box component1Node38Box component1Node45Box
    .chi (3/8) (by rfl) (by rfl)
    component1Node38_sound component1Node45_sound

private noncomputable def component1Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (1), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component1Node47_sound : Sound component1Node47Box :=
  sound_of_literal_split component1Node47Box component1Node31Box component1Node46Box
    .k (3/4) (by rfl) (by rfl)
    component1Node31_sound component1Node46_sound

noncomputable def component1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (1), chiLo := (0), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component1_sound : Sound component1Box :=
  sound_of_literal_split component1Box component1Node21Box component1Node47Box
    .chi (1/4) (by rfl) (by rfl)
    component1Node21_sound component1Node47_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
