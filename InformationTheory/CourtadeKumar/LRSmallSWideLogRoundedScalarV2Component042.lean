import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf1870Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1870Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214219) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (757025367/536870912) }, upper := { exponent := 0, mantissa := (11701/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432075/268428438) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1870InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1870LocalValidity :
    LeafFacts leaf1870Box leaf1870Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1870Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214219) }) = true
      norm_num [leaf1870Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1870CertificateValid :
    WideCertificateValid leaf1870Box leaf1870Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi155ValidityFacts
    leaf1870LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1870CoverageChecked :
    coverageCheck (innerAD leaf1870Box) leaf1870InnerLog = true := by
  rfl'

private theorem leaf1870InnerLogValid :
    leaf1870InnerLog.Valid 8 (innerAD leaf1870Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1870CoverageChecked

private noncomputable def leaf1870InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1870InputLogOnePlusV_eq :
    leaf1870InputLogOnePlusV = outerEnclosure 24
      (leaf1870Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1870RoundedFacts : LeafRoundedFacts 8
    leaf1870Certificate.logOnePlusV leaf1870InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1870InputLogOnePlusV_eq }

private noncomputable def leaf1870Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1870InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1870LowerChecked :
    lowerCheck 24 leaf1870Box leaf1870Inputs = true := by
  rfl'

private theorem leaf1870CoversExact : CoversExact 8
    leaf1870Box leaf1870Certificate leaf1870InnerLog leaf1870Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1870RoundedFacts (by rfl)

private theorem leaf1870FlatSound : Sound leaf1870Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1870CertificateValid
    leaf1870InnerLogValid leaf1870CoversExact leaf1870LowerChecked

private noncomputable def leaf1871Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1871Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107095) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (758860261/536870912) }, upper := { exponent := 0, mantissa := (5865/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216023/134214190) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1871InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1871LocalValidity :
    LeafFacts leaf1871Box leaf1871Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1871Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107095) }) = true
      norm_num [leaf1871Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1871CertificateValid :
    WideCertificateValid leaf1871Box leaf1871Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi155ValidityFacts
    leaf1871LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1871CoverageChecked :
    coverageCheck (innerAD leaf1871Box) leaf1871InnerLog = true := by
  rfl'

private theorem leaf1871InnerLogValid :
    leaf1871InnerLog.Valid 8 (innerAD leaf1871Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1871CoverageChecked

private noncomputable def leaf1871InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814655/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1871InputLogOnePlusV_eq :
    leaf1871InputLogOnePlusV = outerEnclosure 24
      (leaf1871Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1871RoundedFacts : LeafRoundedFacts 8
    leaf1871Certificate.logOnePlusV leaf1871InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1871InputLogOnePlusV_eq }

private noncomputable def leaf1871Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1871InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1871LowerChecked :
    lowerCheck 24 leaf1871Box leaf1871Inputs = true := by
  rfl'

private theorem leaf1871CoversExact : CoversExact 8
    leaf1871Box leaf1871Certificate leaf1871InnerLog leaf1871Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1871RoundedFacts (by rfl)

private theorem leaf1871FlatSound : Sound leaf1871Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1871CertificateValid
    leaf1871InnerLogValid leaf1871CoversExact leaf1871LowerChecked

private noncomputable def leaf1872Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1872Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107049) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (764889205/536870912) }, upper := { exponent := 0, mantissa := (5911/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215977/134214098) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1872InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1872LocalValidity :
    LeafFacts leaf1872Box leaf1872Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1872Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107049) }) = true
      norm_num [leaf1872Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1872CertificateValid :
    WideCertificateValid leaf1872Box leaf1872Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi156ValidityFacts
    leaf1872LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1872CoverageChecked :
    coverageCheck (innerAD leaf1872Box) leaf1872InnerLog = true := by
  rfl'

private theorem leaf1872InnerLogValid :
    leaf1872InnerLog.Valid 8 (innerAD leaf1872Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1872CoverageChecked

private noncomputable def leaf1872InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1872InputLogOnePlusV_eq :
    leaf1872InputLogOnePlusV = outerEnclosure 24
      (leaf1872Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1872RoundedFacts : LeafRoundedFacts 8
    leaf1872Certificate.logOnePlusV leaf1872InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1872InputLogOnePlusV_eq }

private noncomputable def leaf1872Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi156InputQChi innerPair405Input
    leaf1872InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1872LowerChecked :
    lowerCheck 24 leaf1872Box leaf1872Inputs = true := by
  rfl'

private theorem leaf1872CoversExact : CoversExact 8
    leaf1872Box leaf1872Certificate leaf1872InnerLog leaf1872Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi156RoundedFacts
    innerPair405RoundedFacts leaf1872RoundedFacts (by rfl)

private theorem leaf1872FlatSound : Sound leaf1872Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1872CertificateValid
    leaf1872InnerLogValid leaf1872CoversExact leaf1872LowerChecked

private noncomputable def leaf1873Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1873Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553517) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (766789631/536870912) }, upper := { exponent := 0, mantissa := (2963/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107981/67107034) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1873InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1873LocalValidity :
    LeafFacts leaf1873Box leaf1873Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1873Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553517) }) = true
      norm_num [leaf1873Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1873CertificateValid :
    WideCertificateValid leaf1873Box leaf1873Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi156ValidityFacts
    leaf1873LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1873CoverageChecked :
    coverageCheck (innerAD leaf1873Box) leaf1873InnerLog = true := by
  rfl'

private theorem leaf1873InnerLogValid :
    leaf1873InnerLog.Valid 8 (innerAD leaf1873Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1873CoverageChecked

private noncomputable def leaf1873InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1873InputLogOnePlusV_eq :
    leaf1873InputLogOnePlusV = outerEnclosure 24
      (leaf1873Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1873RoundedFacts : LeafRoundedFacts 8
    leaf1873Certificate.logOnePlusV leaf1873InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1873InputLogOnePlusV_eq }

private noncomputable def leaf1873Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi156InputQChi innerPair405Input
    leaf1873InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1873LowerChecked :
    lowerCheck 24 leaf1873Box leaf1873Inputs = true := by
  rfl'

private theorem leaf1873CoversExact : CoversExact 8
    leaf1873Box leaf1873Certificate leaf1873InnerLog leaf1873Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi156RoundedFacts
    innerPair405RoundedFacts leaf1873RoundedFacts (by rfl)

private theorem leaf1873FlatSound : Sound leaf1873Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1873CertificateValid
    leaf1873InnerLogValid leaf1873CoversExact leaf1873LowerChecked

private noncomputable def leaf1874Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1874Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214161) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (760695155/536870912) }, upper := { exponent := 0, mantissa := (11759/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432017/268428322) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1874InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1874LocalValidity :
    LeafFacts leaf1874Box leaf1874Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1874Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214161) }) = true
      norm_num [leaf1874Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1874CertificateValid :
    WideCertificateValid leaf1874Box leaf1874Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi155ValidityFacts
    leaf1874LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1874CoverageChecked :
    coverageCheck (innerAD leaf1874Box) leaf1874InnerLog = true := by
  rfl'

private theorem leaf1874InnerLogValid :
    leaf1874InnerLog.Valid 8 (innerAD leaf1874Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1874CoverageChecked

private noncomputable def leaf1874InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf1874InputLogOnePlusV_eq :
    leaf1874InputLogOnePlusV = outerEnclosure 24
      (leaf1874Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1874RoundedFacts : LeafRoundedFacts 8
    leaf1874Certificate.logOnePlusV leaf1874InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1874InputLogOnePlusV_eq }

private noncomputable def leaf1874Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1874InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1874LowerChecked :
    lowerCheck 24 leaf1874Box leaf1874Inputs = true := by
  rfl'

private theorem leaf1874CoversExact : CoversExact 8
    leaf1874Box leaf1874Certificate leaf1874InnerLog leaf1874Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1874RoundedFacts (by rfl)

private theorem leaf1874FlatSound : Sound leaf1874Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1874CertificateValid
    leaf1874InnerLogValid leaf1874CoversExact leaf1874LowerChecked

private noncomputable def leaf1875Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1875Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871217/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553533) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (762530049/536870912) }, upper := { exponent := 0, mantissa := (2947/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107997/67107066) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1875InnerLog : WideLogData :=
  innerPair444Data

set_option maxRecDepth 1000000 in
private theorem leaf1875LocalValidity :
    LeafFacts leaf1875Box leaf1875Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1875Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553533) }) = true
      norm_num [leaf1875Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1875CertificateValid :
    WideCertificateValid leaf1875Box leaf1875Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi155ValidityFacts
    leaf1875LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1875CoverageChecked :
    coverageCheck (innerAD leaf1875Box) leaf1875InnerLog = true := by
  rfl'

private theorem leaf1875InnerLogValid :
    leaf1875InnerLog.Valid 8 (innerAD leaf1875Box) :=
  wideLogDataValid_of_cachedCheck endpoint157PositiveFacts
    endpoint109PositiveFacts.valid leaf1875CoverageChecked

private noncomputable def leaf1875InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1875InputLogOnePlusV_eq :
    leaf1875InputLogOnePlusV = outerEnclosure 24
      (leaf1875Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1875RoundedFacts : LeafRoundedFacts 8
    leaf1875Certificate.logOnePlusV leaf1875InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1875InputLogOnePlusV_eq }

private noncomputable def leaf1875Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi155InputQChi innerPair444Input
    leaf1875InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1875LowerChecked :
    lowerCheck 24 leaf1875Box leaf1875Inputs = true := by
  rfl'

private theorem leaf1875CoversExact : CoversExact 8
    leaf1875Box leaf1875Certificate leaf1875InnerLog leaf1875Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi155RoundedFacts
    innerPair444RoundedFacts leaf1875RoundedFacts (by rfl)

private theorem leaf1875FlatSound : Sound leaf1875Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1875CertificateValid
    leaf1875InnerLogValid leaf1875CoversExact leaf1875LowerChecked

private noncomputable def leaf1876Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1876Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871217/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107019) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (768690057/536870912) }, upper := { exponent := 0, mantissa := (5941/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215947/134214038) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1876InnerLog : WideLogData :=
  innerPair445Data

set_option maxRecDepth 1000000 in
private theorem leaf1876LocalValidity :
    LeafFacts leaf1876Box leaf1876Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1876Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107019) }) = true
      norm_num [leaf1876Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1876CertificateValid :
    WideCertificateValid leaf1876Box leaf1876Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi156ValidityFacts
    leaf1876LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1876CoverageChecked :
    coverageCheck (innerAD leaf1876Box) leaf1876InnerLog = true := by
  rfl'

private theorem leaf1876InnerLogValid :
    leaf1876InnerLog.Valid 8 (innerAD leaf1876Box) :=
  wideLogDataValid_of_cachedCheck endpoint158PositiveFacts
    endpoint159PositiveFacts.valid leaf1876CoverageChecked

private noncomputable def leaf1876InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1876InputLogOnePlusV_eq :
    leaf1876InputLogOnePlusV = outerEnclosure 24
      (leaf1876Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1876RoundedFacts : LeafRoundedFacts 8
    leaf1876Certificate.logOnePlusV leaf1876InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1876InputLogOnePlusV_eq }

private noncomputable def leaf1876Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi156InputQChi innerPair445Input
    leaf1876InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1876LowerChecked :
    lowerCheck 24 leaf1876Box leaf1876Inputs = true := by
  rfl'

private theorem leaf1876CoversExact : CoversExact 8
    leaf1876Box leaf1876Certificate leaf1876InnerLog leaf1876Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi156RoundedFacts
    innerPair445RoundedFacts leaf1876RoundedFacts (by rfl)

private theorem leaf1876FlatSound : Sound leaf1876Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1876CertificateValid
    leaf1876InnerLogValid leaf1876CoversExact leaf1876LowerChecked

private noncomputable def leaf1877Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (29/256), chiHi := (59/512) }

private noncomputable def leaf1877Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742189/1073741824) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107035) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1541213981/1073741824) }, upper := { exponent := 0, mantissa := (5925/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi167LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215963/134214070) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1877InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1877LocalValidity :
    LeafFacts leaf1877Box leaf1877Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1877Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107035) }) = true
      norm_num [leaf1877Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1877CertificateValid :
    WideCertificateValid leaf1877Box leaf1877Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi167ValidityFacts
    leaf1877LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1877CoverageChecked :
    coverageCheck (innerAD leaf1877Box) leaf1877InnerLog = true := by
  rfl'

private theorem leaf1877InnerLogValid :
    leaf1877InnerLog.Valid 8 (innerAD leaf1877Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1877CoverageChecked

private noncomputable def leaf1877InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1877InputLogOnePlusV_eq :
    leaf1877InputLogOnePlusV = outerEnclosure 24
      (leaf1877Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1877RoundedFacts : LeafRoundedFacts 8
    leaf1877Certificate.logOnePlusV leaf1877InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1877InputLogOnePlusV_eq }

private noncomputable def leaf1877Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi167InputQChi innerPair27Input
    leaf1877InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1877LowerChecked :
    lowerCheck 24 leaf1877Box leaf1877Inputs = true := by
  rfl'

private theorem leaf1877CoversExact : CoversExact 8
    leaf1877Box leaf1877Certificate leaf1877InnerLog leaf1877Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi167RoundedFacts
    innerPair27RoundedFacts leaf1877RoundedFacts (by rfl)

private theorem leaf1877FlatSound : Sound leaf1877Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1877CertificateValid
    leaf1877InnerLogValid leaf1877CoversExact leaf1877LowerChecked

private noncomputable def leaf1878Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (59/512), chiHi := (15/128) }

private noncomputable def leaf1878Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776751) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1549274415/1073741824) }, upper := { exponent := 0, mantissa := (1489/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi168LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33553983/33553502) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1878InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1878LocalValidity :
    LeafFacts leaf1878Box leaf1878Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1878Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776751) }) = true
      norm_num [leaf1878Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1878CertificateValid :
    WideCertificateValid leaf1878Box leaf1878Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi168ValidityFacts
    leaf1878LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1878CoverageChecked :
    coverageCheck (innerAD leaf1878Box) leaf1878InnerLog = true := by
  rfl'

private theorem leaf1878InnerLogValid :
    leaf1878InnerLog.Valid 8 (innerAD leaf1878Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1878CoverageChecked

private noncomputable def leaf1878InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1878InputLogOnePlusV_eq :
    leaf1878InputLogOnePlusV = outerEnclosure 24
      (leaf1878Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1878RoundedFacts : LeafRoundedFacts 8
    leaf1878Certificate.logOnePlusV leaf1878InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1878InputLogOnePlusV_eq }

private noncomputable def leaf1878Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi168InputQChi innerPair34Input
    leaf1878InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1878LowerChecked :
    lowerCheck 24 leaf1878Box leaf1878Inputs = true := by
  rfl'

private theorem leaf1878CoversExact : CoversExact 8
    leaf1878Box leaf1878Certificate leaf1878InnerLog leaf1878Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi168RoundedFacts
    innerPair34RoundedFacts leaf1878RoundedFacts (by rfl)

private theorem leaf1878FlatSound : Sound leaf1878Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1878CertificateValid
    leaf1878InnerLogValid leaf1878CoversExact leaf1878LowerChecked

private noncomputable def leaf1879Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1879Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213977) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (772753043/536870912) }, upper := { exponent := 0, mantissa := (11943/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431833/268427954) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1879InnerLog : WideLogData :=
  innerPair39Data

set_option maxRecDepth 1000000 in
private theorem leaf1879LocalValidity :
    LeafFacts leaf1879Box leaf1879Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1879Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213977) }) = true
      norm_num [leaf1879Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1879CertificateValid :
    WideCertificateValid leaf1879Box leaf1879Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi153ValidityFacts
    leaf1879LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1879CoverageChecked :
    coverageCheck (innerAD leaf1879Box) leaf1879InnerLog = true := by
  rfl'

private theorem leaf1879InnerLogValid :
    leaf1879InnerLog.Valid 8 (innerAD leaf1879Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint160PositiveFacts.valid leaf1879CoverageChecked

private noncomputable def leaf1879InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1879InputLogOnePlusV_eq :
    leaf1879InputLogOnePlusV = outerEnclosure 24
      (leaf1879Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1879RoundedFacts : LeafRoundedFacts 8
    leaf1879Certificate.logOnePlusV leaf1879InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1879InputLogOnePlusV_eq }

private noncomputable def leaf1879Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi153InputQChi innerPair39Input
    leaf1879InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1879LowerChecked :
    lowerCheck 24 leaf1879Box leaf1879Inputs = true := by
  rfl'

private theorem leaf1879CoversExact : CoversExact 8
    leaf1879Box leaf1879Certificate leaf1879InnerLog leaf1879Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi153RoundedFacts
    innerPair39RoundedFacts leaf1879RoundedFacts (by rfl)

private theorem leaf1879FlatSound : Sound leaf1879Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1879CertificateValid
    leaf1879InnerLogValid leaf1879CoversExact leaf1879LowerChecked

private noncomputable def leaf1880Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (15/128), chiHi := (61/512) }

private noncomputable def leaf1880Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742189/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214007) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1549471013/1073741824) }, upper := { exponent := 0, mantissa := (11913/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi169LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431863/268428014) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1880InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1880LocalValidity :
    LeafFacts leaf1880Box leaf1880Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1880Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214007) }) = true
      norm_num [leaf1880Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1880CertificateValid :
    WideCertificateValid leaf1880Box leaf1880Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi169ValidityFacts
    leaf1880LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1880CoverageChecked :
    coverageCheck (innerAD leaf1880Box) leaf1880InnerLog = true := by
  rfl'

private theorem leaf1880InnerLogValid :
    leaf1880InnerLog.Valid 8 (innerAD leaf1880Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1880CoverageChecked

private noncomputable def leaf1880InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1880InputLogOnePlusV_eq :
    leaf1880InputLogOnePlusV = outerEnclosure 24
      (leaf1880Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1880RoundedFacts : LeafRoundedFacts 8
    leaf1880Certificate.logOnePlusV leaf1880InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1880InputLogOnePlusV_eq }

private noncomputable def leaf1880Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi169InputQChi innerPair34Input
    leaf1880InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1880LowerChecked :
    lowerCheck 24 leaf1880Box leaf1880Inputs = true := by
  rfl'

private theorem leaf1880CoversExact : CoversExact 8
    leaf1880Box leaf1880Certificate leaf1880InnerLog leaf1880Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi169RoundedFacts
    innerPair34RoundedFacts leaf1880RoundedFacts (by rfl)

private theorem leaf1880FlatSound : Sound leaf1880Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1880CertificateValid
    leaf1880InnerLogValid leaf1880CoversExact leaf1880LowerChecked

private noncomputable def leaf1881Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (61/512), chiHi := (31/256) }

private noncomputable def leaf1881Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3947584/3947469) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1557400383/1073741824) }, upper := { exponent := 0, mantissa := (5987/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi170LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (7895053/7894938) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1881InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1881LocalValidity :
    LeafFacts leaf1881Box leaf1881Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1881Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3947584/3947469) }) = true
      norm_num [leaf1881Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1881CertificateValid :
    WideCertificateValid leaf1881Box leaf1881Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi170ValidityFacts
    leaf1881LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1881CoverageChecked :
    coverageCheck (innerAD leaf1881Box) leaf1881InnerLog = true := by
  rfl'

private theorem leaf1881InnerLogValid :
    leaf1881InnerLog.Valid 8 (innerAD leaf1881Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1881CoverageChecked

private noncomputable def leaf1881InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1881InputLogOnePlusV_eq :
    leaf1881InputLogOnePlusV = outerEnclosure 24
      (leaf1881Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1881RoundedFacts : LeafRoundedFacts 8
    leaf1881Certificate.logOnePlusV leaf1881InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1881InputLogOnePlusV_eq }

private noncomputable def leaf1881Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi170InputQChi innerPair34Input
    leaf1881InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1881LowerChecked :
    lowerCheck 24 leaf1881Box leaf1881Inputs = true := by
  rfl'

private theorem leaf1881CoversExact : CoversExact 8
    leaf1881Box leaf1881Certificate leaf1881InnerLog leaf1881Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi170RoundedFacts
    innerPair34RoundedFacts leaf1881RoundedFacts (by rfl)

private theorem leaf1881FlatSound : Sound leaf1881Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1881CertificateValid
    leaf1881InnerLogValid leaf1881CoversExact leaf1881LowerChecked

private noncomputable def leaf1882Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1882Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427833) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1561266771/1073741824) }, upper := { exponent := 0, mantissa := (24007/16384) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863545/536855666) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1882InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1882LocalValidity :
    LeafFacts leaf1882Box leaf1882Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1882Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427833) }) = true
      norm_num [leaf1882Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1882CertificateValid :
    WideCertificateValid leaf1882Box leaf1882Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi171ValidityFacts
    leaf1882LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1882CoverageChecked :
    coverageCheck (innerAD leaf1882Box) leaf1882InnerLog = true := by
  rfl'

private theorem leaf1882InnerLogValid :
    leaf1882InnerLog.Valid 8 (innerAD leaf1882Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1882CoverageChecked

private noncomputable def leaf1882InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1882InputLogOnePlusV_eq :
    leaf1882InputLogOnePlusV = outerEnclosure 24
      (leaf1882Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1882RoundedFacts : LeafRoundedFacts 8
    leaf1882Certificate.logOnePlusV leaf1882InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1882InputLogOnePlusV_eq }

private noncomputable def leaf1882Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1882InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1882LowerChecked :
    lowerCheck 24 leaf1882Box leaf1882Inputs = true := by
  rfl'

private theorem leaf1882CoversExact : CoversExact 8
    leaf1882Box leaf1882Certificate leaf1882InnerLog leaf1882Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1882RoundedFacts (by rfl)

private theorem leaf1882FlatSound : Sound leaf1882Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1882CertificateValid
    leaf1882InnerLogValid leaf1882CoversExact leaf1882LowerChecked

private noncomputable def leaf1883Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1883Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194183) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1569130609/1073741824) }, upper := { exponent := 0, mantissa := (377/256) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388491/8388366) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1883InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1883LocalValidity :
    LeafFacts leaf1883Box leaf1883Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1883Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194183) }) = true
      norm_num [leaf1883Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1883CertificateValid :
    WideCertificateValid leaf1883Box leaf1883Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi172ValidityFacts
    leaf1883LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1883CoverageChecked :
    coverageCheck (innerAD leaf1883Box) leaf1883InnerLog = true := by
  rfl'

private theorem leaf1883InnerLogValid :
    leaf1883InnerLog.Valid 8 (innerAD leaf1883Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1883CoverageChecked

private noncomputable def leaf1883InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1883InputLogOnePlusV_eq :
    leaf1883InputLogOnePlusV = outerEnclosure 24
      (leaf1883Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1883RoundedFacts : LeafRoundedFacts 8
    leaf1883Certificate.logOnePlusV leaf1883InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1883InputLogOnePlusV_eq }

private noncomputable def leaf1883Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1883InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1883LowerChecked :
    lowerCheck 24 leaf1883Box leaf1883Inputs = true := by
  rfl'

private theorem leaf1883CoversExact : CoversExact 8
    leaf1883Box leaf1883Certificate leaf1883InnerLog leaf1883Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1883RoundedFacts (by rfl)

private theorem leaf1883FlatSound : Sound leaf1883Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1883CertificateValid
    leaf1883InnerLogValid leaf1883CoversExact leaf1883LowerChecked

private noncomputable def leaf1884Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1884Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213885) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1565329753/1073741824) }, upper := { exponent := 0, mantissa := (12035/8192) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431741/268427770) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1884InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1884LocalValidity :
    LeafFacts leaf1884Box leaf1884Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1884Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213885) }) = true
      norm_num [leaf1884Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1884CertificateValid :
    WideCertificateValid leaf1884Box leaf1884Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi171ValidityFacts
    leaf1884LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1884CoverageChecked :
    coverageCheck (innerAD leaf1884Box) leaf1884InnerLog = true := by
  rfl'

private theorem leaf1884InnerLogValid :
    leaf1884InnerLog.Valid 8 (innerAD leaf1884Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1884CoverageChecked

private noncomputable def leaf1884InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1884InputLogOnePlusV_eq :
    leaf1884InputLogOnePlusV = outerEnclosure 24
      (leaf1884Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1884RoundedFacts : LeafRoundedFacts 8
    leaf1884Certificate.logOnePlusV leaf1884InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1884InputLogOnePlusV_eq }

private noncomputable def leaf1884Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1884InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1884LowerChecked :
    lowerCheck 24 leaf1884Box leaf1884Inputs = true := by
  rfl'

private theorem leaf1884CoversExact : CoversExact 8
    leaf1884Box leaf1884Certificate leaf1884InnerLog leaf1884Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1884RoundedFacts (by rfl)

private theorem leaf1884FlatSound : Sound leaf1884Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1884CertificateValid
    leaf1884InnerLogValid leaf1884CoversExact leaf1884LowerChecked

private noncomputable def leaf1885Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1885Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2097154/2097091) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1573259123/1073741824) }, upper := { exponent := 0, mantissa := (189/128) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4194245/4194182) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1885InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1885LocalValidity :
    LeafFacts leaf1885Box leaf1885Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1885Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2097154/2097091) }) = true
      norm_num [leaf1885Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1885CertificateValid :
    WideCertificateValid leaf1885Box leaf1885Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi172ValidityFacts
    leaf1885LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1885CoverageChecked :
    coverageCheck (innerAD leaf1885Box) leaf1885InnerLog = true := by
  rfl'

private theorem leaf1885InnerLogValid :
    leaf1885InnerLog.Valid 8 (innerAD leaf1885Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1885CoverageChecked

private noncomputable def leaf1885InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1885InputLogOnePlusV_eq :
    leaf1885InputLogOnePlusV = outerEnclosure 24
      (leaf1885Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1885RoundedFacts : LeafRoundedFacts 8
    leaf1885Certificate.logOnePlusV leaf1885InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1885InputLogOnePlusV_eq }

private noncomputable def leaf1885Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1885InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1885LowerChecked :
    lowerCheck 24 leaf1885Box leaf1885Inputs = true := by
  rfl'

private theorem leaf1885CoversExact : CoversExact 8
    leaf1885Box leaf1885Certificate leaf1885InnerLog leaf1885Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1885RoundedFacts (by rfl)

private theorem leaf1885FlatSound : Sound leaf1885Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1885CertificateValid
    leaf1885InnerLogValid leaf1885CoversExact leaf1885LowerChecked

private noncomputable def leaf1886Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (15/128), chiHi := (61/512) }

private noncomputable def leaf1886Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427953) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1553402931/1073741824) }, upper := { exponent := 0, mantissa := (23887/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi169LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863665/536855906) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1886InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1886LocalValidity :
    LeafFacts leaf1886Box leaf1886Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1886Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427953) }) = true
      norm_num [leaf1886Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1886CertificateValid :
    WideCertificateValid leaf1886Box leaf1886Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi169ValidityFacts
    leaf1886LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1886CoverageChecked :
    coverageCheck (innerAD leaf1886Box) leaf1886InnerLog = true := by
  rfl'

private theorem leaf1886InnerLogValid :
    leaf1886InnerLog.Valid 8 (innerAD leaf1886Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1886CoverageChecked

private noncomputable def leaf1886InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1886InputLogOnePlusV_eq :
    leaf1886InputLogOnePlusV = outerEnclosure 24
      (leaf1886Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1886RoundedFacts : LeafRoundedFacts 8
    leaf1886Certificate.logOnePlusV leaf1886InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1886InputLogOnePlusV_eq }

private noncomputable def leaf1886Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi169InputQChi innerPair34Input
    leaf1886InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1886LowerChecked :
    lowerCheck 24 leaf1886Box leaf1886Inputs = true := by
  rfl'

private theorem leaf1886CoversExact : CoversExact 8
    leaf1886Box leaf1886Certificate leaf1886InnerLog leaf1886Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi169RoundedFacts
    innerPair34RoundedFacts leaf1886RoundedFacts (by rfl)

private theorem leaf1886FlatSound : Sound leaf1886Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1886CertificateValid
    leaf1886InnerLogValid leaf1886CoversExact leaf1886LowerChecked

private noncomputable def leaf1887Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (61/512), chiHi := (31/256) }

private noncomputable def leaf1887Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213915) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1561397833/1073741824) }, upper := { exponent := 0, mantissa := (12005/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi170LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431771/268427830) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1887InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1887LocalValidity :
    LeafFacts leaf1887Box leaf1887Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1887Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213915) }) = true
      norm_num [leaf1887Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1887CertificateValid :
    WideCertificateValid leaf1887Box leaf1887Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi170ValidityFacts
    leaf1887LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1887CoverageChecked :
    coverageCheck (innerAD leaf1887Box) leaf1887InnerLog = true := by
  rfl'

private theorem leaf1887InnerLogValid :
    leaf1887InnerLog.Valid 8 (innerAD leaf1887Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1887CoverageChecked

private noncomputable def leaf1887InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1887InputLogOnePlusV_eq :
    leaf1887InputLogOnePlusV = outerEnclosure 24
      (leaf1887Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1887RoundedFacts : LeafRoundedFacts 8
    leaf1887Certificate.logOnePlusV leaf1887InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1887InputLogOnePlusV_eq }

private noncomputable def leaf1887Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi170InputQChi innerPair34Input
    leaf1887InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1887LowerChecked :
    lowerCheck 24 leaf1887Box leaf1887Inputs = true := by
  rfl'

private theorem leaf1887CoversExact : CoversExact 8
    leaf1887Box leaf1887Certificate leaf1887InnerLog leaf1887Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi170RoundedFacts
    innerPair34RoundedFacts leaf1887RoundedFacts (by rfl)

private theorem leaf1887FlatSound : Sound leaf1887Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1887CertificateValid
    leaf1887InnerLogValid leaf1887CoversExact leaf1887LowerChecked

private noncomputable def leaf1888Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (15/128), chiHi := (61/512) }

private noncomputable def leaf1888Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3947584/3947469) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1557334849/1073741824) }, upper := { exponent := 0, mantissa := (5987/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi169LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (7895053/7894938) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1888InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1888LocalValidity :
    LeafFacts leaf1888Box leaf1888Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1888Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3947584/3947469) }) = true
      norm_num [leaf1888Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1888CertificateValid :
    WideCertificateValid leaf1888Box leaf1888Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi169ValidityFacts
    leaf1888LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1888CoverageChecked :
    coverageCheck (innerAD leaf1888Box) leaf1888InnerLog = true := by
  rfl'

private theorem leaf1888InnerLogValid :
    leaf1888InnerLog.Valid 8 (innerAD leaf1888Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1888CoverageChecked

private noncomputable def leaf1888InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1888InputLogOnePlusV_eq :
    leaf1888InputLogOnePlusV = outerEnclosure 24
      (leaf1888Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1888RoundedFacts : LeafRoundedFacts 8
    leaf1888Certificate.logOnePlusV leaf1888InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1888InputLogOnePlusV_eq }

private noncomputable def leaf1888Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi169InputQChi innerPair34Input
    leaf1888InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1888LowerChecked :
    lowerCheck 24 leaf1888Box leaf1888Inputs = true := by
  rfl'

private theorem leaf1888CoversExact : CoversExact 8
    leaf1888Box leaf1888Certificate leaf1888InnerLog leaf1888Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi169RoundedFacts
    innerPair34RoundedFacts leaf1888RoundedFacts (by rfl)

private theorem leaf1888FlatSound : Sound leaf1888Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1888CertificateValid
    leaf1888InnerLogValid leaf1888CoversExact leaf1888LowerChecked

private noncomputable def leaf1889Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (61/512), chiHi := (31/256) }

private noncomputable def leaf1889Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553471) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1565395283/1073741824) }, upper := { exponent := 0, mantissa := (3009/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi170LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107935/67106942) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1889InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1889LocalValidity :
    LeafFacts leaf1889Box leaf1889Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1889Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553471) }) = true
      norm_num [leaf1889Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1889CertificateValid :
    WideCertificateValid leaf1889Box leaf1889Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi170ValidityFacts
    leaf1889LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1889CoverageChecked :
    coverageCheck (innerAD leaf1889Box) leaf1889InnerLog = true := by
  rfl'

private theorem leaf1889InnerLogValid :
    leaf1889InnerLog.Valid 8 (innerAD leaf1889Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1889CoverageChecked

private noncomputable def leaf1889InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1889InputLogOnePlusV_eq :
    leaf1889InputLogOnePlusV = outerEnclosure 24
      (leaf1889Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1889RoundedFacts : LeafRoundedFacts 8
    leaf1889Certificate.logOnePlusV leaf1889InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1889InputLogOnePlusV_eq }

private noncomputable def leaf1889Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi170InputQChi innerPair34Input
    leaf1889InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1889LowerChecked :
    lowerCheck 24 leaf1889Box leaf1889Inputs = true := by
  rfl'

private theorem leaf1889CoversExact : CoversExact 8
    leaf1889Box leaf1889Certificate leaf1889InnerLog leaf1889Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi170RoundedFacts
    innerPair34RoundedFacts leaf1889RoundedFacts (by rfl)

private theorem leaf1889FlatSound : Sound leaf1889Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1889CertificateValid
    leaf1889InnerLogValid leaf1889CoversExact leaf1889LowerChecked

private noncomputable def leaf1890Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1890Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427707) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1569392735/1073741824) }, upper := { exponent := 0, mantissa := (24133/16384) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863419/536855414) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1890InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1890LocalValidity :
    LeafFacts leaf1890Box leaf1890Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1890Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427707) }) = true
      norm_num [leaf1890Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1890CertificateValid :
    WideCertificateValid leaf1890Box leaf1890Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi171ValidityFacts
    leaf1890LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1890CoverageChecked :
    coverageCheck (innerAD leaf1890Box) leaf1890InnerLog = true := by
  rfl'

private theorem leaf1890InnerLogValid :
    leaf1890InnerLog.Valid 8 (innerAD leaf1890Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1890CoverageChecked

private noncomputable def leaf1890InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1890InputLogOnePlusV_eq :
    leaf1890InputLogOnePlusV = outerEnclosure 24
      (leaf1890Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1890RoundedFacts : LeafRoundedFacts 8
    leaf1890Certificate.logOnePlusV leaf1890InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1890InputLogOnePlusV_eq }

private noncomputable def leaf1890Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1890InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1890LowerChecked :
    lowerCheck 24 leaf1890Box leaf1890Inputs = true := by
  rfl'

private theorem leaf1890CoversExact : CoversExact 8
    leaf1890Box leaf1890Certificate leaf1890InnerLog leaf1890Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1890RoundedFacts (by rfl)

private theorem leaf1890FlatSound : Sound leaf1890Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1890CertificateValid
    leaf1890InnerLogValid leaf1890CoversExact leaf1890LowerChecked

private noncomputable def leaf1891Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1891Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194181) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1577387637/1073741824) }, upper := { exponent := 0, mantissa := (379/256) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388489/8388362) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1891InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1891LocalValidity :
    LeafFacts leaf1891Box leaf1891Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1891Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194181) }) = true
      norm_num [leaf1891Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1891CertificateValid :
    WideCertificateValid leaf1891Box leaf1891Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi172ValidityFacts
    leaf1891LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1891CoverageChecked :
    coverageCheck (innerAD leaf1891Box) leaf1891InnerLog = true := by
  rfl'

private theorem leaf1891InnerLogValid :
    leaf1891InnerLog.Valid 8 (innerAD leaf1891Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1891CoverageChecked

private noncomputable def leaf1891InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1891InputLogOnePlusV_eq :
    leaf1891InputLogOnePlusV = outerEnclosure 24
      (leaf1891Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1891RoundedFacts : LeafRoundedFacts 8
    leaf1891Certificate.logOnePlusV leaf1891InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1891InputLogOnePlusV_eq }

private noncomputable def leaf1891Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1891InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1891LowerChecked :
    lowerCheck 24 leaf1891Box leaf1891Inputs = true := by
  rfl'

private theorem leaf1891CoversExact : CoversExact 8
    leaf1891Box leaf1891Certificate leaf1891InnerLog leaf1891Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1891RoundedFacts (by rfl)

private theorem leaf1891FlatSound : Sound leaf1891Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1891CertificateValid
    leaf1891InnerLogValid leaf1891CoversExact leaf1891LowerChecked

private noncomputable def leaf1892Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1892Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106911) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1573455717/1073741824) }, upper := { exponent := 0, mantissa := (6049/4096) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215839/134213822) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1892InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1892LocalValidity :
    LeafFacts leaf1892Box leaf1892Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1892Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106911) }) = true
      norm_num [leaf1892Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1892CertificateValid :
    WideCertificateValid leaf1892Box leaf1892Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi171ValidityFacts
    leaf1892LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1892CoverageChecked :
    coverageCheck (innerAD leaf1892Box) leaf1892InnerLog = true := by
  rfl'

private theorem leaf1892InnerLogValid :
    leaf1892InnerLog.Valid 8 (innerAD leaf1892Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1892CoverageChecked

private noncomputable def leaf1892InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1892InputLogOnePlusV_eq :
    leaf1892InputLogOnePlusV = outerEnclosure 24
      (leaf1892Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1892RoundedFacts : LeafRoundedFacts 8
    leaf1892Certificate.logOnePlusV leaf1892InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1892InputLogOnePlusV_eq }

private noncomputable def leaf1892Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1892InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1892LowerChecked :
    lowerCheck 24 leaf1892Box leaf1892Inputs = true := by
  rfl'

private theorem leaf1892CoversExact : CoversExact 8
    leaf1892Box leaf1892Certificate leaf1892InnerLog leaf1892Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1892RoundedFacts (by rfl)

private theorem leaf1892FlatSound : Sound leaf1892Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1892CertificateValid
    leaf1892InnerLogValid leaf1892CoversExact leaf1892LowerChecked

private noncomputable def leaf1893Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1893Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (4581232913/4581163008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1581516151/1073741824) }, upper := { exponent := 0, mantissa := (95/64) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (9162395921/9162326016) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1893InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1893LocalValidity :
    LeafFacts leaf1893Box leaf1893Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1893Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4581232913/4581163008) }) = true
      norm_num [leaf1893Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1893CertificateValid :
    WideCertificateValid leaf1893Box leaf1893Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi172ValidityFacts
    leaf1893LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1893CoverageChecked :
    coverageCheck (innerAD leaf1893Box) leaf1893InnerLog = true := by
  rfl'

private theorem leaf1893InnerLogValid :
    leaf1893InnerLog.Valid 8 (innerAD leaf1893Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1893CoverageChecked

private noncomputable def leaf1893InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1893InputLogOnePlusV_eq :
    leaf1893InputLogOnePlusV = outerEnclosure 24
      (leaf1893Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1893RoundedFacts : LeafRoundedFacts 8
    leaf1893Certificate.logOnePlusV leaf1893InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1893InputLogOnePlusV_eq }

private noncomputable def leaf1893Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1893InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1893LowerChecked :
    lowerCheck 24 leaf1893Box leaf1893Inputs = true := by
  rfl'

private theorem leaf1893CoversExact : CoversExact 8
    leaf1893Box leaf1893Certificate leaf1893InnerLog leaf1893Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1893RoundedFacts (by rfl)

private theorem leaf1893FlatSound : Sound leaf1893Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1893CertificateValid
    leaf1893InnerLogValid leaf1893CoversExact leaf1893LowerChecked

private noncomputable def leaf1894Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (7/64), chiHi := (57/512) }

private noncomputable def leaf1894Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742187/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268428331) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1528762903/1073741824) }, upper := { exponent := 0, mantissa := (23509/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi173LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536864043/536856662) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1894InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1894LocalValidity :
    LeafFacts leaf1894Box leaf1894Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1894Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268428331) }) = true
      norm_num [leaf1894Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1894CertificateValid :
    WideCertificateValid leaf1894Box leaf1894Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi173ValidityFacts
    leaf1894LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1894CoverageChecked :
    coverageCheck (innerAD leaf1894Box) leaf1894InnerLog = true := by
  rfl'

private theorem leaf1894InnerLogValid :
    leaf1894InnerLog.Valid 8 (innerAD leaf1894Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1894CoverageChecked

private noncomputable def leaf1894InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1894InputLogOnePlusV_eq :
    leaf1894InputLogOnePlusV = outerEnclosure 24
      (leaf1894Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1894RoundedFacts : LeafRoundedFacts 8
    leaf1894Certificate.logOnePlusV leaf1894InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1894InputLogOnePlusV_eq }

private noncomputable def leaf1894Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi173InputQChi innerPair26Input
    leaf1894InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1894LowerChecked :
    lowerCheck 24 leaf1894Box leaf1894Inputs = true := by
  rfl'

private theorem leaf1894CoversExact : CoversExact 8
    leaf1894Box leaf1894Certificate leaf1894InnerLog leaf1894Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi173RoundedFacts
    innerPair26RoundedFacts leaf1894RoundedFacts (by rfl)

private theorem leaf1894FlatSound : Sound leaf1894Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1894CertificateValid
    leaf1894InnerLogValid leaf1894CoversExact leaf1894LowerChecked

private noncomputable def leaf1895Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (57/512), chiHi := (29/256) }

private noncomputable def leaf1895Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742189/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214103) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1536888869/1073741824) }, upper := { exponent := 0, mantissa := (11817/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi174LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431959/268428206) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1895InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1895LocalValidity :
    LeafFacts leaf1895Box leaf1895Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1895Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214103) }) = true
      norm_num [leaf1895Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1895CertificateValid :
    WideCertificateValid leaf1895Box leaf1895Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi174ValidityFacts
    leaf1895LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1895CoverageChecked :
    coverageCheck (innerAD leaf1895Box) leaf1895InnerLog = true := by
  rfl'

private theorem leaf1895InnerLogValid :
    leaf1895InnerLog.Valid 8 (innerAD leaf1895Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1895CoverageChecked

private noncomputable def leaf1895InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1895InputLogOnePlusV_eq :
    leaf1895InputLogOnePlusV = outerEnclosure 24
      (leaf1895Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1895RoundedFacts : LeafRoundedFacts 8
    leaf1895Certificate.logOnePlusV leaf1895InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1895InputLogOnePlusV_eq }

private noncomputable def leaf1895Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi174InputQChi innerPair27Input
    leaf1895InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1895LowerChecked :
    lowerCheck 24 leaf1895Box leaf1895Inputs = true := by
  rfl'

private theorem leaf1895CoversExact : CoversExact 8
    leaf1895Box leaf1895Certificate leaf1895InnerLog leaf1895Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi174RoundedFacts
    innerPair27RoundedFacts leaf1895RoundedFacts (by rfl)

private theorem leaf1895FlatSound : Sound leaf1895Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1895CertificateValid
    leaf1895InnerLogValid leaf1895CoversExact leaf1895LowerChecked

private noncomputable def leaf1896Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (7/64), chiHi := (57/512) }

private noncomputable def leaf1896Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742189/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1532432693/1073741824) }, upper := { exponent := 0, mantissa := (11783/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi173LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431993/268428274) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1896InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1896LocalValidity :
    LeafFacts leaf1896Box leaf1896Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1896Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214137) }) = true
      norm_num [leaf1896Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1896CertificateValid :
    WideCertificateValid leaf1896Box leaf1896Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi173ValidityFacts
    leaf1896LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1896CoverageChecked :
    coverageCheck (innerAD leaf1896Box) leaf1896InnerLog = true := by
  rfl'

private theorem leaf1896InnerLogValid :
    leaf1896InnerLog.Valid 8 (innerAD leaf1896Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1896CoverageChecked

private noncomputable def leaf1896InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1896InputLogOnePlusV_eq :
    leaf1896InputLogOnePlusV = outerEnclosure 24
      (leaf1896Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1896RoundedFacts : LeafRoundedFacts 8
    leaf1896Certificate.logOnePlusV leaf1896InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1896InputLogOnePlusV_eq }

private noncomputable def leaf1896Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi173InputQChi innerPair27Input
    leaf1896InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1896LowerChecked :
    lowerCheck 24 leaf1896Box leaf1896Inputs = true := by
  rfl'

private theorem leaf1896CoversExact : CoversExact 8
    leaf1896Box leaf1896Certificate leaf1896InnerLog leaf1896Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi173RoundedFacts
    innerPair27RoundedFacts leaf1896RoundedFacts (by rfl)

private theorem leaf1896FlatSound : Sound leaf1896Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1896CertificateValid
    leaf1896InnerLogValid leaf1896CoversExact leaf1896LowerChecked

private noncomputable def leaf1897Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (57/512), chiHi := (29/256) }

private noncomputable def leaf1897Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107037) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1540624191/1073741824) }, upper := { exponent := 0, mantissa := (5923/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi174LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215965/134214074) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1897InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1897LocalValidity :
    LeafFacts leaf1897Box leaf1897Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1897Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107037) }) = true
      norm_num [leaf1897Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1897CertificateValid :
    WideCertificateValid leaf1897Box leaf1897Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi174ValidityFacts
    leaf1897LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1897CoverageChecked :
    coverageCheck (innerAD leaf1897Box) leaf1897InnerLog = true := by
  rfl'

private theorem leaf1897InnerLogValid :
    leaf1897InnerLog.Valid 8 (innerAD leaf1897Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1897CoverageChecked

private noncomputable def leaf1897InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1897InputLogOnePlusV_eq :
    leaf1897InputLogOnePlusV = outerEnclosure 24
      (leaf1897Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1897RoundedFacts : LeafRoundedFacts 8
    leaf1897Certificate.logOnePlusV leaf1897InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1897InputLogOnePlusV_eq }

private noncomputable def leaf1897Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi174InputQChi innerPair27Input
    leaf1897InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1897LowerChecked :
    lowerCheck 24 leaf1897Box leaf1897Inputs = true := by
  rfl'

private theorem leaf1897CoversExact : CoversExact 8
    leaf1897Box leaf1897Certificate leaf1897InnerLog leaf1897Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi174RoundedFacts
    innerPair27RoundedFacts leaf1897RoundedFacts (by rfl)

private theorem leaf1897FlatSound : Sound leaf1897Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1897CertificateValid
    leaf1897InnerLogValid leaf1897CoversExact leaf1897LowerChecked

private noncomputable def leaf1898Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (29/256), chiHi := (59/512) }

private noncomputable def leaf1898Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268428081) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1545014835/1073741824) }, upper := { exponent := 0, mantissa := (23759/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi167LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863793/536856162) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1898InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1898LocalValidity :
    LeafFacts leaf1898Box leaf1898Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1898Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268428081) }) = true
      norm_num [leaf1898Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1898CertificateValid :
    WideCertificateValid leaf1898Box leaf1898Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi167ValidityFacts
    leaf1898LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1898CoverageChecked :
    coverageCheck (innerAD leaf1898Box) leaf1898InnerLog = true := by
  rfl'

private theorem leaf1898InnerLogValid :
    leaf1898InnerLog.Valid 8 (innerAD leaf1898Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1898CoverageChecked

private noncomputable def leaf1898InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1898InputLogOnePlusV_eq :
    leaf1898InputLogOnePlusV = outerEnclosure 24
      (leaf1898Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1898RoundedFacts : LeafRoundedFacts 8
    leaf1898Certificate.logOnePlusV leaf1898InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1898InputLogOnePlusV_eq }

private noncomputable def leaf1898Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi167InputQChi innerPair34Input
    leaf1898InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1898LowerChecked :
    lowerCheck 24 leaf1898Box leaf1898Inputs = true := by
  rfl'

private theorem leaf1898CoversExact : CoversExact 8
    leaf1898Box leaf1898Certificate leaf1898InnerLog leaf1898Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi167RoundedFacts
    innerPair34RoundedFacts leaf1898RoundedFacts (by rfl)

private theorem leaf1898FlatSound : Sound leaf1898Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1898CertificateValid
    leaf1898InnerLogValid leaf1898CoversExact leaf1898LowerChecked

private noncomputable def leaf1899Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (59/512), chiHi := (15/128) }

private noncomputable def leaf1899Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106989) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1553140801/1073741824) }, upper := { exponent := 0, mantissa := (5971/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi168LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215917/134213978) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1899InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1899LocalValidity :
    LeafFacts leaf1899Box leaf1899Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1899Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106989) }) = true
      norm_num [leaf1899Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1899CertificateValid :
    WideCertificateValid leaf1899Box leaf1899Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi168ValidityFacts
    leaf1899LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1899CoverageChecked :
    coverageCheck (innerAD leaf1899Box) leaf1899InnerLog = true := by
  rfl'

private theorem leaf1899InnerLogValid :
    leaf1899InnerLog.Valid 8 (innerAD leaf1899Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1899CoverageChecked

private noncomputable def leaf1899InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1899InputLogOnePlusV_eq :
    leaf1899InputLogOnePlusV = outerEnclosure 24
      (leaf1899Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1899RoundedFacts : LeafRoundedFacts 8
    leaf1899Certificate.logOnePlusV leaf1899InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1899InputLogOnePlusV_eq }

private noncomputable def leaf1899Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi168InputQChi innerPair34Input
    leaf1899InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1899LowerChecked :
    lowerCheck 24 leaf1899Box leaf1899Inputs = true := by
  rfl'

private theorem leaf1899CoversExact : CoversExact 8
    leaf1899Box leaf1899Certificate leaf1899InnerLog leaf1899Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi168RoundedFacts
    innerPair34RoundedFacts leaf1899RoundedFacts (by rfl)

private theorem leaf1899FlatSound : Sound leaf1899Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1899CertificateValid
    leaf1899InnerLogValid leaf1899CoversExact leaf1899LowerChecked

private noncomputable def leaf1900Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (29/256), chiHi := (59/512) }

private noncomputable def leaf1900Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214011) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1548815689/1073741824) }, upper := { exponent := 0, mantissa := (11909/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi167LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431867/268428022) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1900InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1900LocalValidity :
    LeafFacts leaf1900Box leaf1900Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1900Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214011) }) = true
      norm_num [leaf1900Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1900CertificateValid :
    WideCertificateValid leaf1900Box leaf1900Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi167ValidityFacts
    leaf1900LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1900CoverageChecked :
    coverageCheck (innerAD leaf1900Box) leaf1900InnerLog = true := by
  rfl'

private theorem leaf1900InnerLogValid :
    leaf1900InnerLog.Valid 8 (innerAD leaf1900Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1900CoverageChecked

private noncomputable def leaf1900InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1900InputLogOnePlusV_eq :
    leaf1900InputLogOnePlusV = outerEnclosure 24
      (leaf1900Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1900RoundedFacts : LeafRoundedFacts 8
    leaf1900Certificate.logOnePlusV leaf1900InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1900InputLogOnePlusV_eq }

private noncomputable def leaf1900Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi167InputQChi innerPair34Input
    leaf1900InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1900LowerChecked :
    lowerCheck 24 leaf1900Box leaf1900Inputs = true := by
  rfl'

private theorem leaf1900CoversExact : CoversExact 8
    leaf1900Box leaf1900Certificate leaf1900InnerLog leaf1900Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi167RoundedFacts
    innerPair34RoundedFacts leaf1900RoundedFacts (by rfl)

private theorem leaf1900FlatSound : Sound leaf1900Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1900CertificateValid
    leaf1900InnerLogValid leaf1900CoversExact leaf1900LowerChecked

private noncomputable def leaf1901Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (59/512), chiHi := (15/128) }

private noncomputable def leaf1901Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1557007187/1073741824) }, upper := { exponent := 0, mantissa := (2993/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi168LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67107951/67106974) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1901InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1901LocalValidity :
    LeafFacts leaf1901Box leaf1901Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1901Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553487) }) = true
      norm_num [leaf1901Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1901CertificateValid :
    WideCertificateValid leaf1901Box leaf1901Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi168ValidityFacts
    leaf1901LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1901CoverageChecked :
    coverageCheck (innerAD leaf1901Box) leaf1901InnerLog = true := by
  rfl'

private theorem leaf1901InnerLogValid :
    leaf1901InnerLog.Valid 8 (innerAD leaf1901Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1901CoverageChecked

private noncomputable def leaf1901InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1901InputLogOnePlusV_eq :
    leaf1901InputLogOnePlusV = outerEnclosure 24
      (leaf1901Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1901RoundedFacts : LeafRoundedFacts 8
    leaf1901Certificate.logOnePlusV leaf1901InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1901InputLogOnePlusV_eq }

private noncomputable def leaf1901Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi168InputQChi innerPair34Input
    leaf1901InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1901LowerChecked :
    lowerCheck 24 leaf1901Box leaf1901Inputs = true := by
  rfl'

private theorem leaf1901CoversExact : CoversExact 8
    leaf1901Box leaf1901Certificate leaf1901InnerLog leaf1901Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi168RoundedFacts
    innerPair34RoundedFacts leaf1901RoundedFacts (by rfl)

private theorem leaf1901FlatSound : Sound leaf1901Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1901CertificateValid
    leaf1901InnerLogValid leaf1901CoversExact leaf1901LowerChecked

private noncomputable def leaf1902Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (7/64), chiHi := (57/512) }

private noncomputable def leaf1902Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268428217) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1536102483/1073741824) }, upper := { exponent := 0, mantissa := (23623/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi173LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863929/536856434) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1902InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1902LocalValidity :
    LeafFacts leaf1902Box leaf1902Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1902Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268428217) }) = true
      norm_num [leaf1902Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1902CertificateValid :
    WideCertificateValid leaf1902Box leaf1902Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi173ValidityFacts
    leaf1902LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1902CoverageChecked :
    coverageCheck (innerAD leaf1902Box) leaf1902InnerLog = true := by
  rfl'

private theorem leaf1902InnerLogValid :
    leaf1902InnerLog.Valid 8 (innerAD leaf1902Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1902CoverageChecked

private noncomputable def leaf1902InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629315/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1902InputLogOnePlusV_eq :
    leaf1902InputLogOnePlusV = outerEnclosure 24
      (leaf1902Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1902RoundedFacts : LeafRoundedFacts 8
    leaf1902Certificate.logOnePlusV leaf1902InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1902InputLogOnePlusV_eq }

private noncomputable def leaf1902Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi173InputQChi innerPair27Input
    leaf1902InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1902LowerChecked :
    lowerCheck 24 leaf1902Box leaf1902Inputs = true := by
  rfl'

private theorem leaf1902CoversExact : CoversExact 8
    leaf1902Box leaf1902Certificate leaf1902InnerLog leaf1902Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi173RoundedFacts
    innerPair27RoundedFacts leaf1902RoundedFacts (by rfl)

private theorem leaf1902FlatSound : Sound leaf1902Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1902CertificateValid
    leaf1902InnerLogValid leaf1902CoversExact leaf1902LowerChecked

private noncomputable def leaf1903Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (57/512), chiHi := (29/256) }

private noncomputable def leaf1903Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214045) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1544359513/1073741824) }, upper := { exponent := 0, mantissa := (11875/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi174LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431901/268428090) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1903InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1903LocalValidity :
    LeafFacts leaf1903Box leaf1903Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1903Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214045) }) = true
      norm_num [leaf1903Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1903CertificateValid :
    WideCertificateValid leaf1903Box leaf1903Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi174ValidityFacts
    leaf1903LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1903CoverageChecked :
    coverageCheck (innerAD leaf1903Box) leaf1903InnerLog = true := by
  rfl'

private theorem leaf1903InnerLogValid :
    leaf1903InnerLog.Valid 8 (innerAD leaf1903Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1903CoverageChecked

private noncomputable def leaf1903InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1903InputLogOnePlusV_eq :
    leaf1903InputLogOnePlusV = outerEnclosure 24
      (leaf1903Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1903RoundedFacts : LeafRoundedFacts 8
    leaf1903Certificate.logOnePlusV leaf1903InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1903InputLogOnePlusV_eq }

private noncomputable def leaf1903Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi174InputQChi innerPair34Input
    leaf1903InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1903LowerChecked :
    lowerCheck 24 leaf1903Box leaf1903Inputs = true := by
  rfl'

private theorem leaf1903CoversExact : CoversExact 8
    leaf1903Box leaf1903Certificate leaf1903InnerLog leaf1903Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi174RoundedFacts
    innerPair34RoundedFacts leaf1903RoundedFacts (by rfl)

private theorem leaf1903FlatSound : Sound leaf1903Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1903CertificateValid
    leaf1903InnerLogValid leaf1903CoversExact leaf1903LowerChecked

private noncomputable def leaf1904Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (7/64), chiHi := (57/512) }

private noncomputable def leaf1904Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742193/1073741824) }, vSqrt := { lower := (65527/65536), upper := (2097154/2097095) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1539772273/1073741824) }, upper := { exponent := 0, mantissa := (185/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi173LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (4194249/4194190) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1904InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf1904LocalValidity :
    LeafFacts leaf1904Box leaf1904Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1904Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (2097154/2097095) }) = true
      norm_num [leaf1904Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1904CertificateValid :
    WideCertificateValid leaf1904Box leaf1904Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi173ValidityFacts
    leaf1904LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1904CoverageChecked :
    coverageCheck (innerAD leaf1904Box) leaf1904InnerLog = true := by
  rfl'

private theorem leaf1904InnerLogValid :
    leaf1904InnerLog.Valid 8 (innerAD leaf1904Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf1904CoverageChecked

private noncomputable def leaf1904InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1904InputLogOnePlusV_eq :
    leaf1904InputLogOnePlusV = outerEnclosure 24
      (leaf1904Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1904RoundedFacts : LeafRoundedFacts 8
    leaf1904Certificate.logOnePlusV leaf1904InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1904InputLogOnePlusV_eq }

private noncomputable def leaf1904Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi173InputQChi innerPair405Input
    leaf1904InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1904LowerChecked :
    lowerCheck 24 leaf1904Box leaf1904Inputs = true := by
  rfl'

private theorem leaf1904CoversExact : CoversExact 8
    leaf1904Box leaf1904Certificate leaf1904InnerLog leaf1904Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi173RoundedFacts
    innerPair405RoundedFacts leaf1904RoundedFacts (by rfl)

private theorem leaf1904FlatSound : Sound leaf1904Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1904CertificateValid
    leaf1904InnerLogValid leaf1904CoversExact leaf1904LowerChecked

private noncomputable def leaf1905Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (57/512), chiHi := (29/256) }

private noncomputable def leaf1905Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1548094835/1073741824) }, upper := { exponent := 0, mantissa := (93/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi174LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048562/1048547) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1905InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1905LocalValidity :
    LeafFacts leaf1905Box leaf1905Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1905Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048547) }) = true
      norm_num [leaf1905Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1905CertificateValid :
    WideCertificateValid leaf1905Box leaf1905Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi174ValidityFacts
    leaf1905LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1905CoverageChecked :
    coverageCheck (innerAD leaf1905Box) leaf1905InnerLog = true := by
  rfl'

private theorem leaf1905InnerLogValid :
    leaf1905InnerLog.Valid 8 (innerAD leaf1905Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1905CoverageChecked

private noncomputable def leaf1905InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1905InputLogOnePlusV_eq :
    leaf1905InputLogOnePlusV = outerEnclosure 24
      (leaf1905Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1905RoundedFacts : LeafRoundedFacts 8
    leaf1905Certificate.logOnePlusV leaf1905InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1905InputLogOnePlusV_eq }

private noncomputable def leaf1905Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi174InputQChi innerPair34Input
    leaf1905InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1905LowerChecked :
    lowerCheck 24 leaf1905Box leaf1905Inputs = true := by
  rfl'

private theorem leaf1905CoversExact : CoversExact 8
    leaf1905Box leaf1905Certificate leaf1905InnerLog leaf1905Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi174RoundedFacts
    innerPair34RoundedFacts leaf1905RoundedFacts (by rfl)

private theorem leaf1905FlatSound : Sound leaf1905Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1905CertificateValid
    leaf1905InnerLogValid leaf1905CoversExact leaf1905LowerChecked

private noncomputable def leaf1906Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (29/256), chiHi := (59/512) }

private noncomputable def leaf1906Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427963) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1552616543/1073741824) }, upper := { exponent := 0, mantissa := (23877/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi167LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863675/536855926) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1906InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1906LocalValidity :
    LeafFacts leaf1906Box leaf1906Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1906Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427963) }) = true
      norm_num [leaf1906Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1906CertificateValid :
    WideCertificateValid leaf1906Box leaf1906Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi167ValidityFacts
    leaf1906LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1906CoverageChecked :
    coverageCheck (innerAD leaf1906Box) leaf1906InnerLog = true := by
  rfl'

private theorem leaf1906InnerLogValid :
    leaf1906InnerLog.Valid 8 (innerAD leaf1906Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1906CoverageChecked

private noncomputable def leaf1906InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1906InputLogOnePlusV_eq :
    leaf1906InputLogOnePlusV = outerEnclosure 24
      (leaf1906Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1906RoundedFacts : LeafRoundedFacts 8
    leaf1906Certificate.logOnePlusV leaf1906InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1906InputLogOnePlusV_eq }

private noncomputable def leaf1906Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi167InputQChi innerPair34Input
    leaf1906InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1906LowerChecked :
    lowerCheck 24 leaf1906Box leaf1906Inputs = true := by
  rfl'

private theorem leaf1906CoversExact : CoversExact 8
    leaf1906Box leaf1906Certificate leaf1906InnerLog leaf1906Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi167RoundedFacts
    innerPair34RoundedFacts leaf1906RoundedFacts (by rfl)

private theorem leaf1906FlatSound : Sound leaf1906Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1906CertificateValid
    leaf1906InnerLogValid leaf1906CoversExact leaf1906LowerChecked

private noncomputable def leaf1907Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (59/512), chiHi := (15/128) }

private noncomputable def leaf1907Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106959) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1560873573/1073741824) }, upper := { exponent := 0, mantissa := (6001/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi168LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215887/134213918) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1907InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1907LocalValidity :
    LeafFacts leaf1907Box leaf1907Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1907Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106959) }) = true
      norm_num [leaf1907Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1907CertificateValid :
    WideCertificateValid leaf1907Box leaf1907Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi168ValidityFacts
    leaf1907LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1907CoverageChecked :
    coverageCheck (innerAD leaf1907Box) leaf1907InnerLog = true := by
  rfl'

private theorem leaf1907InnerLogValid :
    leaf1907InnerLog.Valid 8 (innerAD leaf1907Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1907CoverageChecked

private noncomputable def leaf1907InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1907InputLogOnePlusV_eq :
    leaf1907InputLogOnePlusV = outerEnclosure 24
      (leaf1907Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1907RoundedFacts : LeafRoundedFacts 8
    leaf1907Certificate.logOnePlusV leaf1907InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1907InputLogOnePlusV_eq }

private noncomputable def leaf1907Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi168InputQChi innerPair34Input
    leaf1907InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1907LowerChecked :
    lowerCheck 24 leaf1907Box leaf1907Inputs = true := by
  rfl'

private theorem leaf1907CoversExact : CoversExact 8
    leaf1907Box leaf1907Certificate leaf1907InnerLog leaf1907Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi168RoundedFacts
    innerPair34RoundedFacts leaf1907RoundedFacts (by rfl)

private theorem leaf1907FlatSound : Sound leaf1907Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1907CertificateValid
    leaf1907InnerLogValid leaf1907CoversExact leaf1907LowerChecked

private noncomputable def leaf1908Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (29/256), chiHi := (59/512) }

private noncomputable def leaf1908Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (65527/65536), upper := (2097154/2097093) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1556417397/1073741824) }, upper := { exponent := 0, mantissa := (187/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi167LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (4194247/4194186) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1908InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1908LocalValidity :
    LeafFacts leaf1908Box leaf1908Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1908Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (2097154/2097093) }) = true
      norm_num [leaf1908Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1908CertificateValid :
    WideCertificateValid leaf1908Box leaf1908Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi167ValidityFacts
    leaf1908LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1908CoverageChecked :
    coverageCheck (innerAD leaf1908Box) leaf1908InnerLog = true := by
  rfl'

private theorem leaf1908InnerLogValid :
    leaf1908InnerLog.Valid 8 (innerAD leaf1908Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1908CoverageChecked

private noncomputable def leaf1908InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1908InputLogOnePlusV_eq :
    leaf1908InputLogOnePlusV = outerEnclosure 24
      (leaf1908Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1908RoundedFacts : LeafRoundedFacts 8
    leaf1908Certificate.logOnePlusV leaf1908InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1908InputLogOnePlusV_eq }

private noncomputable def leaf1908Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi167InputQChi innerPair34Input
    leaf1908InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1908LowerChecked :
    lowerCheck 24 leaf1908Box leaf1908Inputs = true := by
  rfl'

private theorem leaf1908CoversExact : CoversExact 8
    leaf1908Box leaf1908Certificate leaf1908InnerLog leaf1908Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi167RoundedFacts
    innerPair34RoundedFacts leaf1908RoundedFacts (by rfl)

private theorem leaf1908FlatSound : Sound leaf1908Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1908CertificateValid
    leaf1908InnerLogValid leaf1908CoversExact leaf1908LowerChecked

private noncomputable def leaf1909Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (59/512), chiHi := (15/128) }

private noncomputable def leaf1909Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048546) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1564739959/1073741824) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi168LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097123/2097092) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1909InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1909LocalValidity :
    LeafFacts leaf1909Box leaf1909Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1909Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048546) }) = true
      norm_num [leaf1909Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1909CertificateValid :
    WideCertificateValid leaf1909Box leaf1909Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi168ValidityFacts
    leaf1909LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1909CoverageChecked :
    coverageCheck (innerAD leaf1909Box) leaf1909InnerLog = true := by
  rfl'

private theorem leaf1909InnerLogValid :
    leaf1909InnerLog.Valid 8 (innerAD leaf1909Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1909CoverageChecked

private noncomputable def leaf1909InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1909InputLogOnePlusV_eq :
    leaf1909InputLogOnePlusV = outerEnclosure 24
      (leaf1909Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1909RoundedFacts : LeafRoundedFacts 8
    leaf1909Certificate.logOnePlusV leaf1909InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1909InputLogOnePlusV_eq }

private noncomputable def leaf1909Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi168InputQChi innerPair34Input
    leaf1909InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1909LowerChecked :
    lowerCheck 24 leaf1909Box leaf1909Inputs = true := by
  rfl'

private theorem leaf1909CoversExact : CoversExact 8
    leaf1909Box leaf1909Certificate leaf1909InnerLog leaf1909Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi168RoundedFacts
    innerPair34RoundedFacts leaf1909RoundedFacts (by rfl)

private theorem leaf1909FlatSound : Sound leaf1909Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1909CertificateValid
    leaf1909InnerLogValid leaf1909CoversExact leaf1909LowerChecked

private noncomputable def leaf1910Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (15/128), chiHi := (61/512) }

private noncomputable def leaf1910Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742195/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427831) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1561266767/1073741824) }, upper := { exponent := 0, mantissa := (24009/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi169LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863543/536855662) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1910InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1910LocalValidity :
    LeafFacts leaf1910Box leaf1910Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1910Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427831) }) = true
      norm_num [leaf1910Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1910CertificateValid :
    WideCertificateValid leaf1910Box leaf1910Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi169ValidityFacts
    leaf1910LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1910CoverageChecked :
    coverageCheck (innerAD leaf1910Box) leaf1910InnerLog = true := by
  rfl'

private theorem leaf1910InnerLogValid :
    leaf1910InnerLog.Valid 8 (innerAD leaf1910Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1910CoverageChecked

private noncomputable def leaf1910InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1910InputLogOnePlusV_eq :
    leaf1910InputLogOnePlusV = outerEnclosure 24
      (leaf1910Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1910RoundedFacts : LeafRoundedFacts 8
    leaf1910Certificate.logOnePlusV leaf1910InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1910InputLogOnePlusV_eq }

private noncomputable def leaf1910Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi169InputQChi innerPair34Input
    leaf1910InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1910LowerChecked :
    lowerCheck 24 leaf1910Box leaf1910Inputs = true := by
  rfl'

private theorem leaf1910CoversExact : CoversExact 8
    leaf1910Box leaf1910Certificate leaf1910InnerLog leaf1910Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi169RoundedFacts
    innerPair34RoundedFacts leaf1910RoundedFacts (by rfl)

private theorem leaf1910FlatSound : Sound leaf1910Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1910CertificateValid
    leaf1910InnerLogValid leaf1910CoversExact leaf1910LowerChecked

private noncomputable def leaf1911Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (61/512), chiHi := (31/256) }

private noncomputable def leaf1911Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213853) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1569392733/1073741824) }, upper := { exponent := 0, mantissa := (12067/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi170LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431709/268427706) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1911InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1911LocalValidity :
    LeafFacts leaf1911Box leaf1911Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1911Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213853) }) = true
      norm_num [leaf1911Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1911CertificateValid :
    WideCertificateValid leaf1911Box leaf1911Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi170ValidityFacts
    leaf1911LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1911CoverageChecked :
    coverageCheck (innerAD leaf1911Box) leaf1911InnerLog = true := by
  rfl'

private theorem leaf1911InnerLogValid :
    leaf1911InnerLog.Valid 8 (innerAD leaf1911Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1911CoverageChecked

private noncomputable def leaf1911InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1911InputLogOnePlusV_eq :
    leaf1911InputLogOnePlusV = outerEnclosure 24
      (leaf1911Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1911RoundedFacts : LeafRoundedFacts 8
    leaf1911Certificate.logOnePlusV leaf1911InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1911InputLogOnePlusV_eq }

private noncomputable def leaf1911Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi170InputQChi innerPair34Input
    leaf1911InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1911LowerChecked :
    lowerCheck 24 leaf1911Box leaf1911Inputs = true := by
  rfl'

private theorem leaf1911CoversExact : CoversExact 8
    leaf1911Box leaf1911Certificate leaf1911InnerLog leaf1911Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi170RoundedFacts
    innerPair34RoundedFacts leaf1911RoundedFacts (by rfl)

private theorem leaf1911FlatSound : Sound leaf1911Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1911CertificateValid
    leaf1911InnerLogValid leaf1911CoversExact leaf1911LowerChecked

private noncomputable def leaf1912Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (15/128), chiHi := (61/512) }

private noncomputable def leaf1912Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742197/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213885) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1565198685/1073741824) }, upper := { exponent := 0, mantissa := (12035/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi169LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431741/268427770) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1912InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1912LocalValidity :
    LeafFacts leaf1912Box leaf1912Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1912Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213885) }) = true
      norm_num [leaf1912Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1912CertificateValid :
    WideCertificateValid leaf1912Box leaf1912Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi169ValidityFacts
    leaf1912LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1912CoverageChecked :
    coverageCheck (innerAD leaf1912Box) leaf1912InnerLog = true := by
  rfl'

private theorem leaf1912InnerLogValid :
    leaf1912InnerLog.Valid 8 (innerAD leaf1912Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1912CoverageChecked

private noncomputable def leaf1912InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1912InputLogOnePlusV_eq :
    leaf1912InputLogOnePlusV = outerEnclosure 24
      (leaf1912Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1912RoundedFacts : LeafRoundedFacts 8
    leaf1912Certificate.logOnePlusV leaf1912InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1912InputLogOnePlusV_eq }

private noncomputable def leaf1912Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi169InputQChi innerPair34Input
    leaf1912InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1912LowerChecked :
    lowerCheck 24 leaf1912Box leaf1912Inputs = true := by
  rfl'

private theorem leaf1912CoversExact : CoversExact 8
    leaf1912Box leaf1912Certificate leaf1912InnerLog leaf1912Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi169RoundedFacts
    innerPair34RoundedFacts leaf1912RoundedFacts (by rfl)

private theorem leaf1912FlatSound : Sound leaf1912Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1912CertificateValid
    leaf1912InnerLogValid leaf1912CoversExact leaf1912LowerChecked

private noncomputable def leaf1913Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (61/512), chiHi := (31/256) }

private noncomputable def leaf1913Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (67108928/67106911) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1573390183/1073741824) }, upper := { exponent := 0, mantissa := (6049/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi170LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134215839/134213822) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1913InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1913LocalValidity :
    LeafFacts leaf1913Box leaf1913Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1913Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67106911) }) = true
      norm_num [leaf1913Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1913CertificateValid :
    WideCertificateValid leaf1913Box leaf1913Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi170ValidityFacts
    leaf1913LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1913CoverageChecked :
    coverageCheck (innerAD leaf1913Box) leaf1913InnerLog = true := by
  rfl'

private theorem leaf1913InnerLogValid :
    leaf1913InnerLog.Valid 8 (innerAD leaf1913Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1913CoverageChecked

private noncomputable def leaf1913InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1913InputLogOnePlusV_eq :
    leaf1913InputLogOnePlusV = outerEnclosure 24
      (leaf1913Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1913RoundedFacts : LeafRoundedFacts 8
    leaf1913Certificate.logOnePlusV leaf1913InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1913InputLogOnePlusV_eq }

private noncomputable def leaf1913Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi170InputQChi innerPair34Input
    leaf1913InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1913LowerChecked :
    lowerCheck 24 leaf1913Box leaf1913Inputs = true := by
  rfl'

private theorem leaf1913CoversExact : CoversExact 8
    leaf1913Box leaf1913Certificate leaf1913InnerLog leaf1913Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi170RoundedFacts
    innerPair34RoundedFacts leaf1913RoundedFacts (by rfl)

private theorem leaf1913FlatSound : Sound leaf1913Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1913CertificateValid
    leaf1913InnerLogValid leaf1913CoversExact leaf1913LowerChecked

private noncomputable def leaf1914Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1914Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427581) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1577518699/1073741824) }, upper := { exponent := 0, mantissa := (24259/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863293/536855162) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1914InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1914LocalValidity :
    LeafFacts leaf1914Box leaf1914Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1914Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427581) }) = true
      norm_num [leaf1914Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1914CertificateValid :
    WideCertificateValid leaf1914Box leaf1914Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi171ValidityFacts
    leaf1914LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1914CoverageChecked :
    coverageCheck (innerAD leaf1914Box) leaf1914InnerLog = true := by
  rfl'

private theorem leaf1914InnerLogValid :
    leaf1914InnerLog.Valid 8 (innerAD leaf1914Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1914CoverageChecked

private noncomputable def leaf1914InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1914InputLogOnePlusV_eq :
    leaf1914InputLogOnePlusV = outerEnclosure 24
      (leaf1914Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1914RoundedFacts : LeafRoundedFacts 8
    leaf1914Certificate.logOnePlusV leaf1914InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1914InputLogOnePlusV_eq }

private noncomputable def leaf1914Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1914InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1914LowerChecked :
    lowerCheck 24 leaf1914Box leaf1914Inputs = true := by
  rfl'

private theorem leaf1914CoversExact : CoversExact 8
    leaf1914Box leaf1914Certificate leaf1914InnerLog leaf1914Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1914RoundedFacts (by rfl)

private theorem leaf1914FlatSound : Sound leaf1914Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1914CertificateValid
    leaf1914InnerLogValid leaf1914CoversExact leaf1914LowerChecked

private noncomputable def leaf1915Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1915Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742201/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717428736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1585644665/1073741824) }, upper := { exponent := 0, mantissa := (381/256) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435922431/137434857472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1915InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1915LocalValidity :
    LeafFacts leaf1915Box leaf1915Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1915Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717428736) }) = true
      norm_num [leaf1915Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1915CertificateValid :
    WideCertificateValid leaf1915Box leaf1915Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi172ValidityFacts
    leaf1915LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1915CoverageChecked :
    coverageCheck (innerAD leaf1915Box) leaf1915InnerLog = true := by
  rfl'

private theorem leaf1915InnerLogValid :
    leaf1915InnerLog.Valid 8 (innerAD leaf1915Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1915CoverageChecked

private noncomputable def leaf1915InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1915InputLogOnePlusV_eq :
    leaf1915InputLogOnePlusV = outerEnclosure 24
      (leaf1915Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1915RoundedFacts : LeafRoundedFacts 8
    leaf1915Certificate.logOnePlusV leaf1915InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1915InputLogOnePlusV_eq }

private noncomputable def leaf1915Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1915InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1915LowerChecked :
    lowerCheck 24 leaf1915Box leaf1915Inputs = true := by
  rfl'

private theorem leaf1915CoversExact : CoversExact 8
    leaf1915Box leaf1915Certificate leaf1915InnerLog leaf1915Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1915RoundedFacts (by rfl)

private theorem leaf1915FlatSound : Sound leaf1915Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1915CertificateValid
    leaf1915InnerLogValid leaf1915CoversExact leaf1915LowerChecked

private noncomputable def leaf1916Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1916Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742201/1073741824) }, vSqrt := { lower := (8191/8192), upper := (4042264335/4042202624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1581581681/1073741824) }, upper := { exponent := 0, mantissa := (12161/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8084466959/8084405248) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1916InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1916LocalValidity :
    LeafFacts leaf1916Box leaf1916Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1916Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4042264335/4042202624) }) = true
      norm_num [leaf1916Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1916CertificateValid :
    WideCertificateValid leaf1916Box leaf1916Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi171ValidityFacts
    leaf1916LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1916CoverageChecked :
    coverageCheck (innerAD leaf1916Box) leaf1916InnerLog = true := by
  rfl'

private theorem leaf1916InnerLogValid :
    leaf1916InnerLog.Valid 8 (innerAD leaf1916Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1916CoverageChecked

private noncomputable def leaf1916InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1916InputLogOnePlusV_eq :
    leaf1916InputLogOnePlusV = outerEnclosure 24
      (leaf1916Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1916RoundedFacts : LeafRoundedFacts 8
    leaf1916Certificate.logOnePlusV leaf1916InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1916InputLogOnePlusV_eq }

private noncomputable def leaf1916Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1916InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1916LowerChecked :
    lowerCheck 24 leaf1916Box leaf1916Inputs = true := by
  rfl'

private theorem leaf1916CoversExact : CoversExact 8
    leaf1916Box leaf1916Certificate leaf1916InnerLog leaf1916Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1916RoundedFacts (by rfl)

private theorem leaf1916FlatSound : Sound leaf1916Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1916CertificateValid
    leaf1916InnerLogValid leaf1916CoversExact leaf1916LowerChecked

private noncomputable def leaf1917Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1917Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742203/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717412352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1589773179/1073741824) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435906047/137434824704) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1917InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1917LocalValidity :
    LeafFacts leaf1917Box leaf1917Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1917Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717412352) }) = true
      norm_num [leaf1917Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1917CertificateValid :
    WideCertificateValid leaf1917Box leaf1917Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi172ValidityFacts
    leaf1917LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1917CoverageChecked :
    coverageCheck (innerAD leaf1917Box) leaf1917InnerLog = true := by
  rfl'

private theorem leaf1917InnerLogValid :
    leaf1917InnerLog.Valid 8 (innerAD leaf1917Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1917CoverageChecked

private noncomputable def leaf1917InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1917InputLogOnePlusV_eq :
    leaf1917InputLogOnePlusV = outerEnclosure 24
      (leaf1917Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1917RoundedFacts : LeafRoundedFacts 8
    leaf1917Certificate.logOnePlusV leaf1917InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1917InputLogOnePlusV_eq }

private noncomputable def leaf1917Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1917InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1917LowerChecked :
    lowerCheck 24 leaf1917Box leaf1917Inputs = true := by
  rfl'

private theorem leaf1917CoversExact : CoversExact 8
    leaf1917Box leaf1917Certificate leaf1917InnerLog leaf1917Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1917RoundedFacts (by rfl)

private theorem leaf1917FlatSound : Sound leaf1917Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1917CertificateValid
    leaf1917InnerLogValid leaf1917CoversExact leaf1917LowerChecked

private noncomputable def leaf1918Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (15/128), chiHi := (61/512) }

private noncomputable def leaf1918Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742199/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268427709) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1569130603/1073741824) }, upper := { exponent := 0, mantissa := (24131/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi169LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536863421/536855418) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1918InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1918LocalValidity :
    LeafFacts leaf1918Box leaf1918Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1918Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268427709) }) = true
      norm_num [leaf1918Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1918CertificateValid :
    WideCertificateValid leaf1918Box leaf1918Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi169ValidityFacts
    leaf1918LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1918CoverageChecked :
    coverageCheck (innerAD leaf1918Box) leaf1918InnerLog = true := by
  rfl'

private theorem leaf1918InnerLogValid :
    leaf1918InnerLog.Valid 8 (innerAD leaf1918Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1918CoverageChecked

private noncomputable def leaf1918InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1918InputLogOnePlusV_eq :
    leaf1918InputLogOnePlusV = outerEnclosure 24
      (leaf1918Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1918RoundedFacts : LeafRoundedFacts 8
    leaf1918Certificate.logOnePlusV leaf1918InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1918InputLogOnePlusV_eq }

private noncomputable def leaf1918Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi169InputQChi innerPair34Input
    leaf1918InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1918LowerChecked :
    lowerCheck 24 leaf1918Box leaf1918Inputs = true := by
  rfl'

private theorem leaf1918CoversExact : CoversExact 8
    leaf1918Box leaf1918Certificate leaf1918InnerLog leaf1918Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi169RoundedFacts
    innerPair34RoundedFacts leaf1918RoundedFacts (by rfl)

private theorem leaf1918FlatSound : Sound leaf1918Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1918CertificateValid
    leaf1918InnerLogValid leaf1918CoversExact leaf1918LowerChecked

private noncomputable def leaf1919Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (61/512), chiHi := (31/256) }

private noncomputable def leaf1919Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742201/1073741824) }, vSqrt := { lower := (8191/8192), upper := (134217856/134213791) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1577387633/1073741824) }, upper := { exponent := 0, mantissa := (12129/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi170LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268431647/268427582) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1919InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1919LocalValidity :
    LeafFacts leaf1919Box leaf1919Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1919Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134213791) }) = true
      norm_num [leaf1919Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1919CertificateValid :
    WideCertificateValid leaf1919Box leaf1919Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi170ValidityFacts
    leaf1919LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1919CoverageChecked :
    coverageCheck (innerAD leaf1919Box) leaf1919InnerLog = true := by
  rfl'

private theorem leaf1919InnerLogValid :
    leaf1919InnerLog.Valid 8 (innerAD leaf1919Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1919CoverageChecked

private noncomputable def leaf1919InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1919InputLogOnePlusV_eq :
    leaf1919InputLogOnePlusV = outerEnclosure 24
      (leaf1919Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1919RoundedFacts : LeafRoundedFacts 8
    leaf1919Certificate.logOnePlusV leaf1919InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1919InputLogOnePlusV_eq }

private noncomputable def leaf1919Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi170InputQChi innerPair34Input
    leaf1919InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1919LowerChecked :
    lowerCheck 24 leaf1919Box leaf1919Inputs = true := by
  rfl'

private theorem leaf1919CoversExact : CoversExact 8
    leaf1919Box leaf1919Certificate leaf1919InnerLog leaf1919Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi170RoundedFacts
    innerPair34RoundedFacts leaf1919RoundedFacts (by rfl)

private theorem leaf1919FlatSound : Sound leaf1919Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1919CertificateValid
    leaf1919InnerLogValid leaf1919CoversExact leaf1919LowerChecked

private noncomputable def leaf1920Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (15/128), chiHi := (61/512) }

private noncomputable def leaf1920Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742201/1073741824) }, vSqrt := { lower := (65527/65536), upper := (2097154/2097091) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1573062521/1073741824) }, upper := { exponent := 0, mantissa := (189/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi169LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (4194245/4194182) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1920InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1920LocalValidity :
    LeafFacts leaf1920Box leaf1920Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1920Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (2097154/2097091) }) = true
      norm_num [leaf1920Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1920CertificateValid :
    WideCertificateValid leaf1920Box leaf1920Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi169ValidityFacts
    leaf1920LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1920CoverageChecked :
    coverageCheck (innerAD leaf1920Box) leaf1920InnerLog = true := by
  rfl'

private theorem leaf1920InnerLogValid :
    leaf1920InnerLog.Valid 8 (innerAD leaf1920Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1920CoverageChecked

private noncomputable def leaf1920InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1920InputLogOnePlusV_eq :
    leaf1920InputLogOnePlusV = outerEnclosure 24
      (leaf1920Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1920RoundedFacts : LeafRoundedFacts 8
    leaf1920Certificate.logOnePlusV leaf1920InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1920InputLogOnePlusV_eq }

private noncomputable def leaf1920Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi169InputQChi innerPair34Input
    leaf1920InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1920LowerChecked :
    lowerCheck 24 leaf1920Box leaf1920Inputs = true := by
  rfl'

private theorem leaf1920CoversExact : CoversExact 8
    leaf1920Box leaf1920Certificate leaf1920InnerLog leaf1920Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi169RoundedFacts
    innerPair34RoundedFacts leaf1920RoundedFacts (by rfl)

private theorem leaf1920FlatSound : Sound leaf1920Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1920CertificateValid
    leaf1920InnerLogValid leaf1920CoversExact leaf1920LowerChecked

private noncomputable def leaf1921Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (61/512), chiHi := (31/256) }

private noncomputable def leaf1921Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742203/1073741824) }, vSqrt := { lower := (65527/65536), upper := (4581232913/4581163008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1581385083/1073741824) }, upper := { exponent := 0, mantissa := (95/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi170LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (9162395921/9162326016) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1921InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1921LocalValidity :
    LeafFacts leaf1921Box leaf1921Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1921Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (4581232913/4581163008) }) = true
      norm_num [leaf1921Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1921CertificateValid :
    WideCertificateValid leaf1921Box leaf1921Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi170ValidityFacts
    leaf1921LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1921CoverageChecked :
    coverageCheck (innerAD leaf1921Box) leaf1921InnerLog = true := by
  rfl'

private theorem leaf1921InnerLogValid :
    leaf1921InnerLog.Valid 8 (innerAD leaf1921Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1921CoverageChecked

private noncomputable def leaf1921InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1921InputLogOnePlusV_eq :
    leaf1921InputLogOnePlusV = outerEnclosure 24
      (leaf1921Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1921RoundedFacts : LeafRoundedFacts 8
    leaf1921Certificate.logOnePlusV leaf1921InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1921InputLogOnePlusV_eq }

private noncomputable def leaf1921Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi170InputQChi innerPair34Input
    leaf1921InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1921LowerChecked :
    lowerCheck 24 leaf1921Box leaf1921Inputs = true := by
  rfl'

private theorem leaf1921CoversExact : CoversExact 8
    leaf1921Box leaf1921Certificate leaf1921InnerLog leaf1921Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi170RoundedFacts
    innerPair34RoundedFacts leaf1921RoundedFacts (by rfl)

private theorem leaf1921FlatSound : Sound leaf1921Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1921CertificateValid
    leaf1921InnerLogValid leaf1921CoversExact leaf1921LowerChecked

private noncomputable def leaf1922Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1922Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742203/1073741824) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743485696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1585644663/1073741824) }, upper := { exponent := 0, mantissa := (24385/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487184435/27486971392) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1922InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1922LocalValidity :
    LeafFacts leaf1922Box leaf1922Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1922Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743485696) }) = true
      norm_num [leaf1922Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1922CertificateValid :
    WideCertificateValid leaf1922Box leaf1922Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi171ValidityFacts
    leaf1922LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1922CoverageChecked :
    coverageCheck (innerAD leaf1922Box) leaf1922InnerLog = true := by
  rfl'

private theorem leaf1922InnerLogValid :
    leaf1922InnerLog.Valid 8 (innerAD leaf1922Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1922CoverageChecked

private noncomputable def leaf1922InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1922InputLogOnePlusV_eq :
    leaf1922InputLogOnePlusV = outerEnclosure 24
      (leaf1922Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1922RoundedFacts : LeafRoundedFacts 8
    leaf1922Certificate.logOnePlusV leaf1922InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1922InputLogOnePlusV_eq }

private noncomputable def leaf1922Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1922InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1922LowerChecked :
    lowerCheck 24 leaf1922Box leaf1922Inputs = true := by
  rfl'

private theorem leaf1922CoversExact : CoversExact 8
    leaf1922Box leaf1922Certificate leaf1922InnerLog leaf1922Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1922RoundedFacts (by rfl)

private theorem leaf1922FlatSound : Sound leaf1922Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1922CertificateValid
    leaf1922InnerLogValid leaf1922CoversExact leaf1922LowerChecked

private noncomputable def leaf1923Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1923Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742205/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905798656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1593901693/1073741824) }, upper := { exponent := 0, mantissa := (383/256) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811963221/45811597312) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1923InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1923LocalValidity :
    LeafFacts leaf1923Box leaf1923Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1923Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905798656) }) = true
      norm_num [leaf1923Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1923CertificateValid :
    WideCertificateValid leaf1923Box leaf1923Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi172ValidityFacts
    leaf1923LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1923CoverageChecked :
    coverageCheck (innerAD leaf1923Box) leaf1923InnerLog = true := by
  rfl'

private theorem leaf1923InnerLogValid :
    leaf1923InnerLog.Valid 8 (innerAD leaf1923Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1923CoverageChecked

private noncomputable def leaf1923InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1923InputLogOnePlusV_eq :
    leaf1923InputLogOnePlusV = outerEnclosure 24
      (leaf1923Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1923RoundedFacts : LeafRoundedFacts 8
    leaf1923Certificate.logOnePlusV leaf1923InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1923InputLogOnePlusV_eq }

private noncomputable def leaf1923Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1923InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1923LowerChecked :
    lowerCheck 24 leaf1923Box leaf1923Inputs = true := by
  rfl'

private theorem leaf1923CoversExact : CoversExact 8
    leaf1923Box leaf1923Certificate leaf1923InnerLog leaf1923Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1923RoundedFacts (by rfl)

private theorem leaf1923FlatSound : Sound leaf1923Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1923CertificateValid
    leaf1923InnerLogValid leaf1923CoversExact leaf1923LowerChecked

private noncomputable def leaf1924Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (31/256), chiHi := (63/512) }

private noncomputable def leaf1924Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742205/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68718493695/68717412352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1589707645/1073741824) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi171LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137435906047/137434824704) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1924InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1924LocalValidity :
    LeafFacts leaf1924Box leaf1924Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1924Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68718493695/68717412352) }) = true
      norm_num [leaf1924Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1924CertificateValid :
    WideCertificateValid leaf1924Box leaf1924Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi171ValidityFacts
    leaf1924LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1924CoverageChecked :
    coverageCheck (innerAD leaf1924Box) leaf1924InnerLog = true := by
  rfl'

private theorem leaf1924InnerLogValid :
    leaf1924InnerLog.Valid 8 (innerAD leaf1924Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1924CoverageChecked

private noncomputable def leaf1924InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1924InputLogOnePlusV_eq :
    leaf1924InputLogOnePlusV = outerEnclosure 24
      (leaf1924Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1924RoundedFacts : LeafRoundedFacts 8
    leaf1924Certificate.logOnePlusV leaf1924InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1924InputLogOnePlusV_eq }

private noncomputable def leaf1924Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi171InputQChi innerPair34Input
    leaf1924InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1924LowerChecked :
    lowerCheck 24 leaf1924Box leaf1924Inputs = true := by
  rfl'

private theorem leaf1924CoversExact : CoversExact 8
    leaf1924Box leaf1924Certificate leaf1924InnerLog leaf1924Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi171RoundedFacts
    innerPair34RoundedFacts leaf1924RoundedFacts (by rfl)

private theorem leaf1924FlatSound : Sound leaf1924Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1924CertificateValid
    leaf1924InnerLogValid leaf1924CoversExact leaf1924LowerChecked

private noncomputable def leaf1925Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (63/512), chiHi := (1/8) }

private noncomputable def leaf1925Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742207/1073741824) }, vSqrt := { lower := (65527/65536), upper := (68718493695/68717379584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1598030207/1073741824) }, upper := { exponent := 0, mantissa := (3/2) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi172LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (137435873279/137434759168) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1925InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1925LocalValidity :
    LeafFacts leaf1925Box leaf1925Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1925Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (68718493695/68717379584) }) = true
      norm_num [leaf1925Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1925CertificateValid :
    WideCertificateValid leaf1925Box leaf1925Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi172ValidityFacts
    leaf1925LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1925CoverageChecked :
    coverageCheck (innerAD leaf1925Box) leaf1925InnerLog = true := by
  rfl'

private theorem leaf1925InnerLogValid :
    leaf1925InnerLog.Valid 8 (innerAD leaf1925Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1925CoverageChecked

private noncomputable def leaf1925InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1925InputLogOnePlusV_eq :
    leaf1925InputLogOnePlusV = outerEnclosure 24
      (leaf1925Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1925RoundedFacts : LeafRoundedFacts 8
    leaf1925Certificate.logOnePlusV leaf1925InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1925InputLogOnePlusV_eq }

private noncomputable def leaf1925Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi172InputQChi innerPair34Input
    leaf1925InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1925LowerChecked :
    lowerCheck 24 leaf1925Box leaf1925Inputs = true := by
  rfl'

private theorem leaf1925CoversExact : CoversExact 8
    leaf1925Box leaf1925Certificate leaf1925InnerLog leaf1925Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi172RoundedFacts
    innerPair34RoundedFacts leaf1925RoundedFacts (by rfl)

private theorem leaf1925FlatSound : Sound leaf1925Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1925CertificateValid
    leaf1925InnerLogValid leaf1925CoversExact leaf1925LowerChecked

private noncomputable def component42Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node0_sound : Sound component42Node0Box :=
  sound_of_literal_split component42Node0Box leaf1870Box leaf1871Box
    .k (121/32) (by rfl) (by rfl)
    leaf1870FlatSound leaf1871FlatSound

private noncomputable def component42Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node1_sound : Sound component42Node1Box :=
  sound_of_literal_split component42Node1Box leaf1872Box leaf1873Box
    .k (121/32) (by rfl) (by rfl)
    leaf1872FlatSound leaf1873FlatSound

private noncomputable def component42Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node2_sound : Sound component42Node2Box :=
  sound_of_literal_split component42Node2Box component42Node0Box component42Node1Box
    .chi (29/256) (by rfl) (by rfl)
    component42Node0_sound component42Node1_sound

private noncomputable def component42Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node3_sound : Sound component42Node3Box :=
  sound_of_literal_split component42Node3Box leaf1874Box leaf1875Box
    .k (123/32) (by rfl) (by rfl)
    leaf1874FlatSound leaf1875FlatSound

private noncomputable def component42Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node4_sound : Sound component42Node4Box :=
  sound_of_literal_split component42Node4Box leaf1877Box leaf1878Box
    .chi (59/512) (by rfl) (by rfl)
    leaf1877FlatSound leaf1878FlatSound

private noncomputable def component42Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node5_sound : Sound component42Node5Box :=
  sound_of_literal_split component42Node5Box leaf1876Box component42Node4Box
    .k (123/32) (by rfl) (by rfl)
    leaf1876FlatSound component42Node4_sound

private noncomputable def component42Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node6_sound : Sound component42Node6Box :=
  sound_of_literal_split component42Node6Box component42Node3Box component42Node5Box
    .chi (29/256) (by rfl) (by rfl)
    component42Node3_sound component42Node5_sound

private noncomputable def component42Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node7_sound : Sound component42Node7Box :=
  sound_of_literal_split component42Node7Box component42Node2Box component42Node6Box
    .k (61/16) (by rfl) (by rfl)
    component42Node2_sound component42Node6_sound

private noncomputable def component42Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node8_sound : Sound component42Node8Box :=
  sound_of_literal_split component42Node8Box leaf1880Box leaf1881Box
    .chi (61/512) (by rfl) (by rfl)
    leaf1880FlatSound leaf1881FlatSound

private noncomputable def component42Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node9_sound : Sound component42Node9Box :=
  sound_of_literal_split component42Node9Box leaf1879Box component42Node8Box
    .k (121/32) (by rfl) (by rfl)
    leaf1879FlatSound component42Node8_sound

private noncomputable def component42Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node10_sound : Sound component42Node10Box :=
  sound_of_literal_split component42Node10Box leaf1882Box leaf1883Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1882FlatSound leaf1883FlatSound

private noncomputable def component42Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node11_sound : Sound component42Node11Box :=
  sound_of_literal_split component42Node11Box leaf1884Box leaf1885Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1884FlatSound leaf1885FlatSound

private noncomputable def component42Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node12_sound : Sound component42Node12Box :=
  sound_of_literal_split component42Node12Box component42Node10Box component42Node11Box
    .k (121/32) (by rfl) (by rfl)
    component42Node10_sound component42Node11_sound

private noncomputable def component42Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node13_sound : Sound component42Node13Box :=
  sound_of_literal_split component42Node13Box component42Node9Box component42Node12Box
    .chi (31/256) (by rfl) (by rfl)
    component42Node9_sound component42Node12_sound

private noncomputable def component42Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node14_sound : Sound component42Node14Box :=
  sound_of_literal_split component42Node14Box leaf1886Box leaf1887Box
    .chi (61/512) (by rfl) (by rfl)
    leaf1886FlatSound leaf1887FlatSound

private noncomputable def component42Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node15_sound : Sound component42Node15Box :=
  sound_of_literal_split component42Node15Box leaf1888Box leaf1889Box
    .chi (61/512) (by rfl) (by rfl)
    leaf1888FlatSound leaf1889FlatSound

private noncomputable def component42Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node16_sound : Sound component42Node16Box :=
  sound_of_literal_split component42Node16Box component42Node14Box component42Node15Box
    .k (123/32) (by rfl) (by rfl)
    component42Node14_sound component42Node15_sound

private noncomputable def component42Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node17_sound : Sound component42Node17Box :=
  sound_of_literal_split component42Node17Box leaf1890Box leaf1891Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1890FlatSound leaf1891FlatSound

private noncomputable def component42Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node18_sound : Sound component42Node18Box :=
  sound_of_literal_split component42Node18Box leaf1892Box leaf1893Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1892FlatSound leaf1893FlatSound

private noncomputable def component42Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node19_sound : Sound component42Node19Box :=
  sound_of_literal_split component42Node19Box component42Node17Box component42Node18Box
    .k (123/32) (by rfl) (by rfl)
    component42Node17_sound component42Node18_sound

private noncomputable def component42Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node20_sound : Sound component42Node20Box :=
  sound_of_literal_split component42Node20Box component42Node16Box component42Node19Box
    .chi (31/256) (by rfl) (by rfl)
    component42Node16_sound component42Node19_sound

private noncomputable def component42Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node21_sound : Sound component42Node21Box :=
  sound_of_literal_split component42Node21Box component42Node13Box component42Node20Box
    .k (61/16) (by rfl) (by rfl)
    component42Node13_sound component42Node20_sound

private noncomputable def component42Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node22_sound : Sound component42Node22Box :=
  sound_of_literal_split component42Node22Box component42Node7Box component42Node21Box
    .chi (15/128) (by rfl) (by rfl)
    component42Node7_sound component42Node21_sound

private noncomputable def component42Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node23_sound : Sound component42Node23Box :=
  sound_of_literal_split component42Node23Box leaf1894Box leaf1895Box
    .chi (57/512) (by rfl) (by rfl)
    leaf1894FlatSound leaf1895FlatSound

private noncomputable def component42Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node24_sound : Sound component42Node24Box :=
  sound_of_literal_split component42Node24Box leaf1896Box leaf1897Box
    .chi (57/512) (by rfl) (by rfl)
    leaf1896FlatSound leaf1897FlatSound

private noncomputable def component42Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node25_sound : Sound component42Node25Box :=
  sound_of_literal_split component42Node25Box component42Node23Box component42Node24Box
    .k (125/32) (by rfl) (by rfl)
    component42Node23_sound component42Node24_sound

private noncomputable def component42Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node26_sound : Sound component42Node26Box :=
  sound_of_literal_split component42Node26Box leaf1898Box leaf1899Box
    .chi (59/512) (by rfl) (by rfl)
    leaf1898FlatSound leaf1899FlatSound

private noncomputable def component42Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node27_sound : Sound component42Node27Box :=
  sound_of_literal_split component42Node27Box leaf1900Box leaf1901Box
    .chi (59/512) (by rfl) (by rfl)
    leaf1900FlatSound leaf1901FlatSound

private noncomputable def component42Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node28_sound : Sound component42Node28Box :=
  sound_of_literal_split component42Node28Box component42Node26Box component42Node27Box
    .k (125/32) (by rfl) (by rfl)
    component42Node26_sound component42Node27_sound

private noncomputable def component42Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node29_sound : Sound component42Node29Box :=
  sound_of_literal_split component42Node29Box component42Node25Box component42Node28Box
    .chi (29/256) (by rfl) (by rfl)
    component42Node25_sound component42Node28_sound

private noncomputable def component42Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node30_sound : Sound component42Node30Box :=
  sound_of_literal_split component42Node30Box leaf1902Box leaf1903Box
    .chi (57/512) (by rfl) (by rfl)
    leaf1902FlatSound leaf1903FlatSound

private noncomputable def component42Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node31_sound : Sound component42Node31Box :=
  sound_of_literal_split component42Node31Box leaf1904Box leaf1905Box
    .chi (57/512) (by rfl) (by rfl)
    leaf1904FlatSound leaf1905FlatSound

private noncomputable def component42Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node32_sound : Sound component42Node32Box :=
  sound_of_literal_split component42Node32Box component42Node30Box component42Node31Box
    .k (127/32) (by rfl) (by rfl)
    component42Node30_sound component42Node31_sound

private noncomputable def component42Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node33_sound : Sound component42Node33Box :=
  sound_of_literal_split component42Node33Box leaf1906Box leaf1907Box
    .chi (59/512) (by rfl) (by rfl)
    leaf1906FlatSound leaf1907FlatSound

private noncomputable def component42Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node34_sound : Sound component42Node34Box :=
  sound_of_literal_split component42Node34Box leaf1908Box leaf1909Box
    .chi (59/512) (by rfl) (by rfl)
    leaf1908FlatSound leaf1909FlatSound

private noncomputable def component42Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node35_sound : Sound component42Node35Box :=
  sound_of_literal_split component42Node35Box component42Node33Box component42Node34Box
    .k (127/32) (by rfl) (by rfl)
    component42Node33_sound component42Node34_sound

private noncomputable def component42Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node36_sound : Sound component42Node36Box :=
  sound_of_literal_split component42Node36Box component42Node32Box component42Node35Box
    .chi (29/256) (by rfl) (by rfl)
    component42Node32_sound component42Node35_sound

private noncomputable def component42Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component42Node37_sound : Sound component42Node37Box :=
  sound_of_literal_split component42Node37Box component42Node29Box component42Node36Box
    .k (63/16) (by rfl) (by rfl)
    component42Node29_sound component42Node36_sound

private noncomputable def component42Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node38_sound : Sound component42Node38Box :=
  sound_of_literal_split component42Node38Box leaf1910Box leaf1911Box
    .chi (61/512) (by rfl) (by rfl)
    leaf1910FlatSound leaf1911FlatSound

private noncomputable def component42Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node39_sound : Sound component42Node39Box :=
  sound_of_literal_split component42Node39Box leaf1912Box leaf1913Box
    .chi (61/512) (by rfl) (by rfl)
    leaf1912FlatSound leaf1913FlatSound

private noncomputable def component42Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node40_sound : Sound component42Node40Box :=
  sound_of_literal_split component42Node40Box component42Node38Box component42Node39Box
    .k (125/32) (by rfl) (by rfl)
    component42Node38_sound component42Node39_sound

private noncomputable def component42Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node41_sound : Sound component42Node41Box :=
  sound_of_literal_split component42Node41Box leaf1914Box leaf1915Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1914FlatSound leaf1915FlatSound

private noncomputable def component42Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node42_sound : Sound component42Node42Box :=
  sound_of_literal_split component42Node42Box leaf1916Box leaf1917Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1916FlatSound leaf1917FlatSound

private noncomputable def component42Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node43_sound : Sound component42Node43Box :=
  sound_of_literal_split component42Node43Box component42Node41Box component42Node42Box
    .k (125/32) (by rfl) (by rfl)
    component42Node41_sound component42Node42_sound

private noncomputable def component42Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node44_sound : Sound component42Node44Box :=
  sound_of_literal_split component42Node44Box component42Node40Box component42Node43Box
    .chi (31/256) (by rfl) (by rfl)
    component42Node40_sound component42Node43_sound

private noncomputable def component42Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node45_sound : Sound component42Node45Box :=
  sound_of_literal_split component42Node45Box leaf1918Box leaf1919Box
    .chi (61/512) (by rfl) (by rfl)
    leaf1918FlatSound leaf1919FlatSound

private noncomputable def component42Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node46_sound : Sound component42Node46Box :=
  sound_of_literal_split component42Node46Box leaf1920Box leaf1921Box
    .chi (61/512) (by rfl) (by rfl)
    leaf1920FlatSound leaf1921FlatSound

private noncomputable def component42Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/128), chiHi := (31/256) }

set_option maxRecDepth 1000000 in
private theorem component42Node47_sound : Sound component42Node47Box :=
  sound_of_literal_split component42Node47Box component42Node45Box component42Node46Box
    .k (127/32) (by rfl) (by rfl)
    component42Node45_sound component42Node46_sound

private noncomputable def component42Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node48_sound : Sound component42Node48Box :=
  sound_of_literal_split component42Node48Box leaf1922Box leaf1923Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1922FlatSound leaf1923FlatSound

private noncomputable def component42Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node49_sound : Sound component42Node49Box :=
  sound_of_literal_split component42Node49Box leaf1924Box leaf1925Box
    .chi (63/512) (by rfl) (by rfl)
    leaf1924FlatSound leaf1925FlatSound

private noncomputable def component42Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (31/256), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node50_sound : Sound component42Node50Box :=
  sound_of_literal_split component42Node50Box component42Node48Box component42Node49Box
    .k (127/32) (by rfl) (by rfl)
    component42Node48_sound component42Node49_sound

private noncomputable def component42Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node51_sound : Sound component42Node51Box :=
  sound_of_literal_split component42Node51Box component42Node47Box component42Node50Box
    .chi (31/256) (by rfl) (by rfl)
    component42Node47_sound component42Node50_sound

private noncomputable def component42Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node52_sound : Sound component42Node52Box :=
  sound_of_literal_split component42Node52Box component42Node44Box component42Node51Box
    .k (63/16) (by rfl) (by rfl)
    component42Node44_sound component42Node51_sound

private noncomputable def component42Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component42Node53_sound : Sound component42Node53Box :=
  sound_of_literal_split component42Node53Box component42Node37Box component42Node52Box
    .chi (15/128) (by rfl) (by rfl)
    component42Node37_sound component42Node52_sound

noncomputable def component42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component42_sound : Sound component42Box :=
  sound_of_literal_split component42Box component42Node22Box component42Node53Box
    .k (31/8) (by rfl) (by rfl)
    component42Node22_sound component42Node53_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
