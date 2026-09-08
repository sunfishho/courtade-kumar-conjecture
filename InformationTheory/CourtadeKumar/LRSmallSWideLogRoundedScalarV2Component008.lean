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

private noncomputable def leaf317Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf317Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (44006727/33554432) }, upper := { exponent := 0, mantissa := (701/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777043/16776838) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf317InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf317LocalValidity :
    LeafFacts leaf317Box leaf317Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf317Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388419) }) = true
      norm_num [leaf317Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf317CertificateValid :
    WideCertificateValid leaf317Box leaf317Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi46ValidityFacts
    leaf317LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf317CoverageChecked :
    coverageCheck (innerAD leaf317Box) leaf317InnerLog = true := by
  rfl'

private theorem leaf317InnerLogValid :
    leaf317InnerLog.Valid 8 (innerAD leaf317Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf317CoverageChecked

private noncomputable def leaf317InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf317InputLogOnePlusV_eq :
    leaf317InputLogOnePlusV = outerEnclosure 24
      (leaf317Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf317RoundedFacts : LeafRoundedFacts 8
    leaf317Certificate.logOnePlusV leaf317InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf317InputLogOnePlusV_eq }

private noncomputable def leaf317Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi46InputQChi innerPair17Input
    leaf317InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf317LowerChecked :
    lowerCheck 24 leaf317Box leaf317Inputs = true := by
  rfl'

private theorem leaf317CoversExact : CoversExact 8
    leaf317Box leaf317Certificate leaf317InnerLog leaf317Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi46RoundedFacts
    innerPair17RoundedFacts leaf317RoundedFacts (by rfl)

private theorem leaf317FlatSound : Sound leaf317Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf317CertificateValid
    leaf317InnerLogValid leaf317CoversExact leaf317LowerChecked

private noncomputable def leaf318Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf318Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554493/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (45317365/33554432) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388511/8388398) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf318InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf318LocalValidity :
    LeafFacts leaf318Box leaf318Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf318Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194199) }) = true
      norm_num [leaf318Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf318CertificateValid :
    WideCertificateValid leaf318Box leaf318Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi47ValidityFacts
    leaf318LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf318CoverageChecked :
    coverageCheck (innerAD leaf318Box) leaf318InnerLog = true := by
  rfl'

private theorem leaf318InnerLogValid :
    leaf318InnerLog.Valid 8 (innerAD leaf318Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf318CoverageChecked

private noncomputable def leaf318InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf318InputLogOnePlusV_eq :
    leaf318InputLogOnePlusV = outerEnclosure 24
      (leaf318Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf318RoundedFacts : LeafRoundedFacts 8
    leaf318Certificate.logOnePlusV leaf318InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf318InputLogOnePlusV_eq }

private noncomputable def leaf318Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi47InputQChi innerPair22Input
    leaf318InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf318LowerChecked :
    lowerCheck 24 leaf318Box leaf318Inputs = true := by
  rfl'

private theorem leaf318CoversExact : CoversExact 8
    leaf318Box leaf318Certificate leaf318InnerLog leaf318Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi47RoundedFacts
    innerPair22RoundedFacts leaf318RoundedFacts (by rfl)

private theorem leaf318FlatSound : Sound leaf318Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf318CertificateValid
    leaf318InnerLogValid leaf318CoversExact leaf318LowerChecked

private noncomputable def leaf319Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf319Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554493/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194205) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (44530981/33554432) }, upper := { exponent := 0, mantissa := (355/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388517/8388410) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf319InnerLog : WideLogData :=
  innerPair24Data

set_option maxRecDepth 1000000 in
private theorem leaf319LocalValidity :
    LeafFacts leaf319Box leaf319Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf319Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194205) }) = true
      norm_num [leaf319Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf319CertificateValid :
    WideCertificateValid leaf319Box leaf319Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi46ValidityFacts
    leaf319LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf319CoverageChecked :
    coverageCheck (innerAD leaf319Box) leaf319InnerLog = true := by
  rfl'

private theorem leaf319InnerLogValid :
    leaf319InnerLog.Valid 8 (innerAD leaf319Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint34PositiveFacts.valid leaf319CoverageChecked

private noncomputable def leaf319InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf319InputLogOnePlusV_eq :
    leaf319InputLogOnePlusV = outerEnclosure 24
      (leaf319Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf319RoundedFacts : LeafRoundedFacts 8
    leaf319Certificate.logOnePlusV leaf319InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf319InputLogOnePlusV_eq }

private noncomputable def leaf319Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi46InputQChi innerPair24Input
    leaf319InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf319LowerChecked :
    lowerCheck 24 leaf319Box leaf319Inputs = true := by
  rfl'

private theorem leaf319CoversExact : CoversExact 8
    leaf319Box leaf319Certificate leaf319InnerLog leaf319Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi46RoundedFacts
    innerPair24RoundedFacts leaf319RoundedFacts (by rfl)

private theorem leaf319FlatSound : Sound leaf319Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf319CertificateValid
    leaf319InnerLogValid leaf319CoversExact leaf319LowerChecked

private noncomputable def leaf320Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf320Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554495/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (45907151/33554432) }, upper := { exponent := 0, mantissa := (183/128) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194253/4194194) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf320InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf320LocalValidity :
    LeafFacts leaf320Box leaf320Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf320Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097097) }) = true
      norm_num [leaf320Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf320CertificateValid :
    WideCertificateValid leaf320Box leaf320Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi47ValidityFacts
    leaf320LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf320CoverageChecked :
    coverageCheck (innerAD leaf320Box) leaf320InnerLog = true := by
  rfl'

private theorem leaf320InnerLogValid :
    leaf320InnerLog.Valid 8 (innerAD leaf320Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf320CoverageChecked

private noncomputable def leaf320InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf320InputLogOnePlusV_eq :
    leaf320InputLogOnePlusV = outerEnclosure 24
      (leaf320Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf320RoundedFacts : LeafRoundedFacts 8
    leaf320Certificate.logOnePlusV leaf320InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf320InputLogOnePlusV_eq }

private noncomputable def leaf320Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi47InputQChi innerPair22Input
    leaf320InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf320LowerChecked :
    lowerCheck 24 leaf320Box leaf320Inputs = true := by
  rfl'

private theorem leaf320CoversExact : CoversExact 8
    leaf320Box leaf320Certificate leaf320InnerLog leaf320Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi47RoundedFacts
    innerPair22RoundedFacts leaf320RoundedFacts (by rfl)

private theorem leaf320FlatSound : Sound leaf320Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf320CertificateValid
    leaf320InnerLogValid leaf320CoversExact leaf320LowerChecked

private noncomputable def leaf321Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf321Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554495/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388377) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (46628003/33554432) }, upper := { exponent := 0, mantissa := (743/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777001/16776754) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf321InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf321LocalValidity :
    LeafFacts leaf321Box leaf321Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf321Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388377) }) = true
      norm_num [leaf321Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf321CertificateValid :
    WideCertificateValid leaf321Box leaf321Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi48ValidityFacts
    leaf321LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf321CoverageChecked :
    coverageCheck (innerAD leaf321Box) leaf321InnerLog = true := by
  rfl'

private theorem leaf321InnerLogValid :
    leaf321InnerLog.Valid 8 (innerAD leaf321Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf321CoverageChecked

private noncomputable def leaf321InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf321InputLogOnePlusV_eq :
    leaf321InputLogOnePlusV = outerEnclosure 24
      (leaf321Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf321RoundedFacts : LeafRoundedFacts 8
    leaf321Certificate.logOnePlusV leaf321InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf321InputLogOnePlusV_eq }

private noncomputable def leaf321Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi48InputQChi innerPair27Input
    leaf321InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf321LowerChecked :
    lowerCheck 24 leaf321Box leaf321Inputs = true := by
  rfl'

private theorem leaf321CoversExact : CoversExact 8
    leaf321Box leaf321Certificate leaf321InnerLog leaf321Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi48RoundedFacts
    innerPair27RoundedFacts leaf321RoundedFacts (by rfl)

private theorem leaf321FlatSound : Sound leaf321Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf321CertificateValid
    leaf321InnerLogValid leaf321CoversExact leaf321LowerChecked

private noncomputable def leaf322Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf322Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554497/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358706176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (47938641/33554432) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717985791/68717412352) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf322InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf322LocalValidity :
    LeafFacts leaf322Box leaf322Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf322Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358706176) }) = true
      norm_num [leaf322Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf322CertificateValid :
    WideCertificateValid leaf322Box leaf322Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi49ValidityFacts
    leaf322LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf322CoverageChecked :
    coverageCheck (innerAD leaf322Box) leaf322InnerLog = true := by
  rfl'

private theorem leaf322InnerLogValid :
    leaf322InnerLog.Valid 8 (innerAD leaf322Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf322CoverageChecked

private noncomputable def leaf322InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf322InputLogOnePlusV_eq :
    leaf322InputLogOnePlusV = outerEnclosure 24
      (leaf322Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf322RoundedFacts : LeafRoundedFacts 8
    leaf322Certificate.logOnePlusV leaf322InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf322InputLogOnePlusV_eq }

private noncomputable def leaf322Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi49InputQChi innerPair27Input
    leaf322InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf322LowerChecked :
    lowerCheck 24 leaf322Box leaf322Inputs = true := by
  rfl'

private theorem leaf322CoversExact : CoversExact 8
    leaf322Box leaf322Certificate leaf322InnerLog leaf322Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi49RoundedFacts
    innerPair27RoundedFacts leaf322RoundedFacts (by rfl)

private theorem leaf322FlatSound : Sound leaf322Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf322CertificateValid
    leaf322InnerLogValid leaf322CoversExact leaf322LowerChecked

private noncomputable def leaf323Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf323Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554497/33554432) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452915712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (47283321/33554432) }, upper := { exponent := 0, mantissa := (377/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22906008917/22905831424) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf323InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf323LocalValidity :
    LeafFacts leaf323Box leaf323Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf323Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452915712) }) = true
      norm_num [leaf323Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf323CertificateValid :
    WideCertificateValid leaf323Box leaf323Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi48ValidityFacts
    leaf323LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf323CoverageChecked :
    coverageCheck (innerAD leaf323Box) leaf323InnerLog = true := by
  rfl'

private theorem leaf323InnerLogValid :
    leaf323InnerLog.Valid 8 (innerAD leaf323Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf323CoverageChecked

private noncomputable def leaf323InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf323InputLogOnePlusV_eq :
    leaf323InputLogOnePlusV = outerEnclosure 24
      (leaf323Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf323RoundedFacts : LeafRoundedFacts 8
    leaf323Certificate.logOnePlusV leaf323InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf323InputLogOnePlusV_eq }

private noncomputable def leaf323Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi48InputQChi innerPair27Input
    leaf323InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf323LowerChecked :
    lowerCheck 24 leaf323Box leaf323Inputs = true := by
  rfl'

private theorem leaf323CoversExact : CoversExact 8
    leaf323Box leaf323Certificate leaf323InnerLog leaf323Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi48RoundedFacts
    innerPair27RoundedFacts leaf323RoundedFacts (by rfl)

private theorem leaf323FlatSound : Sound leaf323Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf323CertificateValid
    leaf323InnerLogValid leaf323CoversExact leaf323LowerChecked

private noncomputable def leaf324Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf324Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554499/33554432) }, vSqrt := { lower := (65533/65536), upper := (2021134095/2021097472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (48659491/33554432) }, upper := { exponent := 0, mantissa := (97/64) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4042231567/4042194944) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf324InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf324LocalValidity :
    LeafFacts leaf324Box leaf324Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf324Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2021134095/2021097472) }) = true
      norm_num [leaf324Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf324CertificateValid :
    WideCertificateValid leaf324Box leaf324Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi49ValidityFacts
    leaf324LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf324CoverageChecked :
    coverageCheck (innerAD leaf324Box) leaf324InnerLog = true := by
  rfl'

private theorem leaf324InnerLogValid :
    leaf324InnerLog.Valid 8 (innerAD leaf324Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf324CoverageChecked

private noncomputable def leaf324InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf324InputLogOnePlusV_eq :
    leaf324InputLogOnePlusV = outerEnclosure 24
      (leaf324Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf324RoundedFacts : LeafRoundedFacts 8
    leaf324Certificate.logOnePlusV leaf324InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf324InputLogOnePlusV_eq }

private noncomputable def leaf324Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi49InputQChi innerPair35Input
    leaf324InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf324LowerChecked :
    lowerCheck 24 leaf324Box leaf324Inputs = true := by
  rfl'

private theorem leaf324CoversExact : CoversExact 8
    leaf324Box leaf324Certificate leaf324InnerLog leaf324Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi49RoundedFacts
    innerPair35RoundedFacts leaf324RoundedFacts (by rfl)

private theorem leaf324FlatSound : Sound leaf324Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf324CertificateValid
    leaf324InnerLogValid leaf324CoversExact leaf324LowerChecked

private noncomputable def leaf325Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (45/32), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf325Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108971/67108864) }, vSqrt := { lower := (65533/65536), upper := (16777232/16776811) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (90143255/67108864) }, upper := { exponent := 0, mantissa := (1429/1024) } }, logOuter := sk53LogOuterCertificate, logK := sk53LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (33554043/33553622) } }, logDArg := sk53LogDArgCertificate }

private noncomputable def leaf325InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf325LocalValidity :
    LeafFacts leaf325Box leaf325Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf325Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (16777232/16776811) }) = true
      norm_num [leaf325Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf325CertificateValid :
    WideCertificateValid leaf325Box leaf325Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk53ValidityFacts chi46ValidityFacts
    leaf325LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf325CoverageChecked :
    coverageCheck (innerAD leaf325Box) leaf325InnerLog = true := by
  rfl'

private theorem leaf325InnerLogValid :
    leaf325InnerLog.Valid 8 (innerAD leaf325Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf325CoverageChecked

private noncomputable def leaf325InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf325InputLogOnePlusV_eq :
    leaf325InputLogOnePlusV = outerEnclosure 24
      (leaf325Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf325RoundedFacts : LeafRoundedFacts 8
    leaf325Certificate.logOnePlusV leaf325InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf325InputLogOnePlusV_eq }

private noncomputable def leaf325Inputs : Inputs :=
  inputsOfCaches globalInput sk53RoundedInputs
    chi46InputQChi innerPair22Input
    leaf325InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf325LowerChecked :
    lowerCheck 24 leaf325Box leaf325Inputs = true := by
  rfl'

private theorem leaf325CoversExact : CoversExact 8
    leaf325Box leaf325Certificate leaf325InnerLog leaf325Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk53RoundedFacts chi46RoundedFacts
    innerPair22RoundedFacts leaf325RoundedFacts (by rfl)

private theorem leaf325FlatSound : Sound leaf325Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf325CertificateValid
    leaf325InnerLogValid leaf325CoversExact leaf325LowerChecked

private noncomputable def leaf326Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/32), kHi := (23/16), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf326Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108973/67108864) }, vSqrt := { lower := (65533/65536), upper := (8388616/8388401) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (90667509/67108864) }, upper := { exponent := 0, mantissa := (719/512) } }, logOuter := sk54LogOuterCertificate, logK := sk54LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777017/16776802) } }, logDArg := sk54LogDArgCertificate }

private noncomputable def leaf326InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf326LocalValidity :
    LeafFacts leaf326Box leaf326Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf326Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388616/8388401) }) = true
      norm_num [leaf326Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf326CertificateValid :
    WideCertificateValid leaf326Box leaf326Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk54ValidityFacts chi46ValidityFacts
    leaf326LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf326CoverageChecked :
    coverageCheck (innerAD leaf326Box) leaf326InnerLog = true := by
  rfl'

private theorem leaf326InnerLogValid :
    leaf326InnerLog.Valid 8 (innerAD leaf326Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf326CoverageChecked

private noncomputable def leaf326InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf326InputLogOnePlusV_eq :
    leaf326InputLogOnePlusV = outerEnclosure 24
      (leaf326Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf326RoundedFacts : LeafRoundedFacts 8
    leaf326Certificate.logOnePlusV leaf326InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf326InputLogOnePlusV_eq }

private noncomputable def leaf326Inputs : Inputs :=
  inputsOfCaches globalInput sk54RoundedInputs
    chi46InputQChi innerPair22Input
    leaf326InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf326LowerChecked :
    lowerCheck 24 leaf326Box leaf326Inputs = true := by
  rfl'

private theorem leaf326CoversExact : CoversExact 8
    leaf326Box leaf326Certificate leaf326InnerLog leaf326Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk54RoundedFacts chi46RoundedFacts
    innerPair22RoundedFacts leaf326RoundedFacts (by rfl)

private theorem leaf326FlatSound : Sound leaf326Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf326CertificateValid
    leaf326InnerLogValid leaf326CoversExact leaf326LowerChecked

private noncomputable def leaf327Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (45/32), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf327Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108973/67108864) }, vSqrt := { lower := (65533/65536), upper := (8388616/8388383) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (93026661/67108864) }, upper := { exponent := 0, mantissa := (737/512) } }, logOuter := sk53LogOuterCertificate, logK := sk53LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16776999/16776766) } }, logDArg := sk53LogDArgCertificate }

private noncomputable def leaf327InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf327LocalValidity :
    LeafFacts leaf327Box leaf327Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf327Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388616/8388383) }) = true
      norm_num [leaf327Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf327CertificateValid :
    WideCertificateValid leaf327Box leaf327Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk53ValidityFacts chi47ValidityFacts
    leaf327LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf327CoverageChecked :
    coverageCheck (innerAD leaf327Box) leaf327InnerLog = true := by
  rfl'

private theorem leaf327InnerLogValid :
    leaf327InnerLog.Valid 8 (innerAD leaf327Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf327CoverageChecked

private noncomputable def leaf327InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf327InputLogOnePlusV_eq :
    leaf327InputLogOnePlusV = outerEnclosure 24
      (leaf327Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf327RoundedFacts : LeafRoundedFacts 8
    leaf327Certificate.logOnePlusV leaf327InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf327InputLogOnePlusV_eq }

private noncomputable def leaf327Inputs : Inputs :=
  inputsOfCaches globalInput sk53RoundedInputs
    chi47InputQChi innerPair27Input
    leaf327InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf327LowerChecked :
    lowerCheck 24 leaf327Box leaf327Inputs = true := by
  rfl'

private theorem leaf327CoversExact : CoversExact 8
    leaf327Box leaf327Certificate leaf327InnerLog leaf327Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk53RoundedFacts chi47RoundedFacts
    innerPair27RoundedFacts leaf327RoundedFacts (by rfl)

private theorem leaf327FlatSound : Sound leaf327Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf327CertificateValid
    leaf327InnerLogValid leaf327CoversExact leaf327LowerChecked

private noncomputable def leaf328Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/32), kHi := (23/16), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf328Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108975/67108864) }, vSqrt := { lower := (65533/65536), upper := (246724/246717) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (93616447/67108864) }, upper := { exponent := 0, mantissa := (371/256) } }, logOuter := sk54LogOuterCertificate, logK := sk54LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (493441/493434) } }, logDArg := sk54LogDArgCertificate }

private noncomputable def leaf328InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf328LocalValidity :
    LeafFacts leaf328Box leaf328Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf328Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (246724/246717) }) = true
      norm_num [leaf328Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf328CertificateValid :
    WideCertificateValid leaf328Box leaf328Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk54ValidityFacts chi47ValidityFacts
    leaf328LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf328CoverageChecked :
    coverageCheck (innerAD leaf328Box) leaf328InnerLog = true := by
  rfl'

private theorem leaf328InnerLogValid :
    leaf328InnerLog.Valid 8 (innerAD leaf328Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf328CoverageChecked

private noncomputable def leaf328InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf328InputLogOnePlusV_eq :
    leaf328InputLogOnePlusV = outerEnclosure 24
      (leaf328Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf328RoundedFacts : LeafRoundedFacts 8
    leaf328Certificate.logOnePlusV leaf328InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf328InputLogOnePlusV_eq }

private noncomputable def leaf328Inputs : Inputs :=
  inputsOfCaches globalInput sk54RoundedInputs
    chi47InputQChi innerPair27Input
    leaf328InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf328LowerChecked :
    lowerCheck 24 leaf328Box leaf328Inputs = true := by
  rfl'

private theorem leaf328CoversExact : CoversExact 8
    leaf328Box leaf328Certificate leaf328InnerLog leaf328Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk54RoundedFacts chi47RoundedFacts
    innerPair27RoundedFacts leaf328RoundedFacts (by rfl)

private theorem leaf328FlatSound : Sound leaf328Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf328CertificateValid
    leaf328InnerLogValid leaf328CoversExact leaf328LowerChecked

private noncomputable def leaf329Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (47/32), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf329Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108975/67108864) }, vSqrt := { lower := (65533/65536), upper := (16777232/16776793) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (91191763/67108864) }, upper := { exponent := 0, mantissa := (1447/1024) } }, logOuter := sk29LogOuterCertificate, logK := sk29LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (33554025/33553586) } }, logDArg := sk29LogDArgCertificate }

private noncomputable def leaf329InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf329LocalValidity :
    LeafFacts leaf329Box leaf329Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf329Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (16777232/16776793) }) = true
      norm_num [leaf329Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf329CertificateValid :
    WideCertificateValid leaf329Box leaf329Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk29ValidityFacts chi46ValidityFacts
    leaf329LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf329CoverageChecked :
    coverageCheck (innerAD leaf329Box) leaf329InnerLog = true := by
  rfl'

private theorem leaf329InnerLogValid :
    leaf329InnerLog.Valid 8 (innerAD leaf329Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf329CoverageChecked

private noncomputable def leaf329InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf329InputLogOnePlusV_eq :
    leaf329InputLogOnePlusV = outerEnclosure 24
      (leaf329Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf329RoundedFacts : LeafRoundedFacts 8
    leaf329Certificate.logOnePlusV leaf329InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf329InputLogOnePlusV_eq }

private noncomputable def leaf329Inputs : Inputs :=
  inputsOfCaches globalInput sk29RoundedInputs
    chi46InputQChi innerPair22Input
    leaf329InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf329LowerChecked :
    lowerCheck 24 leaf329Box leaf329Inputs = true := by
  rfl'

private theorem leaf329CoversExact : CoversExact 8
    leaf329Box leaf329Certificate leaf329InnerLog leaf329Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk29RoundedFacts chi46RoundedFacts
    innerPair22RoundedFacts leaf329RoundedFacts (by rfl)

private theorem leaf329FlatSound : Sound leaf329Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf329CertificateValid
    leaf329InnerLogValid leaf329CoversExact leaf329LowerChecked

private noncomputable def leaf330Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/32), kHi := (3/2), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf330Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108977/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048577/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (91716017/67108864) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk30LogOuterCertificate, logK := sk30LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1048563/1048549) } }, logDArg := sk30LogDArgCertificate }

private noncomputable def leaf330InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf330LocalValidity :
    LeafFacts leaf330Box leaf330Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf330Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048577/1048549) }) = true
      norm_num [leaf330Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf330CertificateValid :
    WideCertificateValid leaf330Box leaf330Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk30ValidityFacts chi46ValidityFacts
    leaf330LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf330CoverageChecked :
    coverageCheck (innerAD leaf330Box) leaf330InnerLog = true := by
  rfl'

private theorem leaf330InnerLogValid :
    leaf330InnerLog.Valid 8 (innerAD leaf330Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf330CoverageChecked

private noncomputable def leaf330InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf330InputLogOnePlusV_eq :
    leaf330InputLogOnePlusV = outerEnclosure 24
      (leaf330Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf330RoundedFacts : LeafRoundedFacts 8
    leaf330Certificate.logOnePlusV leaf330InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf330InputLogOnePlusV_eq }

private noncomputable def leaf330Inputs : Inputs :=
  inputsOfCaches globalInput sk30RoundedInputs
    chi46InputQChi innerPair22Input
    leaf330InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf330LowerChecked :
    lowerCheck 24 leaf330Box leaf330Inputs = true := by
  rfl'

private theorem leaf330CoversExact : CoversExact 8
    leaf330Box leaf330Certificate leaf330InnerLog leaf330Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk30RoundedFacts chi46RoundedFacts
    innerPair22RoundedFacts leaf330RoundedFacts (by rfl)

private theorem leaf330FlatSound : Sound leaf330Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf330CertificateValid
    leaf330InnerLogValid leaf330CoversExact leaf330LowerChecked

private noncomputable def leaf331Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (47/32), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf331Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108977/67108864) }, vSqrt := { lower := (65533/65536), upper := (8388616/8388373) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (94206233/67108864) }, upper := { exponent := 0, mantissa := (747/512) } }, logOuter := sk29LogOuterCertificate, logK := sk29LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16776989/16776746) } }, logDArg := sk29LogDArgCertificate }

private noncomputable def leaf331InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf331LocalValidity :
    LeafFacts leaf331Box leaf331Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf331Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388616/8388373) }) = true
      norm_num [leaf331Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf331CertificateValid :
    WideCertificateValid leaf331Box leaf331Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk29ValidityFacts chi47ValidityFacts
    leaf331LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf331CoverageChecked :
    coverageCheck (innerAD leaf331Box) leaf331InnerLog = true := by
  rfl'

private theorem leaf331InnerLogValid :
    leaf331InnerLog.Valid 8 (innerAD leaf331Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf331CoverageChecked

private noncomputable def leaf331InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907331/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf331InputLogOnePlusV_eq :
    leaf331InputLogOnePlusV = outerEnclosure 24
      (leaf331Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf331RoundedFacts : LeafRoundedFacts 8
    leaf331Certificate.logOnePlusV leaf331InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf331InputLogOnePlusV_eq }

private noncomputable def leaf331Inputs : Inputs :=
  inputsOfCaches globalInput sk29RoundedInputs
    chi47InputQChi innerPair27Input
    leaf331InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf331LowerChecked :
    lowerCheck 24 leaf331Box leaf331Inputs = true := by
  rfl'

private theorem leaf331CoversExact : CoversExact 8
    leaf331Box leaf331Certificate leaf331InnerLog leaf331Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk29RoundedFacts chi47RoundedFacts
    innerPair27RoundedFacts leaf331RoundedFacts (by rfl)

private theorem leaf331FlatSound : Sound leaf331Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf331CertificateValid
    leaf331InnerLogValid leaf331CoversExact leaf331LowerChecked

private noncomputable def leaf332Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/32), kHi := (3/2), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf332Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108979/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048577/1048546) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (94796019/67108864) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk30LogOuterCertificate, logK := sk30LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097123/2097092) } }, logDArg := sk30LogDArgCertificate }

private noncomputable def leaf332InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf332LocalValidity :
    LeafFacts leaf332Box leaf332Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf332Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048577/1048546) }) = true
      norm_num [leaf332Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf332CertificateValid :
    WideCertificateValid leaf332Box leaf332Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk30ValidityFacts chi47ValidityFacts
    leaf332LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf332CoverageChecked :
    coverageCheck (innerAD leaf332Box) leaf332InnerLog = true := by
  rfl'

private theorem leaf332InnerLogValid :
    leaf332InnerLog.Valid 8 (innerAD leaf332Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf332CoverageChecked

private noncomputable def leaf332InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf332InputLogOnePlusV_eq :
    leaf332InputLogOnePlusV = outerEnclosure 24
      (leaf332Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf332RoundedFacts : LeafRoundedFacts 8
    leaf332Certificate.logOnePlusV leaf332InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf332InputLogOnePlusV_eq }

private noncomputable def leaf332Inputs : Inputs :=
  inputsOfCaches globalInput sk30RoundedInputs
    chi47InputQChi innerPair27Input
    leaf332InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf332LowerChecked :
    lowerCheck 24 leaf332Box leaf332Inputs = true := by
  rfl'

private theorem leaf332CoversExact : CoversExact 8
    leaf332Box leaf332Certificate leaf332InnerLog leaf332Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk30RoundedFacts chi47RoundedFacts
    innerPair27RoundedFacts leaf332RoundedFacts (by rfl)

private theorem leaf332FlatSound : Sound leaf332Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf332CertificateValid
    leaf332InnerLogValid leaf332CoversExact leaf332LowerChecked

private noncomputable def leaf333Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf333Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554499/33554432) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871740416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (47938639/33554432) }, upper := { exponent := 0, mantissa := (765/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743596339/13743480832) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf333InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf333LocalValidity :
    LeafFacts leaf333Box leaf333Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf333Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871740416) }) = true
      norm_num [leaf333Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf333CertificateValid :
    WideCertificateValid leaf333Box leaf333Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi48ValidityFacts
    leaf333LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf333CoverageChecked :
    coverageCheck (innerAD leaf333Box) leaf333InnerLog = true := by
  rfl'

private theorem leaf333InnerLogValid :
    leaf333InnerLog.Valid 8 (innerAD leaf333Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf333CoverageChecked

private noncomputable def leaf333InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf333InputLogOnePlusV_eq :
    leaf333InputLogOnePlusV = outerEnclosure 24
      (leaf333Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf333RoundedFacts : LeafRoundedFacts 8
    leaf333Certificate.logOnePlusV leaf333InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf333InputLogOnePlusV_eq }

private noncomputable def leaf333Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi48InputQChi innerPair27Input
    leaf333InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf333LowerChecked :
    lowerCheck 24 leaf333Box leaf333Inputs = true := by
  rfl'

private theorem leaf333CoversExact : CoversExact 8
    leaf333Box leaf333Certificate leaf333InnerLog leaf333Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi48RoundedFacts
    innerPair27RoundedFacts leaf333RoundedFacts (by rfl)

private theorem leaf333FlatSound : Sound leaf333Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf333CertificateValid
    leaf333InnerLogValid leaf333CoversExact leaf333LowerChecked

private noncomputable def leaf334Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf334Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554501/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358607872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (49380341/33554432) }, upper := { exponent := 0, mantissa := (197/128) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717887487/68717215744) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf334InnerLog : WideLogData :=
  innerPair152Data

set_option maxRecDepth 1000000 in
private theorem leaf334LocalValidity :
    LeafFacts leaf334Box leaf334Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf334Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358607872) }) = true
      norm_num [leaf334Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf334CertificateValid :
    WideCertificateValid leaf334Box leaf334Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi49ValidityFacts
    leaf334LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf334CoverageChecked :
    coverageCheck (innerAD leaf334Box) leaf334InnerLog = true := by
  rfl'

private theorem leaf334InnerLogValid :
    leaf334InnerLog.Valid 8 (innerAD leaf334Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint43PositiveFacts.valid leaf334CoverageChecked

private noncomputable def leaf334InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf334InputLogOnePlusV_eq :
    leaf334InputLogOnePlusV = outerEnclosure 24
      (leaf334Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf334RoundedFacts : LeafRoundedFacts 8
    leaf334Certificate.logOnePlusV leaf334InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf334InputLogOnePlusV_eq }

private noncomputable def leaf334Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi49InputQChi innerPair152Input
    leaf334InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf334LowerChecked :
    lowerCheck 24 leaf334Box leaf334Inputs = true := by
  rfl'

private theorem leaf334CoversExact : CoversExact 8
    leaf334Box leaf334Certificate leaf334InnerLog leaf334Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi49RoundedFacts
    innerPair152RoundedFacts leaf334RoundedFacts (by rfl)

private theorem leaf334FlatSound : Sound leaf334Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf334CertificateValid
    leaf334InnerLogValid leaf334CoversExact leaf334LowerChecked

private noncomputable def leaf335Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (47/32), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf335Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108979/67108864) }, vSqrt := { lower := (65533/65536), upper := (22906164565/22905786368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (97220703/67108864) }, upper := { exponent := 0, mantissa := (1541/1024) } }, logOuter := sk29LogOuterCertificate, logK := sk29LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (45811950933/45811572736) } }, logDArg := sk29LogDArgCertificate }

private noncomputable def leaf335InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf335LocalValidity :
    LeafFacts leaf335Box leaf335Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf335Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (22906164565/22905786368) }) = true
      norm_num [leaf335Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf335CertificateValid :
    WideCertificateValid leaf335Box leaf335Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk29ValidityFacts chi48ValidityFacts
    leaf335LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf335CoverageChecked :
    coverageCheck (innerAD leaf335Box) leaf335InnerLog = true := by
  rfl'

private theorem leaf335InnerLogValid :
    leaf335InnerLog.Valid 8 (innerAD leaf335Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf335CoverageChecked

private noncomputable def leaf335InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf335InputLogOnePlusV_eq :
    leaf335InputLogOnePlusV = outerEnclosure 24
      (leaf335Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf335RoundedFacts : LeafRoundedFacts 8
    leaf335Certificate.logOnePlusV leaf335InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf335InputLogOnePlusV_eq }

private noncomputable def leaf335Inputs : Inputs :=
  inputsOfCaches globalInput sk29RoundedInputs
    chi48InputQChi innerPair35Input
    leaf335InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf335LowerChecked :
    lowerCheck 24 leaf335Box leaf335Inputs = true := by
  rfl'

private theorem leaf335CoversExact : CoversExact 8
    leaf335Box leaf335Certificate leaf335InnerLog leaf335Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk29RoundedFacts chi48RoundedFacts
    innerPair35RoundedFacts leaf335RoundedFacts (by rfl)

private theorem leaf335FlatSound : Sound leaf335Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf335CertificateValid
    leaf335InnerLogValid leaf335CoversExact leaf335LowerChecked

private noncomputable def leaf336Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/32), kHi := (3/2), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf336Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (4042264335/4042194944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (97876021/67108864) }, upper := { exponent := 0, mantissa := (97/64) } }, logOuter := sk30LogOuterCertificate, logK := sk30LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8084459279/8084389888) } }, logDArg := sk30LogDArgCertificate }

private noncomputable def leaf336InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf336LocalValidity :
    LeafFacts leaf336Box leaf336Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf336Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4042264335/4042194944) }) = true
      norm_num [leaf336Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf336CertificateValid :
    WideCertificateValid leaf336Box leaf336Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk30ValidityFacts chi48ValidityFacts
    leaf336LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf336CoverageChecked :
    coverageCheck (innerAD leaf336Box) leaf336InnerLog = true := by
  rfl'

private theorem leaf336InnerLogValid :
    leaf336InnerLog.Valid 8 (innerAD leaf336Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf336CoverageChecked

private noncomputable def leaf336InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf336InputLogOnePlusV_eq :
    leaf336InputLogOnePlusV = outerEnclosure 24
      (leaf336Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf336RoundedFacts : LeafRoundedFacts 8
    leaf336Certificate.logOnePlusV leaf336InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf336InputLogOnePlusV_eq }

private noncomputable def leaf336Inputs : Inputs :=
  inputsOfCaches globalInput sk30RoundedInputs
    chi48InputQChi innerPair35Input
    leaf336InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf336LowerChecked :
    lowerCheck 24 leaf336Box leaf336Inputs = true := by
  rfl'

private theorem leaf336CoversExact : CoversExact 8
    leaf336Box leaf336Certificate leaf336InnerLog leaf336Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk30RoundedFacts chi48RoundedFacts
    innerPair35RoundedFacts leaf336RoundedFacts (by rfl)

private theorem leaf336FlatSound : Sound leaf336Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf336CertificateValid
    leaf336InnerLogValid leaf336CoversExact leaf336LowerChecked

private noncomputable def leaf337Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (47/32), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf337Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108981/67108864) }, vSqrt := { lower := (65533/65536), upper := (68718493695/68717166592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (100235173/67108864) }, upper := { exponent := 0, mantissa := (397/256) } }, logOuter := sk29LogOuterCertificate, logK := sk29LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (137435660287/137434333184) } }, logDArg := sk29LogDArgCertificate }

private noncomputable def leaf337InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf337LocalValidity :
    LeafFacts leaf337Box leaf337Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf337Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (68718493695/68717166592) }) = true
      norm_num [leaf337Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf337CertificateValid :
    WideCertificateValid leaf337Box leaf337Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk29ValidityFacts chi49ValidityFacts
    leaf337LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf337CoverageChecked :
    coverageCheck (innerAD leaf337Box) leaf337InnerLog = true := by
  rfl'

private theorem leaf337InnerLogValid :
    leaf337InnerLog.Valid 8 (innerAD leaf337Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf337CoverageChecked

private noncomputable def leaf337InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf337InputLogOnePlusV_eq :
    leaf337InputLogOnePlusV = outerEnclosure 24
      (leaf337Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf337RoundedFacts : LeafRoundedFacts 8
    leaf337Certificate.logOnePlusV leaf337InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf337InputLogOnePlusV_eq }

private noncomputable def leaf337Inputs : Inputs :=
  inputsOfCaches globalInput sk29RoundedInputs
    chi49InputQChi innerPair35Input
    leaf337InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf337LowerChecked :
    lowerCheck 24 leaf337Box leaf337Inputs = true := by
  rfl'

private theorem leaf337CoversExact : CoversExact 8
    leaf337Box leaf337Certificate leaf337InnerLog leaf337Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk29RoundedFacts chi49RoundedFacts
    innerPair35RoundedFacts leaf337RoundedFacts (by rfl)

private theorem leaf337FlatSound : Sound leaf337Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf337CertificateValid
    leaf337InnerLogValid leaf337CoversExact leaf337LowerChecked

private noncomputable def leaf338Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/32), kHi := (3/2), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf338Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (13743698739/13743423488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (100956023/67108864) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk30LogOuterCertificate, logK := sk30LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (27487122227/27486846976) } }, logDArg := sk30LogDArgCertificate }

private noncomputable def leaf338InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf338LocalValidity :
    LeafFacts leaf338Box leaf338Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf338Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (13743698739/13743423488) }) = true
      norm_num [leaf338Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf338CertificateValid :
    WideCertificateValid leaf338Box leaf338Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk30ValidityFacts chi49ValidityFacts
    leaf338LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf338CoverageChecked :
    coverageCheck (innerAD leaf338Box) leaf338InnerLog = true := by
  rfl'

private theorem leaf338InnerLogValid :
    leaf338InnerLog.Valid 8 (innerAD leaf338Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf338CoverageChecked

private noncomputable def leaf338InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf338InputLogOnePlusV_eq :
    leaf338InputLogOnePlusV = outerEnclosure 24
      (leaf338Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf338RoundedFacts : LeafRoundedFacts 8
    leaf338Certificate.logOnePlusV leaf338InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf338InputLogOnePlusV_eq }

private noncomputable def leaf338Inputs : Inputs :=
  inputsOfCaches globalInput sk30RoundedInputs
    chi49InputQChi innerPair40Input
    leaf338InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf338LowerChecked :
    lowerCheck 24 leaf338Box leaf338Inputs = true := by
  rfl'

private theorem leaf338CoversExact : CoversExact 8
    leaf338Box leaf338Certificate leaf338InnerLog leaf338Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk30RoundedFacts chi49RoundedFacts
    innerPair40RoundedFacts leaf338RoundedFacts (by rfl)

private theorem leaf338FlatSound : Sound leaf338Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf338CertificateValid
    leaf338InnerLogValid leaf338CoversExact leaf338LowerChecked

private noncomputable def leaf339Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (3/8), chiHi := (13/32) }

private noncomputable def leaf339Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554499/33554432) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871724032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (49249279/33554432) }, upper := { exponent := 0, mantissa := (785/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi50LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743579955/13743448064) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf339InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf339LocalValidity :
    LeafFacts leaf339Box leaf339Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf339Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871724032) }) = true
      norm_num [leaf339Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf339CertificateValid :
    WideCertificateValid leaf339Box leaf339Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi50ValidityFacts
    leaf339LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf339CoverageChecked :
    coverageCheck (innerAD leaf339Box) leaf339InnerLog = true := by
  rfl'

private theorem leaf339InnerLogValid :
    leaf339InnerLog.Valid 8 (innerAD leaf339Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf339CoverageChecked

private noncomputable def leaf339InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf339InputLogOnePlusV_eq :
    leaf339InputLogOnePlusV = outerEnclosure 24
      (leaf339Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf339RoundedFacts : LeafRoundedFacts 8
    leaf339Certificate.logOnePlusV leaf339InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf339InputLogOnePlusV_eq }

private noncomputable def leaf339Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi50InputQChi innerPair35Input
    leaf339InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf339LowerChecked :
    lowerCheck 24 leaf339Box leaf339Inputs = true := by
  rfl'

private theorem leaf339CoversExact : CoversExact 8
    leaf339Box leaf339Certificate leaf339InnerLog leaf339Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi50RoundedFacts
    innerPair35RoundedFacts leaf339RoundedFacts (by rfl)

private theorem leaf339FlatSound : Sound leaf339Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf339CertificateValid
    leaf339InnerLogValid leaf339CoversExact leaf339LowerChecked

private noncomputable def leaf340Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf340Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554501/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358534144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (50559917/33554432) }, upper := { exponent := 0, mantissa := (403/256) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717813759/68717068288) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf340InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf340LocalValidity :
    LeafFacts leaf340Box leaf340Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf340Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358534144) }) = true
      norm_num [leaf340Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf340CertificateValid :
    WideCertificateValid leaf340Box leaf340Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi51ValidityFacts
    leaf340LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf340CoverageChecked :
    coverageCheck (innerAD leaf340Box) leaf340InnerLog = true := by
  rfl'

private theorem leaf340InnerLogValid :
    leaf340InnerLog.Valid 8 (innerAD leaf340Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf340CoverageChecked

private noncomputable def leaf340InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf340InputLogOnePlusV_eq :
    leaf340InputLogOnePlusV = outerEnclosure 24
      (leaf340Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf340RoundedFacts : LeafRoundedFacts 8
    leaf340Certificate.logOnePlusV leaf340InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf340InputLogOnePlusV_eq }

private noncomputable def leaf340Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi51InputQChi innerPair41Input
    leaf340InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf340LowerChecked :
    lowerCheck 24 leaf340Box leaf340Inputs = true := by
  rfl'

private theorem leaf340CoversExact : CoversExact 8
    leaf340Box leaf340Certificate leaf340InnerLog leaf340Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi51RoundedFacts
    innerPair41RoundedFacts leaf340RoundedFacts (by rfl)

private theorem leaf340FlatSound : Sound leaf340Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf340CertificateValid
    leaf340InnerLogValid leaf340CoversExact leaf340LowerChecked

private noncomputable def leaf341Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (3/8), chiHi := (13/32) }

private noncomputable def leaf341Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554501/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358566912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (50035661/33554432) }, upper := { exponent := 0, mantissa := (399/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi50LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717846527/68717133824) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf341InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf341LocalValidity :
    LeafFacts leaf341Box leaf341Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf341Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358566912) }) = true
      norm_num [leaf341Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf341CertificateValid :
    WideCertificateValid leaf341Box leaf341Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi50ValidityFacts
    leaf341LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf341CoverageChecked :
    coverageCheck (innerAD leaf341Box) leaf341InnerLog = true := by
  rfl'

private theorem leaf341InnerLogValid :
    leaf341InnerLog.Valid 8 (innerAD leaf341Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf341CoverageChecked

private noncomputable def leaf341InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf341InputLogOnePlusV_eq :
    leaf341InputLogOnePlusV = outerEnclosure 24
      (leaf341Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf341RoundedFacts : LeafRoundedFacts 8
    leaf341Certificate.logOnePlusV leaf341InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf341InputLogOnePlusV_eq }

private noncomputable def leaf341Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi50InputQChi innerPair35Input
    leaf341InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf341LowerChecked :
    lowerCheck 24 leaf341Box leaf341Inputs = true := by
  rfl'

private theorem leaf341CoversExact : CoversExact 8
    leaf341Box leaf341Certificate leaf341InnerLog leaf341Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi50RoundedFacts
    innerPair35RoundedFacts leaf341RoundedFacts (by rfl)

private theorem leaf341FlatSound : Sound leaf341Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf341CertificateValid
    leaf341InnerLogValid leaf341CoversExact leaf341LowerChecked

private noncomputable def leaf342Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf342Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554503/33554432) }, vSqrt := { lower := (65533/65536), upper := (2290618641/2290565120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (51411831/33554432) }, upper := { exponent := 0, mantissa := (205/128) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4581183761/4581130240) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf342InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf342LocalValidity :
    LeafFacts leaf342Box leaf342Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf342Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2290618641/2290565120) }) = true
      norm_num [leaf342Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf342CertificateValid :
    WideCertificateValid leaf342Box leaf342Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi51ValidityFacts
    leaf342LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf342CoverageChecked :
    coverageCheck (innerAD leaf342Box) leaf342InnerLog = true := by
  rfl'

private theorem leaf342InnerLogValid :
    leaf342InnerLog.Valid 8 (innerAD leaf342Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf342CoverageChecked

private noncomputable def leaf342InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf342InputLogOnePlusV_eq :
    leaf342InputLogOnePlusV = outerEnclosure 24
      (leaf342Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf342RoundedFacts : LeafRoundedFacts 8
    leaf342Certificate.logOnePlusV leaf342InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf342InputLogOnePlusV_eq }

private noncomputable def leaf342Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi51InputQChi innerPair41Input
    leaf342InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf342LowerChecked :
    lowerCheck 24 leaf342Box leaf342Inputs = true := by
  rfl'

private theorem leaf342CoversExact : CoversExact 8
    leaf342Box leaf342Certificate leaf342InnerLog leaf342Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi51RoundedFacts
    innerPair41RoundedFacts leaf342RoundedFacts (by rfl)

private theorem leaf342FlatSound : Sound leaf342Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf342CertificateValid
    leaf342InnerLogValid leaf342CoversExact leaf342LowerChecked

private noncomputable def leaf343Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf343Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554503/33554432) }, vSqrt := { lower := (65533/65536), upper := (2021134095/2021085184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (51870555/33554432) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4042219279/4042170368) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf343InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf343LocalValidity :
    LeafFacts leaf343Box leaf343Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf343Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2021134095/2021085184) }) = true
      norm_num [leaf343Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf343CertificateValid :
    WideCertificateValid leaf343Box leaf343Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi52ValidityFacts
    leaf343LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf343CoverageChecked :
    coverageCheck (innerAD leaf343Box) leaf343InnerLog = true := by
  rfl'

private theorem leaf343InnerLogValid :
    leaf343InnerLog.Valid 8 (innerAD leaf343Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf343CoverageChecked

private noncomputable def leaf343InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf343InputLogOnePlusV_eq :
    leaf343InputLogOnePlusV = outerEnclosure 24
      (leaf343Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf343RoundedFacts : LeafRoundedFacts 8
    leaf343Certificate.logOnePlusV leaf343InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf343InputLogOnePlusV_eq }

private noncomputable def leaf343Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi52InputQChi innerPair41Input
    leaf343InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf343LowerChecked :
    lowerCheck 24 leaf343Box leaf343Inputs = true := by
  rfl'

private theorem leaf343CoversExact : CoversExact 8
    leaf343Box leaf343Certificate leaf343InnerLog leaf343Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi52RoundedFacts
    innerPair41RoundedFacts leaf343RoundedFacts (by rfl)

private theorem leaf343FlatSound : Sound leaf343Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf343CertificateValid
    leaf343InnerLogValid leaf343CoversExact leaf343LowerChecked

private noncomputable def leaf344Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf344Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554505/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358362112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (53181193/33554432) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717641727/68716724224) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf344InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf344LocalValidity :
    LeafFacts leaf344Box leaf344Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf344Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358362112) }) = true
      norm_num [leaf344Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf344CertificateValid :
    WideCertificateValid leaf344Box leaf344Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi53ValidityFacts
    leaf344LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf344CoverageChecked :
    coverageCheck (innerAD leaf344Box) leaf344InnerLog = true := by
  rfl'

private theorem leaf344InnerLogValid :
    leaf344InnerLog.Valid 8 (innerAD leaf344Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf344CoverageChecked

private noncomputable def leaf344InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf344InputLogOnePlusV_eq :
    leaf344InputLogOnePlusV = outerEnclosure 24
      (leaf344Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf344RoundedFacts : LeafRoundedFacts 8
    leaf344Certificate.logOnePlusV leaf344InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf344InputLogOnePlusV_eq }

private noncomputable def leaf344Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi53InputQChi innerPair51Input
    leaf344InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf344LowerChecked :
    lowerCheck 24 leaf344Box leaf344Inputs = true := by
  rfl'

private theorem leaf344CoversExact : CoversExact 8
    leaf344Box leaf344Certificate leaf344InnerLog leaf344Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi53RoundedFacts
    innerPair51RoundedFacts leaf344RoundedFacts (by rfl)

private theorem leaf344FlatSound : Sound leaf344Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf344CertificateValid
    leaf344InnerLogValid leaf344CoversExact leaf344LowerChecked

private noncomputable def leaf345Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf345Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554505/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358386688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (52788001/33554432) }, upper := { exponent := 0, mantissa := (421/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717666303/68716773376) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf345InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf345LocalValidity :
    LeafFacts leaf345Box leaf345Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf345Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358386688) }) = true
      norm_num [leaf345Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf345CertificateValid :
    WideCertificateValid leaf345Box leaf345Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi52ValidityFacts
    leaf345LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf345CoverageChecked :
    coverageCheck (innerAD leaf345Box) leaf345InnerLog = true := by
  rfl'

private theorem leaf345InnerLogValid :
    leaf345InnerLog.Valid 8 (innerAD leaf345Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf345CoverageChecked

private noncomputable def leaf345InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf345InputLogOnePlusV_eq :
    leaf345InputLogOnePlusV = outerEnclosure 24
      (leaf345Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf345RoundedFacts : LeafRoundedFacts 8
    leaf345Certificate.logOnePlusV leaf345InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf345InputLogOnePlusV_eq }

private noncomputable def leaf345Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi52InputQChi innerPair51Input
    leaf345InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf345LowerChecked :
    lowerCheck 24 leaf345Box leaf345Inputs = true := by
  rfl'

private theorem leaf345CoversExact : CoversExact 8
    leaf345Box leaf345Certificate leaf345InnerLog leaf345Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi52RoundedFacts
    innerPair51RoundedFacts leaf345RoundedFacts (by rfl)

private theorem leaf345FlatSound : Sound leaf345Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf345CertificateValid
    leaf345InnerLogValid leaf345CoversExact leaf345LowerChecked

private noncomputable def leaf346Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf346Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554507/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358296576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (54164171/33554432) }, upper := { exponent := 0, mantissa := (27/16) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717576191/68716593152) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf346InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf346LocalValidity :
    LeafFacts leaf346Box leaf346Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf346Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358296576) }) = true
      norm_num [leaf346Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf346CertificateValid :
    WideCertificateValid leaf346Box leaf346Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi53ValidityFacts
    leaf346LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf346CoverageChecked :
    coverageCheck (innerAD leaf346Box) leaf346InnerLog = true := by
  rfl'

private theorem leaf346InnerLogValid :
    leaf346InnerLog.Valid 8 (innerAD leaf346Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf346CoverageChecked

private noncomputable def leaf346InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf346InputLogOnePlusV_eq :
    leaf346InputLogOnePlusV = outerEnclosure 24
      (leaf346Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf346RoundedFacts : LeafRoundedFacts 8
    leaf346Certificate.logOnePlusV leaf346InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf346InputLogOnePlusV_eq }

private noncomputable def leaf346Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi53InputQChi innerPair51Input
    leaf346InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf346LowerChecked :
    lowerCheck 24 leaf346Box leaf346Inputs = true := by
  rfl'

private theorem leaf346CoversExact : CoversExact 8
    leaf346Box leaf346Certificate leaf346InnerLog leaf346Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi53RoundedFacts
    innerPair51RoundedFacts leaf346RoundedFacts (by rfl)

private theorem leaf346FlatSound : Sound leaf346Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf346CertificateValid
    leaf346InnerLogValid leaf346CoversExact leaf346LowerChecked

private noncomputable def leaf347Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (3/8), chiHi := (13/32) }

private noncomputable def leaf347Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554503/33554432) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452837888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (50822043/33554432) }, upper := { exponent := 0, mantissa := (811/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi50LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905931093/22905675776) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf347InnerLog : WideLogData :=
  innerPair46Data

set_option maxRecDepth 1000000 in
private theorem leaf347LocalValidity :
    LeafFacts leaf347Box leaf347Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf347Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452837888) }) = true
      norm_num [leaf347Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf347CertificateValid :
    WideCertificateValid leaf347Box leaf347Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi50ValidityFacts
    leaf347LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf347CoverageChecked :
    coverageCheck (innerAD leaf347Box) leaf347InnerLog = true := by
  rfl'

private theorem leaf347InnerLogValid :
    leaf347InnerLog.Valid 8 (innerAD leaf347Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint44PositiveFacts.valid leaf347CoverageChecked

private noncomputable def leaf347InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf347InputLogOnePlusV_eq :
    leaf347InputLogOnePlusV = outerEnclosure 24
      (leaf347Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf347RoundedFacts : LeafRoundedFacts 8
    leaf347Certificate.logOnePlusV leaf347InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf347InputLogOnePlusV_eq }

private noncomputable def leaf347Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi50InputQChi innerPair46Input
    leaf347InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf347LowerChecked :
    lowerCheck 24 leaf347Box leaf347Inputs = true := by
  rfl'

private theorem leaf347CoversExact : CoversExact 8
    leaf347Box leaf347Certificate leaf347InnerLog leaf347Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi50RoundedFacts
    innerPair46RoundedFacts leaf347RoundedFacts (by rfl)

private theorem leaf347FlatSound : Sound leaf347Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf347CertificateValid
    leaf347InnerLogValid leaf347CoversExact leaf347LowerChecked

private noncomputable def leaf348Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf348Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554505/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358419456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (52263745/33554432) }, upper := { exponent := 0, mantissa := (417/256) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717699071/68716838912) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf348InnerLog : WideLogData :=
  innerPair155Data

set_option maxRecDepth 1000000 in
private theorem leaf348LocalValidity :
    LeafFacts leaf348Box leaf348Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf348Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358419456) }) = true
      norm_num [leaf348Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf348CertificateValid :
    WideCertificateValid leaf348Box leaf348Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi51ValidityFacts
    leaf348LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf348CoverageChecked :
    coverageCheck (innerAD leaf348Box) leaf348InnerLog = true := by
  rfl'

private theorem leaf348InnerLogValid :
    leaf348InnerLog.Valid 8 (innerAD leaf348Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint45PositiveFacts.valid leaf348CoverageChecked

private noncomputable def leaf348InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf348InputLogOnePlusV_eq :
    leaf348InputLogOnePlusV = outerEnclosure 24
      (leaf348Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf348RoundedFacts : LeafRoundedFacts 8
    leaf348Certificate.logOnePlusV leaf348InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf348InputLogOnePlusV_eq }

private noncomputable def leaf348Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi51InputQChi innerPair155Input
    leaf348InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf348LowerChecked :
    lowerCheck 24 leaf348Box leaf348Inputs = true := by
  rfl'

private theorem leaf348CoversExact : CoversExact 8
    leaf348Box leaf348Certificate leaf348InnerLog leaf348Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi51RoundedFacts
    innerPair155RoundedFacts leaf348RoundedFacts (by rfl)

private theorem leaf348FlatSound : Sound leaf348Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf348CertificateValid
    leaf348InnerLogValid leaf348CoversExact leaf348LowerChecked

private noncomputable def leaf349Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (3/8), chiHi := (13/32) }

private noncomputable def leaf349Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554505/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358460416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (51608425/33554432) }, upper := { exponent := 0, mantissa := (103/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi50LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717740031/68716920832) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf349InnerLog : WideLogData :=
  innerPair86Data

set_option maxRecDepth 1000000 in
private theorem leaf349LocalValidity :
    LeafFacts leaf349Box leaf349Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf349Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358460416) }) = true
      norm_num [leaf349Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf349CertificateValid :
    WideCertificateValid leaf349Box leaf349Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi50ValidityFacts
    leaf349LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf349CoverageChecked :
    coverageCheck (innerAD leaf349Box) leaf349InnerLog = true := by
  rfl'

private theorem leaf349InnerLogValid :
    leaf349InnerLog.Valid 8 (innerAD leaf349Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint46PositiveFacts.valid leaf349CoverageChecked

private noncomputable def leaf349InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf349InputLogOnePlusV_eq :
    leaf349InputLogOnePlusV = outerEnclosure 24
      (leaf349Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf349RoundedFacts : LeafRoundedFacts 8
    leaf349Certificate.logOnePlusV leaf349InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf349InputLogOnePlusV_eq }

private noncomputable def leaf349Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi50InputQChi innerPair86Input
    leaf349InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf349LowerChecked :
    lowerCheck 24 leaf349Box leaf349Inputs = true := by
  rfl'

private theorem leaf349CoversExact : CoversExact 8
    leaf349Box leaf349Certificate leaf349InnerLog leaf349Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi50RoundedFacts
    innerPair86RoundedFacts leaf349RoundedFacts (by rfl)

private theorem leaf349FlatSound : Sound leaf349Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf349CertificateValid
    leaf349InnerLogValid leaf349CoversExact leaf349LowerChecked

private noncomputable def leaf350Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf350Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554507/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358362112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (53115659/33554432) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717641727/68716724224) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf350InnerLog : WideLogData :=
  innerPair172Data

set_option maxRecDepth 1000000 in
private theorem leaf350LocalValidity :
    LeafFacts leaf350Box leaf350Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf350Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358362112) }) = true
      norm_num [leaf350Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf350CertificateValid :
    WideCertificateValid leaf350Box leaf350Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi51ValidityFacts
    leaf350LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf350CoverageChecked :
    coverageCheck (innerAD leaf350Box) leaf350InnerLog = true := by
  rfl'

private theorem leaf350InnerLogValid :
    leaf350InnerLog.Valid 8 (innerAD leaf350Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint48PositiveFacts.valid leaf350CoverageChecked

private noncomputable def leaf350InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf350InputLogOnePlusV_eq :
    leaf350InputLogOnePlusV = outerEnclosure 24
      (leaf350Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf350RoundedFacts : LeafRoundedFacts 8
    leaf350Certificate.logOnePlusV leaf350InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf350InputLogOnePlusV_eq }

private noncomputable def leaf350Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi51InputQChi innerPair172Input
    leaf350InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf350LowerChecked :
    lowerCheck 24 leaf350Box leaf350Inputs = true := by
  rfl'

private theorem leaf350CoversExact : CoversExact 8
    leaf350Box leaf350Certificate leaf350InnerLog leaf350Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi51RoundedFacts
    innerPair172RoundedFacts leaf350RoundedFacts (by rfl)

private theorem leaf350FlatSound : Sound leaf350Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf350CertificateValid
    leaf350InnerLogValid leaf350CoversExact leaf350LowerChecked

private noncomputable def leaf351Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf351Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554507/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358325248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (53705447/33554432) }, upper := { exponent := 0, mantissa := (857/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717604863/68716650496) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf351InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf351LocalValidity :
    LeafFacts leaf351Box leaf351Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf351Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358325248) }) = true
      norm_num [leaf351Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf351CertificateValid :
    WideCertificateValid leaf351Box leaf351Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi52ValidityFacts
    leaf351LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf351CoverageChecked :
    coverageCheck (innerAD leaf351Box) leaf351InnerLog = true := by
  rfl'

private theorem leaf351InnerLogValid :
    leaf351InnerLog.Valid 8 (innerAD leaf351Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf351CoverageChecked

private noncomputable def leaf351InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf351InputLogOnePlusV_eq :
    leaf351InputLogOnePlusV = outerEnclosure 24
      (leaf351Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf351RoundedFacts : LeafRoundedFacts 8
    leaf351Certificate.logOnePlusV leaf351InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf351InputLogOnePlusV_eq }

private noncomputable def leaf351Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi52InputQChi innerPair51Input
    leaf351InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf351LowerChecked :
    lowerCheck 24 leaf351Box leaf351Inputs = true := by
  rfl'

private theorem leaf351CoversExact : CoversExact 8
    leaf351Box leaf351Certificate leaf351InnerLog leaf351Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi52RoundedFacts
    innerPair51RoundedFacts leaf351RoundedFacts (by rfl)

private theorem leaf351FlatSound : Sound leaf351Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf351CertificateValid
    leaf351InnerLogValid leaf351CoversExact leaf351LowerChecked

private noncomputable def leaf352Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf352Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554509/33554432) }, vSqrt := { lower := (65533/65536), upper := (2290618641/2290548736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (55147149/33554432) }, upper := { exponent := 0, mantissa := (55/32) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4581167377/4581097472) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf352InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf352LocalValidity :
    LeafFacts leaf352Box leaf352Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf352Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2290618641/2290548736) }) = true
      norm_num [leaf352Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf352CertificateValid :
    WideCertificateValid leaf352Box leaf352Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi53ValidityFacts
    leaf352LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf352CoverageChecked :
    coverageCheck (innerAD leaf352Box) leaf352InnerLog = true := by
  rfl'

private theorem leaf352InnerLogValid :
    leaf352InnerLog.Valid 8 (innerAD leaf352Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf352CoverageChecked

private noncomputable def leaf352InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf352InputLogOnePlusV_eq :
    leaf352InputLogOnePlusV = outerEnclosure 24
      (leaf352Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf352RoundedFacts : LeafRoundedFacts 8
    leaf352Certificate.logOnePlusV leaf352InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf352InputLogOnePlusV_eq }

private noncomputable def leaf352Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi53InputQChi innerPair57Input
    leaf352InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf352LowerChecked :
    lowerCheck 24 leaf352Box leaf352Inputs = true := by
  rfl'

private theorem leaf352CoversExact : CoversExact 8
    leaf352Box leaf352Certificate leaf352InnerLog leaf352Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi53RoundedFacts
    innerPair57RoundedFacts leaf352RoundedFacts (by rfl)

private theorem leaf352FlatSound : Sound leaf352Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf352CertificateValid
    leaf352InnerLogValid leaf352CoversExact leaf352LowerChecked

private noncomputable def leaf353Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf353Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554509/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358263808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (54622893/33554432) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717543423/68716527616) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf353InnerLog : WideLogData :=
  innerPair58Data

set_option maxRecDepth 1000000 in
private theorem leaf353LocalValidity :
    LeafFacts leaf353Box leaf353Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf353Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358263808) }) = true
      norm_num [leaf353Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf353CertificateValid :
    WideCertificateValid leaf353Box leaf353Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi52ValidityFacts
    leaf353LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf353CoverageChecked :
    coverageCheck (innerAD leaf353Box) leaf353InnerLog = true := by
  rfl'

private theorem leaf353InnerLogValid :
    leaf353InnerLog.Valid 8 (innerAD leaf353Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint20PositiveFacts.valid leaf353CoverageChecked

private noncomputable def leaf353InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf353InputLogOnePlusV_eq :
    leaf353InputLogOnePlusV = outerEnclosure 24
      (leaf353Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf353RoundedFacts : LeafRoundedFacts 8
    leaf353Certificate.logOnePlusV leaf353InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf353InputLogOnePlusV_eq }

private noncomputable def leaf353Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi52InputQChi innerPair58Input
    leaf353InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf353LowerChecked :
    lowerCheck 24 leaf353Box leaf353Inputs = true := by
  rfl'

private theorem leaf353CoversExact : CoversExact 8
    leaf353Box leaf353Certificate leaf353InnerLog leaf353Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi52RoundedFacts
    innerPair58RoundedFacts leaf353RoundedFacts (by rfl)

private theorem leaf353FlatSound : Sound leaf353Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf353CertificateValid
    leaf353InnerLogValid leaf353CoversExact leaf353LowerChecked

private noncomputable def leaf354Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf354Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554511/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34358165504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (56130127/33554432) }, upper := { exponent := 0, mantissa := (7/4) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717445119/68716331008) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf354InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf354LocalValidity :
    LeafFacts leaf354Box leaf354Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf354Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34358165504) }) = true
      norm_num [leaf354Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf354CertificateValid :
    WideCertificateValid leaf354Box leaf354Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi53ValidityFacts
    leaf354LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf354CoverageChecked :
    coverageCheck (innerAD leaf354Box) leaf354InnerLog = true := by
  rfl'

private theorem leaf354InnerLogValid :
    leaf354InnerLog.Valid 8 (innerAD leaf354Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf354CoverageChecked

private noncomputable def leaf354InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf354InputLogOnePlusV_eq :
    leaf354InputLogOnePlusV = outerEnclosure 24
      (leaf354Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf354RoundedFacts : LeafRoundedFacts 8
    leaf354Certificate.logOnePlusV leaf354InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf354InputLogOnePlusV_eq }

private noncomputable def leaf354Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi53InputQChi innerPair57Input
    leaf354InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf354LowerChecked :
    lowerCheck 24 leaf354Box leaf354Inputs = true := by
  rfl'

private theorem leaf354CoversExact : CoversExact 8
    leaf354Box leaf354Certificate leaf354InnerLog leaf354Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi53RoundedFacts
    innerPair57RoundedFacts leaf354RoundedFacts (by rfl)

private theorem leaf354FlatSound : Sound leaf354Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf354CertificateValid
    leaf354InnerLogValid leaf354CoversExact leaf354LowerChecked

private noncomputable def component8Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node0_sound : Sound component8Node0Box :=
  sound_of_literal_split component8Node0Box leaf317Box leaf318Box
    .chi (9/32) (by rfl) (by rfl)
    leaf317FlatSound leaf318FlatSound

private noncomputable def component8Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node1_sound : Sound component8Node1Box :=
  sound_of_literal_split component8Node1Box leaf319Box leaf320Box
    .chi (9/32) (by rfl) (by rfl)
    leaf319FlatSound leaf320FlatSound

private noncomputable def component8Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node2_sound : Sound component8Node2Box :=
  sound_of_literal_split component8Node2Box component8Node0Box component8Node1Box
    .k (21/16) (by rfl) (by rfl)
    component8Node0_sound component8Node1_sound

private noncomputable def component8Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node3_sound : Sound component8Node3Box :=
  sound_of_literal_split component8Node3Box leaf321Box leaf322Box
    .chi (11/32) (by rfl) (by rfl)
    leaf321FlatSound leaf322FlatSound

private noncomputable def component8Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node4_sound : Sound component8Node4Box :=
  sound_of_literal_split component8Node4Box leaf323Box leaf324Box
    .chi (11/32) (by rfl) (by rfl)
    leaf323FlatSound leaf324FlatSound

private noncomputable def component8Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node5_sound : Sound component8Node5Box :=
  sound_of_literal_split component8Node5Box component8Node3Box component8Node4Box
    .k (21/16) (by rfl) (by rfl)
    component8Node3_sound component8Node4_sound

private noncomputable def component8Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node6_sound : Sound component8Node6Box :=
  sound_of_literal_split component8Node6Box component8Node2Box component8Node5Box
    .chi (5/16) (by rfl) (by rfl)
    component8Node2_sound component8Node5_sound

private noncomputable def component8Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component8Node7_sound : Sound component8Node7Box :=
  sound_of_literal_split component8Node7Box leaf325Box leaf326Box
    .k (45/32) (by rfl) (by rfl)
    leaf325FlatSound leaf326FlatSound

private noncomputable def component8Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node8_sound : Sound component8Node8Box :=
  sound_of_literal_split component8Node8Box leaf327Box leaf328Box
    .k (45/32) (by rfl) (by rfl)
    leaf327FlatSound leaf328FlatSound

private noncomputable def component8Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node9_sound : Sound component8Node9Box :=
  sound_of_literal_split component8Node9Box component8Node7Box component8Node8Box
    .chi (9/32) (by rfl) (by rfl)
    component8Node7_sound component8Node8_sound

private noncomputable def component8Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component8Node10_sound : Sound component8Node10Box :=
  sound_of_literal_split component8Node10Box leaf329Box leaf330Box
    .k (47/32) (by rfl) (by rfl)
    leaf329FlatSound leaf330FlatSound

private noncomputable def component8Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node11_sound : Sound component8Node11Box :=
  sound_of_literal_split component8Node11Box leaf331Box leaf332Box
    .k (47/32) (by rfl) (by rfl)
    leaf331FlatSound leaf332FlatSound

private noncomputable def component8Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node12_sound : Sound component8Node12Box :=
  sound_of_literal_split component8Node12Box component8Node10Box component8Node11Box
    .chi (9/32) (by rfl) (by rfl)
    component8Node10_sound component8Node11_sound

private noncomputable def component8Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node13_sound : Sound component8Node13Box :=
  sound_of_literal_split component8Node13Box component8Node9Box component8Node12Box
    .k (23/16) (by rfl) (by rfl)
    component8Node9_sound component8Node12_sound

private noncomputable def component8Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node14_sound : Sound component8Node14Box :=
  sound_of_literal_split component8Node14Box leaf333Box leaf334Box
    .chi (11/32) (by rfl) (by rfl)
    leaf333FlatSound leaf334FlatSound

private noncomputable def component8Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component8Node15_sound : Sound component8Node15Box :=
  sound_of_literal_split component8Node15Box leaf335Box leaf336Box
    .k (47/32) (by rfl) (by rfl)
    leaf335FlatSound leaf336FlatSound

private noncomputable def component8Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node16_sound : Sound component8Node16Box :=
  sound_of_literal_split component8Node16Box leaf337Box leaf338Box
    .k (47/32) (by rfl) (by rfl)
    leaf337FlatSound leaf338FlatSound

private noncomputable def component8Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node17_sound : Sound component8Node17Box :=
  sound_of_literal_split component8Node17Box component8Node15Box component8Node16Box
    .chi (11/32) (by rfl) (by rfl)
    component8Node15_sound component8Node16_sound

private noncomputable def component8Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node18_sound : Sound component8Node18Box :=
  sound_of_literal_split component8Node18Box component8Node14Box component8Node17Box
    .k (23/16) (by rfl) (by rfl)
    component8Node14_sound component8Node17_sound

private noncomputable def component8Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node19_sound : Sound component8Node19Box :=
  sound_of_literal_split component8Node19Box component8Node13Box component8Node18Box
    .chi (5/16) (by rfl) (by rfl)
    component8Node13_sound component8Node18_sound

private noncomputable def component8Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component8Node20_sound : Sound component8Node20Box :=
  sound_of_literal_split component8Node20Box component8Node6Box component8Node19Box
    .k (11/8) (by rfl) (by rfl)
    component8Node6_sound component8Node19_sound

private noncomputable def component8Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node21_sound : Sound component8Node21Box :=
  sound_of_literal_split component8Node21Box leaf339Box leaf340Box
    .chi (13/32) (by rfl) (by rfl)
    leaf339FlatSound leaf340FlatSound

private noncomputable def component8Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node22_sound : Sound component8Node22Box :=
  sound_of_literal_split component8Node22Box leaf341Box leaf342Box
    .chi (13/32) (by rfl) (by rfl)
    leaf341FlatSound leaf342FlatSound

private noncomputable def component8Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node23_sound : Sound component8Node23Box :=
  sound_of_literal_split component8Node23Box component8Node21Box component8Node22Box
    .k (21/16) (by rfl) (by rfl)
    component8Node21_sound component8Node22_sound

private noncomputable def component8Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node24_sound : Sound component8Node24Box :=
  sound_of_literal_split component8Node24Box leaf343Box leaf344Box
    .chi (15/32) (by rfl) (by rfl)
    leaf343FlatSound leaf344FlatSound

private noncomputable def component8Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node25_sound : Sound component8Node25Box :=
  sound_of_literal_split component8Node25Box leaf345Box leaf346Box
    .chi (15/32) (by rfl) (by rfl)
    leaf345FlatSound leaf346FlatSound

private noncomputable def component8Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node26_sound : Sound component8Node26Box :=
  sound_of_literal_split component8Node26Box component8Node24Box component8Node25Box
    .k (21/16) (by rfl) (by rfl)
    component8Node24_sound component8Node25_sound

private noncomputable def component8Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node27_sound : Sound component8Node27Box :=
  sound_of_literal_split component8Node27Box component8Node23Box component8Node26Box
    .chi (7/16) (by rfl) (by rfl)
    component8Node23_sound component8Node26_sound

private noncomputable def component8Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node28_sound : Sound component8Node28Box :=
  sound_of_literal_split component8Node28Box leaf347Box leaf348Box
    .chi (13/32) (by rfl) (by rfl)
    leaf347FlatSound leaf348FlatSound

private noncomputable def component8Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node29_sound : Sound component8Node29Box :=
  sound_of_literal_split component8Node29Box leaf349Box leaf350Box
    .chi (13/32) (by rfl) (by rfl)
    leaf349FlatSound leaf350FlatSound

private noncomputable def component8Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component8Node30_sound : Sound component8Node30Box :=
  sound_of_literal_split component8Node30Box component8Node28Box component8Node29Box
    .k (23/16) (by rfl) (by rfl)
    component8Node28_sound component8Node29_sound

private noncomputable def component8Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node31_sound : Sound component8Node31Box :=
  sound_of_literal_split component8Node31Box leaf351Box leaf352Box
    .chi (15/32) (by rfl) (by rfl)
    leaf351FlatSound leaf352FlatSound

private noncomputable def component8Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node32_sound : Sound component8Node32Box :=
  sound_of_literal_split component8Node32Box leaf353Box leaf354Box
    .chi (15/32) (by rfl) (by rfl)
    leaf353FlatSound leaf354FlatSound

private noncomputable def component8Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node33_sound : Sound component8Node33Box :=
  sound_of_literal_split component8Node33Box component8Node31Box component8Node32Box
    .k (23/16) (by rfl) (by rfl)
    component8Node31_sound component8Node32_sound

private noncomputable def component8Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node34_sound : Sound component8Node34Box :=
  sound_of_literal_split component8Node34Box component8Node30Box component8Node33Box
    .chi (7/16) (by rfl) (by rfl)
    component8Node30_sound component8Node33_sound

private noncomputable def component8Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component8Node35_sound : Sound component8Node35Box :=
  sound_of_literal_split component8Node35Box component8Node27Box component8Node34Box
    .k (11/8) (by rfl) (by rfl)
    component8Node27_sound component8Node34_sound

noncomputable def component8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component8_sound : Sound component8Box :=
  sound_of_literal_split component8Box component8Node20Box component8Node35Box
    .chi (3/8) (by rfl) (by rfl)
    component8Node20_sound component8Node35_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
