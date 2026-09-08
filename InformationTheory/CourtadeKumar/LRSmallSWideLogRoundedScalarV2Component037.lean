import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf1596Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1596Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435587/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108351) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (297760895/268435456) }, upper := { exponent := 0, mantissa := (4609/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217343/134216702) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1596InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1596LocalValidity :
    LeafFacts leaf1596Box leaf1596Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1596Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108351) }) = true
      norm_num [leaf1596Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1596CertificateValid :
    WideCertificateValid leaf1596Box leaf1596Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi139ValidityFacts
    leaf1596LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1596CoverageChecked :
    coverageCheck (innerAD leaf1596Box) leaf1596InnerLog = true := by
  rfl'

private theorem leaf1596InnerLogValid :
    leaf1596InnerLog.Valid 8 (innerAD leaf1596Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1596CoverageChecked

private noncomputable def leaf1596InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1596InputLogOnePlusV_eq :
    leaf1596InputLogOnePlusV = outerEnclosure 24
      (leaf1596Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1596RoundedFacts : LeafRoundedFacts 8
    leaf1596Certificate.logOnePlusV leaf1596InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1596InputLogOnePlusV_eq }

private noncomputable def leaf1596Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1596InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1596LowerChecked :
    lowerCheck 24 leaf1596Box leaf1596Inputs = true := by
  rfl'

private theorem leaf1596CoversExact : CoversExact 8
    leaf1596Box leaf1596Certificate leaf1596InnerLog leaf1596Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1596RoundedFacts (by rfl)

private theorem leaf1596FlatSound : Sound leaf1596Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1596CertificateValid
    leaf1596InnerLogValid leaf1596CoversExact leaf1596LowerChecked

private noncomputable def leaf1597Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1597Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435589/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554171) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (298285149/268435456) }, upper := { exponent := 0, mantissa := (2309/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108667/67108342) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1597InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1597LocalValidity :
    LeafFacts leaf1597Box leaf1597Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1597Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554171) }) = true
      norm_num [leaf1597Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1597CertificateValid :
    WideCertificateValid leaf1597Box leaf1597Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi139ValidityFacts
    leaf1597LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1597CoverageChecked :
    coverageCheck (innerAD leaf1597Box) leaf1597InnerLog = true := by
  rfl'

private theorem leaf1597InnerLogValid :
    leaf1597InnerLog.Valid 8 (innerAD leaf1597Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1597CoverageChecked

private noncomputable def leaf1597InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814581/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1597InputLogOnePlusV_eq :
    leaf1597InputLogOnePlusV = outerEnclosure 24
      (leaf1597Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1597RoundedFacts : LeafRoundedFacts 8
    leaf1597Certificate.logOnePlusV leaf1597InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1597InputLogOnePlusV_eq }

private noncomputable def leaf1597Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1597InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1597LowerChecked :
    lowerCheck 24 leaf1597Box leaf1597Inputs = true := by
  rfl'

private theorem leaf1597CoversExact : CoversExact 8
    leaf1597Box leaf1597Certificate leaf1597InnerLog leaf1597Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1597RoundedFacts (by rfl)

private theorem leaf1597FlatSound : Sound leaf1597Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1597CertificateValid
    leaf1597InnerLogValid leaf1597CoversExact leaf1597LowerChecked

private noncomputable def leaf1598Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1598Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435589/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554147) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (301430685/268435456) }, upper := { exponent := 0, mantissa := (2333/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108643/67108294) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1598InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1598LocalValidity :
    LeafFacts leaf1598Box leaf1598Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1598Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554147) }) = true
      norm_num [leaf1598Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1598CertificateValid :
    WideCertificateValid leaf1598Box leaf1598Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi140ValidityFacts
    leaf1598LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1598CoverageChecked :
    coverageCheck (innerAD leaf1598Box) leaf1598InnerLog = true := by
  rfl'

private theorem leaf1598InnerLogValid :
    leaf1598InnerLog.Valid 8 (innerAD leaf1598Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1598CoverageChecked

private noncomputable def leaf1598InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726823/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1598InputLogOnePlusV_eq :
    leaf1598InputLogOnePlusV = outerEnclosure 24
      (leaf1598Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1598RoundedFacts : LeafRoundedFacts 8
    leaf1598Certificate.logOnePlusV leaf1598InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1598InputLogOnePlusV_eq }

private noncomputable def leaf1598Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi140InputQChi innerPair6Input
    leaf1598InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1598LowerChecked :
    lowerCheck 24 leaf1598Box leaf1598Inputs = true := by
  rfl'

private theorem leaf1598CoversExact : CoversExact 8
    leaf1598Box leaf1598Certificate leaf1598InnerLog leaf1598Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi140RoundedFacts
    innerPair6RoundedFacts leaf1598RoundedFacts (by rfl)

private theorem leaf1598FlatSound : Sound leaf1598Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1598CertificateValid
    leaf1598InnerLogValid leaf1598CoversExact leaf1598LowerChecked

private noncomputable def leaf1599Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1599Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435591/268435456) }, vSqrt := { lower := (8191/8192), upper := (5592416/5592357) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (302020471/268435456) }, upper := { exponent := 0, mantissa := (1169/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11184773/11184714) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1599InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1599LocalValidity :
    LeafFacts leaf1599Box leaf1599Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1599Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5592416/5592357) }) = true
      norm_num [leaf1599Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1599CertificateValid :
    WideCertificateValid leaf1599Box leaf1599Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi140ValidityFacts
    leaf1599LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1599CoverageChecked :
    coverageCheck (innerAD leaf1599Box) leaf1599InnerLog = true := by
  rfl'

private theorem leaf1599InnerLogValid :
    leaf1599InnerLog.Valid 8 (innerAD leaf1599Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1599CoverageChecked

private noncomputable def leaf1599InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1599InputLogOnePlusV_eq :
    leaf1599InputLogOnePlusV = outerEnclosure 24
      (leaf1599Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1599RoundedFacts : LeafRoundedFacts 8
    leaf1599Certificate.logOnePlusV leaf1599InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1599InputLogOnePlusV_eq }

private noncomputable def leaf1599Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi140InputQChi innerPair2Input
    leaf1599InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1599LowerChecked :
    lowerCheck 24 leaf1599Box leaf1599Inputs = true := by
  rfl'

private theorem leaf1599CoversExact : CoversExact 8
    leaf1599Box leaf1599Certificate leaf1599InnerLog leaf1599Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi140RoundedFacts
    innerPair2RoundedFacts leaf1599RoundedFacts (by rfl)

private theorem leaf1599FlatSound : Sound leaf1599Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1599CertificateValid
    leaf1599InnerLogValid leaf1599CoversExact leaf1599LowerChecked

private noncomputable def leaf1600Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1600Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435591/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108237) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (305100475/268435456) }, upper := { exponent := 0, mantissa := (4723/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217229/134216474) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1600InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1600LocalValidity :
    LeafFacts leaf1600Box leaf1600Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1600Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108237) }) = true
      norm_num [leaf1600Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1600CertificateValid :
    WideCertificateValid leaf1600Box leaf1600Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi143ValidityFacts
    leaf1600LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1600CoverageChecked :
    coverageCheck (innerAD leaf1600Box) leaf1600InnerLog = true := by
  rfl'

private theorem leaf1600InnerLogValid :
    leaf1600InnerLog.Valid 8 (innerAD leaf1600Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1600CoverageChecked

private noncomputable def leaf1600InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629175/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1600InputLogOnePlusV_eq :
    leaf1600InputLogOnePlusV = outerEnclosure 24
      (leaf1600Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1600RoundedFacts : LeafRoundedFacts 8
    leaf1600Certificate.logOnePlusV leaf1600InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1600InputLogOnePlusV_eq }

private noncomputable def leaf1600Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1600InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1600LowerChecked :
    lowerCheck 24 leaf1600Box leaf1600Inputs = true := by
  rfl'

private theorem leaf1600CoversExact : CoversExact 8
    leaf1600Box leaf1600Certificate leaf1600InnerLog leaf1600Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1600RoundedFacts (by rfl)

private theorem leaf1600FlatSound : Sound leaf1600Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1600CertificateValid
    leaf1600InnerLogValid leaf1600CoversExact leaf1600LowerChecked

private noncomputable def leaf1601Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1601Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435593/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (305755793/268435456) }, upper := { exponent := 0, mantissa := (2367/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108609/67108226) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1601InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1601LocalValidity :
    LeafFacts leaf1601Box leaf1601Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1601Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554113) }) = true
      norm_num [leaf1601Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1601CertificateValid :
    WideCertificateValid leaf1601Box leaf1601Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi143ValidityFacts
    leaf1601LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1601CoverageChecked :
    coverageCheck (innerAD leaf1601Box) leaf1601InnerLog = true := by
  rfl'

private theorem leaf1601InnerLogValid :
    leaf1601InnerLog.Valid 8 (innerAD leaf1601Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1601CoverageChecked

private noncomputable def leaf1601InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453647/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1601InputLogOnePlusV_eq :
    leaf1601InputLogOnePlusV = outerEnclosure 24
      (leaf1601Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1601RoundedFacts : LeafRoundedFacts 8
    leaf1601Certificate.logOnePlusV leaf1601InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1601InputLogOnePlusV_eq }

private noncomputable def leaf1601Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1601InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1601LowerChecked :
    lowerCheck 24 leaf1601Box leaf1601Inputs = true := by
  rfl'

private theorem leaf1601CoversExact : CoversExact 8
    leaf1601Box leaf1601Certificate leaf1601InnerLog leaf1601Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1601RoundedFacts (by rfl)

private theorem leaf1601FlatSound : Sound leaf1601Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1601CertificateValid
    leaf1601InnerLogValid leaf1601CoversExact leaf1601LowerChecked

private noncomputable def leaf1602Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1602Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435593/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777045) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (308770265/268435456) }, upper := { exponent := 0, mantissa := (1195/1024) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554293/33554090) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1602InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1602LocalValidity :
    LeafFacts leaf1602Box leaf1602Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1602Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777045) }) = true
      norm_num [leaf1602Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1602CertificateValid :
    WideCertificateValid leaf1602Box leaf1602Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi144ValidityFacts
    leaf1602LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1602CoverageChecked :
    coverageCheck (innerAD leaf1602Box) leaf1602InnerLog = true := by
  rfl'

private theorem leaf1602InnerLogValid :
    leaf1602InnerLog.Valid 8 (innerAD leaf1602Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1602CoverageChecked

private noncomputable def leaf1602InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814591/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1602InputLogOnePlusV_eq :
    leaf1602InputLogOnePlusV = outerEnclosure 24
      (leaf1602Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1602RoundedFacts : LeafRoundedFacts 8
    leaf1602Certificate.logOnePlusV leaf1602InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1602InputLogOnePlusV_eq }

private noncomputable def leaf1602Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1602InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1602LowerChecked :
    lowerCheck 24 leaf1602Box leaf1602Inputs = true := by
  rfl'

private theorem leaf1602CoversExact : CoversExact 8
    leaf1602Box leaf1602Certificate leaf1602InnerLog leaf1602Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1602RoundedFacts (by rfl)

private theorem leaf1602FlatSound : Sound leaf1602Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1602CertificateValid
    leaf1602InnerLogValid leaf1602CoversExact leaf1602LowerChecked

private noncomputable def leaf1603Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1603Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388521) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (309491115/268435456) }, upper := { exponent := 0, mantissa := (599/512) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777145/16777042) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1603InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1603LocalValidity :
    LeafFacts leaf1603Box leaf1603Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1603Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388521) }) = true
      norm_num [leaf1603Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1603CertificateValid :
    WideCertificateValid leaf1603Box leaf1603Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi144ValidityFacts
    leaf1603LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1603CoverageChecked :
    coverageCheck (innerAD leaf1603Box) leaf1603InnerLog = true := by
  rfl'

private theorem leaf1603InnerLogValid :
    leaf1603InnerLog.Valid 8 (innerAD leaf1603Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1603CoverageChecked

private noncomputable def leaf1603InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90853/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf1603InputLogOnePlusV_eq :
    leaf1603InputLogOnePlusV = outerEnclosure 24
      (leaf1603Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1603RoundedFacts : LeafRoundedFacts 8
    leaf1603Certificate.logOnePlusV leaf1603InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1603InputLogOnePlusV_eq }

private noncomputable def leaf1603Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1603InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1603LowerChecked :
    lowerCheck 24 leaf1603Box leaf1603Inputs = true := by
  rfl'

private theorem leaf1603CoversExact : CoversExact 8
    leaf1603Box leaf1603Certificate leaf1603InnerLog leaf1603Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1603RoundedFacts (by rfl)

private theorem leaf1603FlatSound : Sound leaf1603Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1603CertificateValid
    leaf1603InnerLogValid leaf1603CoversExact leaf1603LowerChecked

private noncomputable def leaf1604Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1604Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435591/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108333) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (298809403/268435456) }, upper := { exponent := 0, mantissa := (4627/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217325/134216666) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1604InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1604LocalValidity :
    LeafFacts leaf1604Box leaf1604Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1604Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108333) }) = true
      norm_num [leaf1604Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1604CertificateValid :
    WideCertificateValid leaf1604Box leaf1604Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi139ValidityFacts
    leaf1604LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1604CoverageChecked :
    coverageCheck (innerAD leaf1604Box) leaf1604InnerLog = true := by
  rfl'

private theorem leaf1604InnerLogValid :
    leaf1604InnerLog.Valid 8 (innerAD leaf1604Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1604CoverageChecked

private noncomputable def leaf1604InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1604InputLogOnePlusV_eq :
    leaf1604InputLogOnePlusV = outerEnclosure 24
      (leaf1604Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1604RoundedFacts : LeafRoundedFacts 8
    leaf1604Certificate.logOnePlusV leaf1604InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1604InputLogOnePlusV_eq }

private noncomputable def leaf1604Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1604InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1604LowerChecked :
    lowerCheck 24 leaf1604Box leaf1604Inputs = true := by
  rfl'

private theorem leaf1604CoversExact : CoversExact 8
    leaf1604Box leaf1604Certificate leaf1604InnerLog leaf1604Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1604RoundedFacts (by rfl)

private theorem leaf1604FlatSound : Sound leaf1604Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1604CertificateValid
    leaf1604InnerLogValid leaf1604CoversExact leaf1604LowerChecked

private noncomputable def leaf1605Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1605Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435593/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777081) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (299333657/268435456) }, upper := { exponent := 0, mantissa := (1159/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554329/33554162) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1605InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1605LocalValidity :
    LeafFacts leaf1605Box leaf1605Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1605Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777081) }) = true
      norm_num [leaf1605Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1605CertificateValid :
    WideCertificateValid leaf1605Box leaf1605Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi139ValidityFacts
    leaf1605LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1605CoverageChecked :
    coverageCheck (innerAD leaf1605Box) leaf1605InnerLog = true := by
  rfl'

private theorem leaf1605InnerLogValid :
    leaf1605InnerLog.Valid 8 (innerAD leaf1605Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1605CoverageChecked

private noncomputable def leaf1605InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907291/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1605InputLogOnePlusV_eq :
    leaf1605InputLogOnePlusV = outerEnclosure 24
      (leaf1605Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1605RoundedFacts : LeafRoundedFacts 8
    leaf1605Certificate.logOnePlusV leaf1605InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1605InputLogOnePlusV_eq }

private noncomputable def leaf1605Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1605InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1605LowerChecked :
    lowerCheck 24 leaf1605Box leaf1605Inputs = true := by
  rfl'

private theorem leaf1605CoversExact : CoversExact 8
    leaf1605Box leaf1605Certificate leaf1605InnerLog leaf1605Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1605RoundedFacts (by rfl)

private theorem leaf1605FlatSound : Sound leaf1605Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1605CertificateValid
    leaf1605InnerLogValid leaf1605CoversExact leaf1605LowerChecked

private noncomputable def leaf1606Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1606Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435593/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (302610257/268435456) }, upper := { exponent := 0, mantissa := (2343/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108633/67108274) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1606InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1606LocalValidity :
    LeafFacts leaf1606Box leaf1606Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1606Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554137) }) = true
      norm_num [leaf1606Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1606CertificateValid :
    WideCertificateValid leaf1606Box leaf1606Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi140ValidityFacts
    leaf1606LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1606CoverageChecked :
    coverageCheck (innerAD leaf1606Box) leaf1606InnerLog = true := by
  rfl'

private theorem leaf1606InnerLogValid :
    leaf1606InnerLog.Valid 8 (innerAD leaf1606Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1606CoverageChecked

private noncomputable def leaf1606InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814585/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1606InputLogOnePlusV_eq :
    leaf1606InputLogOnePlusV = outerEnclosure 24
      (leaf1606Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1606RoundedFacts : LeafRoundedFacts 8
    leaf1606Certificate.logOnePlusV leaf1606InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1606InputLogOnePlusV_eq }

private noncomputable def leaf1606Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi140InputQChi innerPair2Input
    leaf1606InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1606LowerChecked :
    lowerCheck 24 leaf1606Box leaf1606Inputs = true := by
  rfl'

private theorem leaf1606CoversExact : CoversExact 8
    leaf1606Box leaf1606Certificate leaf1606InnerLog leaf1606Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi140RoundedFacts
    innerPair2RoundedFacts leaf1606RoundedFacts (by rfl)

private theorem leaf1606FlatSound : Sound leaf1606Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1606CertificateValid
    leaf1606InnerLogValid leaf1606CoversExact leaf1606LowerChecked

private noncomputable def leaf1607Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1607Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388533) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (303200043/268435456) }, upper := { exponent := 0, mantissa := (587/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777157/16777066) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1607InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1607LocalValidity :
    LeafFacts leaf1607Box leaf1607Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1607Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388533) }) = true
      norm_num [leaf1607Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1607CertificateValid :
    WideCertificateValid leaf1607Box leaf1607Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi140ValidityFacts
    leaf1607LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1607CoverageChecked :
    coverageCheck (innerAD leaf1607Box) leaf1607InnerLog = true := by
  rfl'

private theorem leaf1607InnerLogValid :
    leaf1607InnerLog.Valid 8 (innerAD leaf1607Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1607CoverageChecked

private noncomputable def leaf1607InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907293/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1607InputLogOnePlusV_eq :
    leaf1607InputLogOnePlusV = outerEnclosure 24
      (leaf1607Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1607RoundedFacts : LeafRoundedFacts 8
    leaf1607Certificate.logOnePlusV leaf1607InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1607InputLogOnePlusV_eq }

private noncomputable def leaf1607Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi140InputQChi innerPair2Input
    leaf1607InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1607LowerChecked :
    lowerCheck 24 leaf1607Box leaf1607Inputs = true := by
  rfl'

private theorem leaf1607CoversExact : CoversExact 8
    leaf1607Box leaf1607Certificate leaf1607InnerLog leaf1607Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi140RoundedFacts
    innerPair2RoundedFacts leaf1607RoundedFacts (by rfl)

private theorem leaf1607FlatSound : Sound leaf1607Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1607CertificateValid
    leaf1607InnerLogValid leaf1607CoversExact leaf1607LowerChecked

private noncomputable def leaf1608Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1608Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (8191/8192), upper := (22369664/22369405) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (306411111/268435456) }, upper := { exponent := 0, mantissa := (4745/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (44739069/44738810) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1608InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1608LocalValidity :
    LeafFacts leaf1608Box leaf1608Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1608Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22369664/22369405) }) = true
      norm_num [leaf1608Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1608CertificateValid :
    WideCertificateValid leaf1608Box leaf1608Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi143ValidityFacts
    leaf1608LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1608CoverageChecked :
    coverageCheck (innerAD leaf1608Box) leaf1608InnerLog = true := by
  rfl'

private theorem leaf1608InnerLogValid :
    leaf1608InnerLog.Valid 8 (innerAD leaf1608Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1608CoverageChecked

private noncomputable def leaf1608InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814589/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1608InputLogOnePlusV_eq :
    leaf1608InputLogOnePlusV = outerEnclosure 24
      (leaf1608Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1608RoundedFacts : LeafRoundedFacts 8
    leaf1608Certificate.logOnePlusV leaf1608InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1608InputLogOnePlusV_eq }

private noncomputable def leaf1608Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1608InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1608LowerChecked :
    lowerCheck 24 leaf1608Box leaf1608Inputs = true := by
  rfl'

private theorem leaf1608CoversExact : CoversExact 8
    leaf1608Box leaf1608Certificate leaf1608InnerLog leaf1608Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1608RoundedFacts (by rfl)

private theorem leaf1608FlatSound : Sound leaf1608Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1608CertificateValid
    leaf1608InnerLogValid leaf1608CoversExact leaf1608LowerChecked

private noncomputable def leaf1609Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1609Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777051) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (307066429/268435456) }, upper := { exponent := 0, mantissa := (1189/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554299/33554102) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1609InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1609LocalValidity :
    LeafFacts leaf1609Box leaf1609Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1609Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777051) }) = true
      norm_num [leaf1609Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1609CertificateValid :
    WideCertificateValid leaf1609Box leaf1609Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi143ValidityFacts
    leaf1609LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1609CoverageChecked :
    coverageCheck (innerAD leaf1609Box) leaf1609InnerLog = true := by
  rfl'

private theorem leaf1609InnerLogValid :
    leaf1609InnerLog.Valid 8 (innerAD leaf1609Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1609CoverageChecked

private noncomputable def leaf1609InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629179/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1609InputLogOnePlusV_eq :
    leaf1609InputLogOnePlusV = outerEnclosure 24
      (leaf1609Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1609RoundedFacts : LeafRoundedFacts 8
    leaf1609Certificate.logOnePlusV leaf1609InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1609InputLogOnePlusV_eq }

private noncomputable def leaf1609Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1609InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1609LowerChecked :
    lowerCheck 24 leaf1609Box leaf1609Inputs = true := by
  rfl'

private theorem leaf1609CoversExact : CoversExact 8
    leaf1609Box leaf1609Certificate leaf1609InnerLog leaf1609Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1609RoundedFacts (by rfl)

private theorem leaf1609FlatSound : Sound leaf1609Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1609CertificateValid
    leaf1609InnerLogValid leaf1609CoversExact leaf1609LowerChecked

private noncomputable def leaf1610Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1610Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (310211965/268435456) }, upper := { exponent := 0, mantissa := (1201/1024) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554287/33554078) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1610InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1610LocalValidity :
    LeafFacts leaf1610Box leaf1610Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1610Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777039) }) = true
      norm_num [leaf1610Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1610CertificateValid :
    WideCertificateValid leaf1610Box leaf1610Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi144ValidityFacts
    leaf1610LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1610CoverageChecked :
    coverageCheck (innerAD leaf1610Box) leaf1610InnerLog = true := by
  rfl'

private theorem leaf1610InnerLogValid :
    leaf1610InnerLog.Valid 8 (innerAD leaf1610Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1610CoverageChecked

private noncomputable def leaf1610InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1610InputLogOnePlusV_eq :
    leaf1610InputLogOnePlusV = outerEnclosure 24
      (leaf1610Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1610RoundedFacts : LeafRoundedFacts 8
    leaf1610Certificate.logOnePlusV leaf1610InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1610InputLogOnePlusV_eq }

private noncomputable def leaf1610Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1610InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1610LowerChecked :
    lowerCheck 24 leaf1610Box leaf1610Inputs = true := by
  rfl'

private theorem leaf1610CoversExact : CoversExact 8
    leaf1610Box leaf1610Certificate leaf1610InnerLog leaf1610Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1610RoundedFacts (by rfl)

private theorem leaf1610FlatSound : Sound leaf1610Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1610CertificateValid
    leaf1610InnerLogValid leaf1610CoversExact leaf1610LowerChecked

private noncomputable def leaf1611Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1611Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (8191/8192), upper := (4194312/4194259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (310932815/268435456) }, upper := { exponent := 0, mantissa := (301/256) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388571/8388518) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1611InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1611LocalValidity :
    LeafFacts leaf1611Box leaf1611Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1611Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194312/4194259) }) = true
      norm_num [leaf1611Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1611CertificateValid :
    WideCertificateValid leaf1611Box leaf1611Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi144ValidityFacts
    leaf1611LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1611CoverageChecked :
    coverageCheck (innerAD leaf1611Box) leaf1611InnerLog = true := by
  rfl'

private theorem leaf1611InnerLogValid :
    leaf1611InnerLog.Valid 8 (innerAD leaf1611Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1611CoverageChecked

private noncomputable def leaf1611InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629187/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1611InputLogOnePlusV_eq :
    leaf1611InputLogOnePlusV = outerEnclosure 24
      (leaf1611Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1611RoundedFacts : LeafRoundedFacts 8
    leaf1611Certificate.logOnePlusV leaf1611InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1611InputLogOnePlusV_eq }

private noncomputable def leaf1611Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1611InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1611LowerChecked :
    lowerCheck 24 leaf1611Box leaf1611Inputs = true := by
  rfl'

private theorem leaf1611CoversExact : CoversExact 8
    leaf1611Box leaf1611Certificate leaf1611InnerLog leaf1611Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1611RoundedFacts (by rfl)

private theorem leaf1611FlatSound : Sound leaf1611Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1611CertificateValid
    leaf1611InnerLogValid leaf1611CoversExact leaf1611LowerChecked

private noncomputable def leaf1612Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1612Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217855/134217728) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554033) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (156203587/134217728) }, upper := { exponent := 0, mantissa := (2447/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108529/67108066) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1612InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1612LocalValidity :
    LeafFacts leaf1612Box leaf1612Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1612Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554033) }) = true
      norm_num [leaf1612Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1612CertificateValid :
    WideCertificateValid leaf1612Box leaf1612Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi96ValidityFacts
    leaf1612LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1612CoverageChecked :
    coverageCheck (innerAD leaf1612Box) leaf1612InnerLog = true := by
  rfl'

private theorem leaf1612InnerLogValid :
    leaf1612InnerLog.Valid 8 (innerAD leaf1612Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1612CoverageChecked

private noncomputable def leaf1612InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907299/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1612InputLogOnePlusV_eq :
    leaf1612InputLogOnePlusV = outerEnclosure 24
      (leaf1612Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1612RoundedFacts : LeafRoundedFacts 8
    leaf1612Certificate.logOnePlusV leaf1612InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1612InputLogOnePlusV_eq }

private noncomputable def leaf1612Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi96InputQChi innerPair3Input
    leaf1612InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1612LowerChecked :
    lowerCheck 24 leaf1612Box leaf1612Inputs = true := by
  rfl'

private theorem leaf1612CoversExact : CoversExact 8
    leaf1612Box leaf1612Certificate leaf1612InnerLog leaf1612Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi96RoundedFacts
    innerPair3RoundedFacts leaf1612RoundedFacts (by rfl)

private theorem leaf1612FlatSound : Sound leaf1612Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1612CertificateValid
    leaf1612InnerLogValid leaf1612CoversExact leaf1612LowerChecked

private noncomputable def leaf1613Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1613Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217857/134217728) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777013) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (156596777/134217728) }, upper := { exponent := 0, mantissa := (1227/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554261/33554026) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1613InnerLog : WideLogData :=
  innerPair49Data

set_option maxRecDepth 1000000 in
private theorem leaf1613LocalValidity :
    LeafFacts leaf1613Box leaf1613Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1613Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777013) }) = true
      norm_num [leaf1613Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1613CertificateValid :
    WideCertificateValid leaf1613Box leaf1613Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi96ValidityFacts
    leaf1613LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1613CoverageChecked :
    coverageCheck (innerAD leaf1613Box) leaf1613InnerLog = true := by
  rfl'

private theorem leaf1613InnerLogValid :
    leaf1613InnerLog.Valid 8 (innerAD leaf1613Box) :=
  wideLogDataValid_of_cachedCheck endpoint12PositiveFacts
    endpoint26PositiveFacts.valid leaf1613CoverageChecked

private noncomputable def leaf1613InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814599/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1613InputLogOnePlusV_eq :
    leaf1613InputLogOnePlusV = outerEnclosure 24
      (leaf1613Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1613RoundedFacts : LeafRoundedFacts 8
    leaf1613Certificate.logOnePlusV leaf1613InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1613InputLogOnePlusV_eq }

private noncomputable def leaf1613Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi96InputQChi innerPair49Input
    leaf1613InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1613LowerChecked :
    lowerCheck 24 leaf1613Box leaf1613Inputs = true := by
  rfl'

private theorem leaf1613CoversExact : CoversExact 8
    leaf1613Box leaf1613Certificate leaf1613InnerLog leaf1613Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi96RoundedFacts
    innerPair49RoundedFacts leaf1613RoundedFacts (by rfl)

private theorem leaf1613FlatSound : Sound leaf1613Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1613CertificateValid
    leaf1613InnerLogValid leaf1613CoversExact leaf1613LowerChecked

private noncomputable def leaf1614Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1614Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108009) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (319779635/268435456) }, upper := { exponent := 0, mantissa := (4951/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217001/134216018) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1614InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1614LocalValidity :
    LeafFacts leaf1614Box leaf1614Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1614Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108009) }) = true
      norm_num [leaf1614Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1614CertificateValid :
    WideCertificateValid leaf1614Box leaf1614Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi145ValidityFacts
    leaf1614LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1614CoverageChecked :
    coverageCheck (innerAD leaf1614Box) leaf1614InnerLog = true := by
  rfl'

private theorem leaf1614InnerLogValid :
    leaf1614InnerLog.Valid 8 (innerAD leaf1614Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1614CoverageChecked

private noncomputable def leaf1614InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907301/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1614InputLogOnePlusV_eq :
    leaf1614InputLogOnePlusV = outerEnclosure 24
      (leaf1614Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1614RoundedFacts : LeafRoundedFacts 8
    leaf1614Certificate.logOnePlusV leaf1614InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1614InputLogOnePlusV_eq }

private noncomputable def leaf1614Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1614InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1614LowerChecked :
    lowerCheck 24 leaf1614Box leaf1614Inputs = true := by
  rfl'

private theorem leaf1614CoversExact : CoversExact 8
    leaf1614Box leaf1614Certificate leaf1614InnerLog leaf1614Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1614RoundedFacts (by rfl)

private theorem leaf1614FlatSound : Sound leaf1614Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1614CertificateValid
    leaf1614InnerLogValid leaf1614CoversExact leaf1614LowerChecked

private noncomputable def leaf1615Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1615Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (8191/8192), upper := (4194312/4194247) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (323449425/268435456) }, upper := { exponent := 0, mantissa := (313/256) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388559/8388494) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1615InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1615LocalValidity :
    LeafFacts leaf1615Box leaf1615Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1615Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194312/4194247) }) = true
      norm_num [leaf1615Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1615CertificateValid :
    WideCertificateValid leaf1615Box leaf1615Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi146ValidityFacts
    leaf1615LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1615CoverageChecked :
    coverageCheck (innerAD leaf1615Box) leaf1615InnerLog = true := by
  rfl'

private theorem leaf1615InnerLogValid :
    leaf1615InnerLog.Valid 8 (innerAD leaf1615Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1615CoverageChecked

private noncomputable def leaf1615InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1615InputLogOnePlusV_eq :
    leaf1615InputLogOnePlusV = outerEnclosure 24
      (leaf1615Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1615RoundedFacts : LeafRoundedFacts 8
    leaf1615Certificate.logOnePlusV leaf1615InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1615InputLogOnePlusV_eq }

private noncomputable def leaf1615Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1615InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1615LowerChecked :
    lowerCheck 24 leaf1615Box leaf1615Inputs = true := by
  rfl'

private theorem leaf1615CoversExact : CoversExact 8
    leaf1615Box leaf1615Certificate leaf1615InnerLog leaf1615Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1615RoundedFacts (by rfl)

private theorem leaf1615FlatSound : Sound leaf1615Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1615CertificateValid
    leaf1615InnerLogValid leaf1615CoversExact leaf1615LowerChecked

private noncomputable def leaf1616Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1616Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33553997) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (320697081/268435456) }, upper := { exponent := 0, mantissa := (2483/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108493/67107994) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1616InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1616LocalValidity :
    LeafFacts leaf1616Box leaf1616Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1616Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33553997) }) = true
      norm_num [leaf1616Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1616CertificateValid :
    WideCertificateValid leaf1616Box leaf1616Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi145ValidityFacts
    leaf1616LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1616CoverageChecked :
    coverageCheck (innerAD leaf1616Box) leaf1616InnerLog = true := by
  rfl'

private theorem leaf1616InnerLogValid :
    leaf1616InnerLog.Valid 8 (innerAD leaf1616Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1616CoverageChecked

private noncomputable def leaf1616InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1616InputLogOnePlusV_eq :
    leaf1616InputLogOnePlusV = outerEnclosure 24
      (leaf1616Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1616RoundedFacts : LeafRoundedFacts 8
    leaf1616Certificate.logOnePlusV leaf1616InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1616InputLogOnePlusV_eq }

private noncomputable def leaf1616Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1616InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1616LowerChecked :
    lowerCheck 24 leaf1616Box leaf1616Inputs = true := by
  rfl'

private theorem leaf1616CoversExact : CoversExact 8
    leaf1616Box leaf1616Certificate leaf1616InnerLog leaf1616Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1616RoundedFacts (by rfl)

private theorem leaf1616FlatSound : Sound leaf1616Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1616CertificateValid
    leaf1616InnerLogValid leaf1616CoversExact leaf1616LowerChecked

private noncomputable def leaf1617Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1617Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (699052/699041) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (324432403/268435456) }, upper := { exponent := 0, mantissa := (157/128) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1398093/1398082) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1617InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1617LocalValidity :
    LeafFacts leaf1617Box leaf1617Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1617Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (699052/699041) }) = true
      norm_num [leaf1617Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1617CertificateValid :
    WideCertificateValid leaf1617Box leaf1617Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi146ValidityFacts
    leaf1617LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1617CoverageChecked :
    coverageCheck (innerAD leaf1617Box) leaf1617InnerLog = true := by
  rfl'

private theorem leaf1617InnerLogValid :
    leaf1617InnerLog.Valid 8 (innerAD leaf1617Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1617CoverageChecked

private noncomputable def leaf1617InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1617InputLogOnePlusV_eq :
    leaf1617InputLogOnePlusV = outerEnclosure 24
      (leaf1617Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1617RoundedFacts : LeafRoundedFacts 8
    leaf1617Certificate.logOnePlusV leaf1617InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1617InputLogOnePlusV_eq }

private noncomputable def leaf1617Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1617InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1617LowerChecked :
    lowerCheck 24 leaf1617Box leaf1617Inputs = true := by
  rfl'

private theorem leaf1617CoversExact : CoversExact 8
    leaf1617Box leaf1617Certificate leaf1617InnerLog leaf1617Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1617RoundedFacts (by rfl)

private theorem leaf1617FlatSound : Sound leaf1617Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1617CertificateValid
    leaf1617InnerLogValid leaf1617CoversExact leaf1617LowerChecked

private noncomputable def leaf1618Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf1618Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217859/134217728) }, vSqrt := { lower := (8191/8192), upper := (11184832/11184673) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (156989967/134217728) }, upper := { exponent := 0, mantissa := (2461/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22369505/22369346) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1618InnerLog : WideLogData :=
  innerPair49Data

set_option maxRecDepth 1000000 in
private theorem leaf1618LocalValidity :
    LeafFacts leaf1618Box leaf1618Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1618Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11184832/11184673) }) = true
      norm_num [leaf1618Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1618CertificateValid :
    WideCertificateValid leaf1618Box leaf1618Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi96ValidityFacts
    leaf1618LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1618CoverageChecked :
    coverageCheck (innerAD leaf1618Box) leaf1618InnerLog = true := by
  rfl'

private theorem leaf1618InnerLogValid :
    leaf1618InnerLog.Valid 8 (innerAD leaf1618Box) :=
  wideLogDataValid_of_cachedCheck endpoint12PositiveFacts
    endpoint26PositiveFacts.valid leaf1618CoverageChecked

private noncomputable def leaf1618InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726825/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1618InputLogOnePlusV_eq :
    leaf1618InputLogOnePlusV = outerEnclosure 24
      (leaf1618Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1618RoundedFacts : LeafRoundedFacts 8
    leaf1618Certificate.logOnePlusV leaf1618InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1618InputLogOnePlusV_eq }

private noncomputable def leaf1618Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi96InputQChi innerPair49Input
    leaf1618InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1618LowerChecked :
    lowerCheck 24 leaf1618Box leaf1618Inputs = true := by
  rfl'

private theorem leaf1618CoversExact : CoversExact 8
    leaf1618Box leaf1618Certificate leaf1618InnerLog leaf1618Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi96RoundedFacts
    innerPair49RoundedFacts leaf1618RoundedFacts (by rfl)

private theorem leaf1618FlatSound : Sound leaf1618Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1618CertificateValid
    leaf1618InnerLogValid leaf1618CoversExact leaf1618LowerChecked

private noncomputable def leaf1619Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/64), chiHi := (13/256) }

private noncomputable def leaf1619Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777021) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (314799201/268435456) }, upper := { exponent := 0, mantissa := (1219/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi159LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554269/33554042) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1619InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1619LocalValidity :
    LeafFacts leaf1619Box leaf1619Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1619Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777021) }) = true
      norm_num [leaf1619Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1619CertificateValid :
    WideCertificateValid leaf1619Box leaf1619Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi159ValidityFacts
    leaf1619LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1619CoverageChecked :
    coverageCheck (innerAD leaf1619Box) leaf1619InnerLog = true := by
  rfl'

private theorem leaf1619InnerLogValid :
    leaf1619InnerLog.Valid 8 (innerAD leaf1619Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1619CoverageChecked

private noncomputable def leaf1619InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814597/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1619InputLogOnePlusV_eq :
    leaf1619InputLogOnePlusV = outerEnclosure 24
      (leaf1619Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1619RoundedFacts : LeafRoundedFacts 8
    leaf1619Certificate.logOnePlusV leaf1619InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1619InputLogOnePlusV_eq }

private noncomputable def leaf1619Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi159InputQChi innerPair3Input
    leaf1619InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1619LowerChecked :
    lowerCheck 24 leaf1619Box leaf1619Inputs = true := by
  rfl'

private theorem leaf1619CoversExact : CoversExact 8
    leaf1619Box leaf1619Certificate leaf1619InnerLog leaf1619Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi159RoundedFacts
    innerPair3RoundedFacts leaf1619RoundedFacts (by rfl)

private theorem leaf1619FlatSound : Sound leaf1619Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1619CertificateValid
    leaf1619InnerLogValid leaf1619CoversExact leaf1619LowerChecked

private noncomputable def leaf1620Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (13/256), chiHi := (7/128) }

private noncomputable def leaf1620Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388503) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (318665587/268435456) }, upper := { exponent := 0, mantissa := (617/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi160LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777127/16777006) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1620InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1620LocalValidity :
    LeafFacts leaf1620Box leaf1620Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1620Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388503) }) = true
      norm_num [leaf1620Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1620CertificateValid :
    WideCertificateValid leaf1620Box leaf1620Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi160ValidityFacts
    leaf1620LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1620CoverageChecked :
    coverageCheck (innerAD leaf1620Box) leaf1620InnerLog = true := by
  rfl'

private theorem leaf1620InnerLogValid :
    leaf1620InnerLog.Valid 8 (innerAD leaf1620Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1620CoverageChecked

private noncomputable def leaf1620InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814601/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1620InputLogOnePlusV_eq :
    leaf1620InputLogOnePlusV = outerEnclosure 24
      (leaf1620Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1620RoundedFacts : LeafRoundedFacts 8
    leaf1620Certificate.logOnePlusV leaf1620InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1620InputLogOnePlusV_eq }

private noncomputable def leaf1620Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi160InputQChi innerPair3Input
    leaf1620InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1620LowerChecked :
    lowerCheck 24 leaf1620Box leaf1620Inputs = true := by
  rfl'

private theorem leaf1620CoversExact : CoversExact 8
    leaf1620Box leaf1620Certificate leaf1620InnerLog leaf1620Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi160RoundedFacts
    innerPair3RoundedFacts leaf1620RoundedFacts (by rfl)

private theorem leaf1620FlatSound : Sound leaf1620Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1620CertificateValid
    leaf1620InnerLogValid leaf1620CoversExact leaf1620LowerChecked

private noncomputable def leaf1621Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1621Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67107979) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (321614527/268435456) }, upper := { exponent := 0, mantissa := (4981/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216971/134215958) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1621InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1621LocalValidity :
    LeafFacts leaf1621Box leaf1621Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1621Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67107979) }) = true
      norm_num [leaf1621Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1621CertificateValid :
    WideCertificateValid leaf1621Box leaf1621Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi145ValidityFacts
    leaf1621LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1621CoverageChecked :
    coverageCheck (innerAD leaf1621Box) leaf1621InnerLog = true := by
  rfl'

private theorem leaf1621InnerLogValid :
    leaf1621InnerLog.Valid 8 (innerAD leaf1621Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1621CoverageChecked

private noncomputable def leaf1621InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1621InputLogOnePlusV_eq :
    leaf1621InputLogOnePlusV = outerEnclosure 24
      (leaf1621Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1621RoundedFacts : LeafRoundedFacts 8
    leaf1621Certificate.logOnePlusV leaf1621InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1621InputLogOnePlusV_eq }

private noncomputable def leaf1621Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1621InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1621LowerChecked :
    lowerCheck 24 leaf1621Box leaf1621Inputs = true := by
  rfl'

private theorem leaf1621CoversExact : CoversExact 8
    leaf1621Box leaf1621Certificate leaf1621InnerLog leaf1621Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1621RoundedFacts (by rfl)

private theorem leaf1621FlatSound : Sound leaf1621Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1621CertificateValid
    leaf1621InnerLogValid leaf1621CoversExact leaf1621LowerChecked

private noncomputable def leaf1622Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1622Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (4194312/4194245) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (325415381/268435456) }, upper := { exponent := 0, mantissa := (315/256) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388557/8388490) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1622InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1622LocalValidity :
    LeafFacts leaf1622Box leaf1622Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1622Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194312/4194245) }) = true
      norm_num [leaf1622Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1622CertificateValid :
    WideCertificateValid leaf1622Box leaf1622Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi146ValidityFacts
    leaf1622LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1622CoverageChecked :
    coverageCheck (innerAD leaf1622Box) leaf1622InnerLog = true := by
  rfl'

private theorem leaf1622InnerLogValid :
    leaf1622InnerLog.Valid 8 (innerAD leaf1622Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1622CoverageChecked

private noncomputable def leaf1622InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1622InputLogOnePlusV_eq :
    leaf1622InputLogOnePlusV = outerEnclosure 24
      (leaf1622Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1622RoundedFacts : LeafRoundedFacts 8
    leaf1622Certificate.logOnePlusV leaf1622InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1622InputLogOnePlusV_eq }

private noncomputable def leaf1622Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1622InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1622LowerChecked :
    lowerCheck 24 leaf1622Box leaf1622Inputs = true := by
  rfl'

private theorem leaf1622CoversExact : CoversExact 8
    leaf1622Box leaf1622Certificate leaf1622InnerLog leaf1622Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1622RoundedFacts (by rfl)

private theorem leaf1622FlatSound : Sound leaf1622Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1622CertificateValid
    leaf1622InnerLogValid leaf1622CoversExact leaf1622LowerChecked

private noncomputable def leaf1623Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1623Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16776991) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (322531973/268435456) }, upper := { exponent := 0, mantissa := (1249/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554239/33553982) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1623InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1623LocalValidity :
    LeafFacts leaf1623Box leaf1623Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1623Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16776991) }) = true
      norm_num [leaf1623Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1623CertificateValid :
    WideCertificateValid leaf1623Box leaf1623Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi145ValidityFacts
    leaf1623LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1623CoverageChecked :
    coverageCheck (innerAD leaf1623Box) leaf1623InnerLog = true := by
  rfl'

private theorem leaf1623InnerLogValid :
    leaf1623InnerLog.Valid 8 (innerAD leaf1623Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1623CoverageChecked

private noncomputable def leaf1623InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1623InputLogOnePlusV_eq :
    leaf1623InputLogOnePlusV = outerEnclosure 24
      (leaf1623Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1623RoundedFacts : LeafRoundedFacts 8
    leaf1623Certificate.logOnePlusV leaf1623InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1623InputLogOnePlusV_eq }

private noncomputable def leaf1623Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1623InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1623LowerChecked :
    lowerCheck 24 leaf1623Box leaf1623Inputs = true := by
  rfl'

private theorem leaf1623CoversExact : CoversExact 8
    leaf1623Box leaf1623Certificate leaf1623InnerLog leaf1623Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1623RoundedFacts (by rfl)

private theorem leaf1623FlatSound : Sound leaf1623Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1623CertificateValid
    leaf1623InnerLogValid leaf1623CoversExact leaf1623LowerChecked

private noncomputable def leaf1624Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1624Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (326398359/268435456) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1624InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1624LocalValidity :
    LeafFacts leaf1624Box leaf1624Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1624Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1048578/1048561) }) = true
      norm_num [leaf1624Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1624CertificateValid :
    WideCertificateValid leaf1624Box leaf1624Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi146ValidityFacts
    leaf1624LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1624CoverageChecked :
    coverageCheck (innerAD leaf1624Box) leaf1624InnerLog = true := by
  rfl'

private theorem leaf1624InnerLogValid :
    leaf1624InnerLog.Valid 8 (innerAD leaf1624Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1624CoverageChecked

private noncomputable def leaf1624InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1624InputLogOnePlusV_eq :
    leaf1624InputLogOnePlusV = outerEnclosure 24
      (leaf1624Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1624RoundedFacts : LeafRoundedFacts 8
    leaf1624Certificate.logOnePlusV leaf1624InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1624InputLogOnePlusV_eq }

private noncomputable def leaf1624Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1624InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1624LowerChecked :
    lowerCheck 24 leaf1624Box leaf1624Inputs = true := by
  rfl'

private theorem leaf1624CoversExact : CoversExact 8
    leaf1624Box leaf1624Certificate leaf1624InnerLog leaf1624Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1624RoundedFacts (by rfl)

private theorem leaf1624FlatSound : Sound leaf1624Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1624CertificateValid
    leaf1624InnerLogValid leaf1624CoversExact leaf1624LowerChecked

private noncomputable def leaf1625Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1625Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108315) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (299857911/268435456) }, upper := { exponent := 0, mantissa := (4645/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217307/134216630) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1625InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1625LocalValidity :
    LeafFacts leaf1625Box leaf1625Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1625Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108315) }) = true
      norm_num [leaf1625Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1625CertificateValid :
    WideCertificateValid leaf1625Box leaf1625Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi139ValidityFacts
    leaf1625LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1625CoverageChecked :
    coverageCheck (innerAD leaf1625Box) leaf1625InnerLog = true := by
  rfl'

private theorem leaf1625InnerLogValid :
    leaf1625InnerLog.Valid 8 (innerAD leaf1625Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1625CoverageChecked

private noncomputable def leaf1625InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1625InputLogOnePlusV_eq :
    leaf1625InputLogOnePlusV = outerEnclosure 24
      (leaf1625Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1625RoundedFacts : LeafRoundedFacts 8
    leaf1625Certificate.logOnePlusV leaf1625InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1625InputLogOnePlusV_eq }

private noncomputable def leaf1625Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1625InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1625LowerChecked :
    lowerCheck 24 leaf1625Box leaf1625Inputs = true := by
  rfl'

private theorem leaf1625CoversExact : CoversExact 8
    leaf1625Box leaf1625Certificate leaf1625InnerLog leaf1625Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1625RoundedFacts (by rfl)

private theorem leaf1625FlatSound : Sound leaf1625Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1625CertificateValid
    leaf1625InnerLogValid leaf1625CoversExact leaf1625LowerChecked

private noncomputable def leaf1626Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1626Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554153) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (300382165/268435456) }, upper := { exponent := 0, mantissa := (2327/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108649/67108306) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1626InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1626LocalValidity :
    LeafFacts leaf1626Box leaf1626Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1626Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554153) }) = true
      norm_num [leaf1626Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1626CertificateValid :
    WideCertificateValid leaf1626Box leaf1626Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi139ValidityFacts
    leaf1626LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1626CoverageChecked :
    coverageCheck (innerAD leaf1626Box) leaf1626InnerLog = true := by
  rfl'

private theorem leaf1626InnerLogValid :
    leaf1626InnerLog.Valid 8 (innerAD leaf1626Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1626CoverageChecked

private noncomputable def leaf1626InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814583/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1626InputLogOnePlusV_eq :
    leaf1626InputLogOnePlusV = outerEnclosure 24
      (leaf1626Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1626RoundedFacts : LeafRoundedFacts 8
    leaf1626Certificate.logOnePlusV leaf1626InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1626InputLogOnePlusV_eq }

private noncomputable def leaf1626Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1626InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1626LowerChecked :
    lowerCheck 24 leaf1626Box leaf1626Inputs = true := by
  rfl'

private theorem leaf1626CoversExact : CoversExact 8
    leaf1626Box leaf1626Certificate leaf1626InnerLog leaf1626Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1626RoundedFacts (by rfl)

private theorem leaf1626FlatSound : Sound leaf1626Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1626CertificateValid
    leaf1626InnerLogValid leaf1626CoversExact leaf1626LowerChecked

private noncomputable def leaf1627Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1627Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (8191/8192), upper := (11184832/11184709) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (303789829/268435456) }, upper := { exponent := 0, mantissa := (2353/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22369541/22369418) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1627InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1627LocalValidity :
    LeafFacts leaf1627Box leaf1627Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1627Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11184832/11184709) }) = true
      norm_num [leaf1627Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1627CertificateValid :
    WideCertificateValid leaf1627Box leaf1627Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi140ValidityFacts
    leaf1627LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1627CoverageChecked :
    coverageCheck (innerAD leaf1627Box) leaf1627InnerLog = true := by
  rfl'

private theorem leaf1627InnerLogValid :
    leaf1627InnerLog.Valid 8 (innerAD leaf1627Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1627CoverageChecked

private noncomputable def leaf1627InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629173/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1627InputLogOnePlusV_eq :
    leaf1627InputLogOnePlusV = outerEnclosure 24
      (leaf1627Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1627RoundedFacts : LeafRoundedFacts 8
    leaf1627Certificate.logOnePlusV leaf1627InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1627InputLogOnePlusV_eq }

private noncomputable def leaf1627Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi140InputQChi innerPair2Input
    leaf1627InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1627LowerChecked :
    lowerCheck 24 leaf1627Box leaf1627Inputs = true := by
  rfl'

private theorem leaf1627CoversExact : CoversExact 8
    leaf1627Box leaf1627Certificate leaf1627InnerLog leaf1627Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi140RoundedFacts
    innerPair2RoundedFacts leaf1627RoundedFacts (by rfl)

private theorem leaf1627FlatSound : Sound leaf1627Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1627CertificateValid
    leaf1627InnerLogValid leaf1627CoversExact leaf1627LowerChecked

private noncomputable def leaf1628Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1628Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777061) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (304379615/268435456) }, upper := { exponent := 0, mantissa := (1179/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554309/33554122) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1628InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1628LocalValidity :
    LeafFacts leaf1628Box leaf1628Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1628Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777061) }) = true
      norm_num [leaf1628Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1628CertificateValid :
    WideCertificateValid leaf1628Box leaf1628Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi140ValidityFacts
    leaf1628LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1628CoverageChecked :
    coverageCheck (innerAD leaf1628Box) leaf1628InnerLog = true := by
  rfl'

private theorem leaf1628InnerLogValid :
    leaf1628InnerLog.Valid 8 (innerAD leaf1628Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1628CoverageChecked

private noncomputable def leaf1628InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814587/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1628InputLogOnePlusV_eq :
    leaf1628InputLogOnePlusV = outerEnclosure 24
      (leaf1628Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1628RoundedFacts : LeafRoundedFacts 8
    leaf1628Certificate.logOnePlusV leaf1628InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1628InputLogOnePlusV_eq }

private noncomputable def leaf1628Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi140InputQChi innerPair2Input
    leaf1628InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1628LowerChecked :
    lowerCheck 24 leaf1628Box leaf1628Inputs = true := by
  rfl'

private theorem leaf1628CoversExact : CoversExact 8
    leaf1628Box leaf1628Certificate leaf1628InnerLog leaf1628Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi140RoundedFacts
    innerPair2RoundedFacts leaf1628RoundedFacts (by rfl)

private theorem leaf1628FlatSound : Sound leaf1628Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1628CertificateValid
    leaf1628InnerLogValid leaf1628CoversExact leaf1628LowerChecked

private noncomputable def leaf1629Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1629Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108193) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (307721747/268435456) }, upper := { exponent := 0, mantissa := (4767/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217185/134216386) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1629InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1629LocalValidity :
    LeafFacts leaf1629Box leaf1629Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1629Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108193) }) = true
      norm_num [leaf1629Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1629CertificateValid :
    WideCertificateValid leaf1629Box leaf1629Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi143ValidityFacts
    leaf1629LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1629CoverageChecked :
    coverageCheck (innerAD leaf1629Box) leaf1629InnerLog = true := by
  rfl'

private theorem leaf1629InnerLogValid :
    leaf1629InnerLog.Valid 8 (innerAD leaf1629Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1629CoverageChecked

private noncomputable def leaf1629InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1629InputLogOnePlusV_eq :
    leaf1629InputLogOnePlusV = outerEnclosure 24
      (leaf1629Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1629RoundedFacts : LeafRoundedFacts 8
    leaf1629Certificate.logOnePlusV leaf1629InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1629InputLogOnePlusV_eq }

private noncomputable def leaf1629Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1629InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1629LowerChecked :
    lowerCheck 24 leaf1629Box leaf1629Inputs = true := by
  rfl'

private theorem leaf1629CoversExact : CoversExact 8
    leaf1629Box leaf1629Certificate leaf1629InnerLog leaf1629Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1629RoundedFacts (by rfl)

private theorem leaf1629FlatSound : Sound leaf1629Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1629CertificateValid
    leaf1629InnerLogValid leaf1629CoversExact leaf1629LowerChecked

private noncomputable def leaf1630Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1630Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (8191/8192), upper := (11184832/11184697) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (308377065/268435456) }, upper := { exponent := 0, mantissa := (2389/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22369529/22369394) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1630InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1630LocalValidity :
    LeafFacts leaf1630Box leaf1630Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1630Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11184832/11184697) }) = true
      norm_num [leaf1630Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1630CertificateValid :
    WideCertificateValid leaf1630Box leaf1630Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi143ValidityFacts
    leaf1630LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1630CoverageChecked :
    coverageCheck (innerAD leaf1630Box) leaf1630InnerLog = true := by
  rfl'

private theorem leaf1630InnerLogValid :
    leaf1630InnerLog.Valid 8 (innerAD leaf1630Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1630CoverageChecked

private noncomputable def leaf1630InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814591/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1630InputLogOnePlusV_eq :
    leaf1630InputLogOnePlusV = outerEnclosure 24
      (leaf1630Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1630RoundedFacts : LeafRoundedFacts 8
    leaf1630Certificate.logOnePlusV leaf1630InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1630InputLogOnePlusV_eq }

private noncomputable def leaf1630Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1630InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1630LowerChecked :
    lowerCheck 24 leaf1630Box leaf1630Inputs = true := by
  rfl'

private theorem leaf1630CoversExact : CoversExact 8
    leaf1630Box leaf1630Certificate leaf1630InnerLog leaf1630Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1630RoundedFacts (by rfl)

private theorem leaf1630FlatSound : Sound leaf1630Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1630CertificateValid
    leaf1630InnerLogValid leaf1630CoversExact leaf1630LowerChecked

private noncomputable def leaf1631Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1631Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777033) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (311653665/268435456) }, upper := { exponent := 0, mantissa := (1207/1024) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554281/33554066) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1631InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1631LocalValidity :
    LeafFacts leaf1631Box leaf1631Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1631Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777033) }) = true
      norm_num [leaf1631Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1631CertificateValid :
    WideCertificateValid leaf1631Box leaf1631Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi144ValidityFacts
    leaf1631LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1631CoverageChecked :
    coverageCheck (innerAD leaf1631Box) leaf1631InnerLog = true := by
  rfl'

private theorem leaf1631InnerLogValid :
    leaf1631InnerLog.Valid 8 (innerAD leaf1631Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1631CoverageChecked

private noncomputable def leaf1631InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907297/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1631InputLogOnePlusV_eq :
    leaf1631InputLogOnePlusV = outerEnclosure 24
      (leaf1631Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1631RoundedFacts : LeafRoundedFacts 8
    leaf1631Certificate.logOnePlusV leaf1631InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1631InputLogOnePlusV_eq }

private noncomputable def leaf1631Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1631InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1631LowerChecked :
    lowerCheck 24 leaf1631Box leaf1631Inputs = true := by
  rfl'

private theorem leaf1631CoversExact : CoversExact 8
    leaf1631Box leaf1631Certificate leaf1631InnerLog leaf1631Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1631RoundedFacts (by rfl)

private theorem leaf1631FlatSound : Sound leaf1631Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1631CertificateValid
    leaf1631InnerLogValid leaf1631CoversExact leaf1631LowerChecked

private noncomputable def leaf1632Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1632Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388515) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (312374515/268435456) }, upper := { exponent := 0, mantissa := (605/512) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777139/16777030) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1632InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1632LocalValidity :
    LeafFacts leaf1632Box leaf1632Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1632Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388515) }) = true
      norm_num [leaf1632Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1632CertificateValid :
    WideCertificateValid leaf1632Box leaf1632Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi144ValidityFacts
    leaf1632LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1632CoverageChecked :
    coverageCheck (innerAD leaf1632Box) leaf1632InnerLog = true := by
  rfl'

private theorem leaf1632InnerLogValid :
    leaf1632InnerLog.Valid 8 (innerAD leaf1632Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1632CoverageChecked

private noncomputable def leaf1632InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814595/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1632InputLogOnePlusV_eq :
    leaf1632InputLogOnePlusV = outerEnclosure 24
      (leaf1632Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1632RoundedFacts : LeafRoundedFacts 8
    leaf1632Certificate.logOnePlusV leaf1632InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1632InputLogOnePlusV_eq }

private noncomputable def leaf1632Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1632InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1632LowerChecked :
    lowerCheck 24 leaf1632Box leaf1632Inputs = true := by
  rfl'

private theorem leaf1632CoversExact : CoversExact 8
    leaf1632Box leaf1632Certificate leaf1632InnerLog leaf1632Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1632RoundedFacts (by rfl)

private theorem leaf1632FlatSound : Sound leaf1632Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1632CertificateValid
    leaf1632InnerLogValid leaf1632CoversExact leaf1632LowerChecked

private noncomputable def leaf1633Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1633Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108297) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (300906419/268435456) }, upper := { exponent := 0, mantissa := (4663/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217289/134216594) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1633InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1633LocalValidity :
    LeafFacts leaf1633Box leaf1633Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1633Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108297) }) = true
      norm_num [leaf1633Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1633CertificateValid :
    WideCertificateValid leaf1633Box leaf1633Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi139ValidityFacts
    leaf1633LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1633CoverageChecked :
    coverageCheck (innerAD leaf1633Box) leaf1633InnerLog = true := by
  rfl'

private theorem leaf1633InnerLogValid :
    leaf1633InnerLog.Valid 8 (innerAD leaf1633Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1633CoverageChecked

private noncomputable def leaf1633InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726823/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1633InputLogOnePlusV_eq :
    leaf1633InputLogOnePlusV = outerEnclosure 24
      (leaf1633Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1633RoundedFacts : LeafRoundedFacts 8
    leaf1633Certificate.logOnePlusV leaf1633InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1633InputLogOnePlusV_eq }

private noncomputable def leaf1633Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1633InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1633LowerChecked :
    lowerCheck 24 leaf1633Box leaf1633Inputs = true := by
  rfl'

private theorem leaf1633CoversExact : CoversExact 8
    leaf1633Box leaf1633Certificate leaf1633InnerLog leaf1633Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1633RoundedFacts (by rfl)

private theorem leaf1633FlatSound : Sound leaf1633Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1633CertificateValid
    leaf1633InnerLogValid leaf1633CoversExact leaf1633LowerChecked

private noncomputable def leaf1634Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/32), chiHi := (9/256) }

private noncomputable def leaf1634Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65527/65536), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (301430673/268435456) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi139LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1634InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf1634LocalValidity :
    LeafFacts leaf1634Box leaf1634Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1634Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048578/1048567) }) = true
      norm_num [leaf1634Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1634CertificateValid :
    WideCertificateValid leaf1634Box leaf1634Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi139ValidityFacts
    leaf1634LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1634CoverageChecked :
    coverageCheck (innerAD leaf1634Box) leaf1634InnerLog = true := by
  rfl'

private theorem leaf1634InnerLogValid :
    leaf1634InnerLog.Valid 8 (innerAD leaf1634Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf1634CoverageChecked

private noncomputable def leaf1634InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1634InputLogOnePlusV_eq :
    leaf1634InputLogOnePlusV = outerEnclosure 24
      (leaf1634Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1634RoundedFacts : LeafRoundedFacts 8
    leaf1634Certificate.logOnePlusV leaf1634InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1634InputLogOnePlusV_eq }

private noncomputable def leaf1634Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi139InputQChi innerPair6Input
    leaf1634InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1634LowerChecked :
    lowerCheck 24 leaf1634Box leaf1634Inputs = true := by
  rfl'

private theorem leaf1634CoversExact : CoversExact 8
    leaf1634Box leaf1634Certificate leaf1634InnerLog leaf1634Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi139RoundedFacts
    innerPair6RoundedFacts leaf1634RoundedFacts (by rfl)

private theorem leaf1634FlatSound : Sound leaf1634Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1634CertificateValid
    leaf1634InnerLogValid leaf1634CoversExact leaf1634LowerChecked

private noncomputable def leaf1635Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1635Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554117) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (304969401/268435456) }, upper := { exponent := 0, mantissa := (2363/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108613/67108234) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1635InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1635LocalValidity :
    LeafFacts leaf1635Box leaf1635Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1635Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554117) }) = true
      norm_num [leaf1635Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1635CertificateValid :
    WideCertificateValid leaf1635Box leaf1635Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi140ValidityFacts
    leaf1635LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1635CoverageChecked :
    coverageCheck (innerAD leaf1635Box) leaf1635InnerLog = true := by
  rfl'

private theorem leaf1635InnerLogValid :
    leaf1635InnerLog.Valid 8 (innerAD leaf1635Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1635CoverageChecked

private noncomputable def leaf1635InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629175/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1635InputLogOnePlusV_eq :
    leaf1635InputLogOnePlusV = outerEnclosure 24
      (leaf1635Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1635RoundedFacts : LeafRoundedFacts 8
    leaf1635Certificate.logOnePlusV leaf1635InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1635InputLogOnePlusV_eq }

private noncomputable def leaf1635Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi140InputQChi innerPair2Input
    leaf1635InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1635LowerChecked :
    lowerCheck 24 leaf1635Box leaf1635Inputs = true := by
  rfl'

private theorem leaf1635CoversExact : CoversExact 8
    leaf1635Box leaf1635Certificate leaf1635InnerLog leaf1635Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi140RoundedFacts
    innerPair2RoundedFacts leaf1635RoundedFacts (by rfl)

private theorem leaf1635FlatSound : Sound leaf1635Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1635CertificateValid
    leaf1635InnerLogValid leaf1635CoversExact leaf1635LowerChecked

private noncomputable def leaf1636Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/256), chiHi := (5/128) }

private noncomputable def leaf1636Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65527/65536), upper := (174763/174761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (305559187/268435456) }, upper := { exponent := 0, mantissa := (37/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi140LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (174762/174761) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1636InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1636LocalValidity :
    LeafFacts leaf1636Box leaf1636Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1636Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (174763/174761) }) = true
      norm_num [leaf1636Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1636CertificateValid :
    WideCertificateValid leaf1636Box leaf1636Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi140ValidityFacts
    leaf1636LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1636CoverageChecked :
    coverageCheck (innerAD leaf1636Box) leaf1636InnerLog = true := by
  rfl'

private theorem leaf1636InnerLogValid :
    leaf1636InnerLog.Valid 8 (innerAD leaf1636Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1636CoverageChecked

private noncomputable def leaf1636InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629177/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1636InputLogOnePlusV_eq :
    leaf1636InputLogOnePlusV = outerEnclosure 24
      (leaf1636Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1636RoundedFacts : LeafRoundedFacts 8
    leaf1636Certificate.logOnePlusV leaf1636InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1636InputLogOnePlusV_eq }

private noncomputable def leaf1636Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi140InputQChi innerPair2Input
    leaf1636InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1636LowerChecked :
    lowerCheck 24 leaf1636Box leaf1636Inputs = true := by
  rfl'

private theorem leaf1636CoversExact : CoversExact 8
    leaf1636Box leaf1636Certificate leaf1636InnerLog leaf1636Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi140RoundedFacts
    innerPair2RoundedFacts leaf1636RoundedFacts (by rfl)

private theorem leaf1636FlatSound : Sound leaf1636Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1636CertificateValid
    leaf1636InnerLogValid leaf1636CoversExact leaf1636LowerChecked

private noncomputable def leaf1637Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1637Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108171) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (309032383/268435456) }, upper := { exponent := 0, mantissa := (4789/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217163/134216342) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1637InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1637LocalValidity :
    LeafFacts leaf1637Box leaf1637Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1637Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108171) }) = true
      norm_num [leaf1637Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1637CertificateValid :
    WideCertificateValid leaf1637Box leaf1637Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi143ValidityFacts
    leaf1637LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1637CoverageChecked :
    coverageCheck (innerAD leaf1637Box) leaf1637InnerLog = true := by
  rfl'

private theorem leaf1637InnerLogValid :
    leaf1637InnerLog.Valid 8 (innerAD leaf1637Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1637CoverageChecked

private noncomputable def leaf1637InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629183/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1637InputLogOnePlusV_eq :
    leaf1637InputLogOnePlusV = outerEnclosure 24
      (leaf1637Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1637RoundedFacts : LeafRoundedFacts 8
    leaf1637Certificate.logOnePlusV leaf1637InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1637InputLogOnePlusV_eq }

private noncomputable def leaf1637Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1637InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1637LowerChecked :
    lowerCheck 24 leaf1637Box leaf1637Inputs = true := by
  rfl'

private theorem leaf1637CoversExact : CoversExact 8
    leaf1637Box leaf1637Certificate leaf1637InnerLog leaf1637Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1637RoundedFacts (by rfl)

private theorem leaf1637FlatSound : Sound leaf1637Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1637CertificateValid
    leaf1637InnerLogValid leaf1637CoversExact leaf1637LowerChecked

private noncomputable def leaf1638Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/128), chiHi := (11/256) }

private noncomputable def leaf1638Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65527/65536), upper := (1048578/1048565) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (309687701/268435456) }, upper := { exponent := 0, mantissa := (75/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi143LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097143/2097130) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1638InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1638LocalValidity :
    LeafFacts leaf1638Box leaf1638Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1638Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048578/1048565) }) = true
      norm_num [leaf1638Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1638CertificateValid :
    WideCertificateValid leaf1638Box leaf1638Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi143ValidityFacts
    leaf1638LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1638CoverageChecked :
    coverageCheck (innerAD leaf1638Box) leaf1638InnerLog = true := by
  rfl'

private theorem leaf1638InnerLogValid :
    leaf1638InnerLog.Valid 8 (innerAD leaf1638Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1638CoverageChecked

private noncomputable def leaf1638InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1638InputLogOnePlusV_eq :
    leaf1638InputLogOnePlusV = outerEnclosure 24
      (leaf1638Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1638RoundedFacts : LeafRoundedFacts 8
    leaf1638Certificate.logOnePlusV leaf1638InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1638InputLogOnePlusV_eq }

private noncomputable def leaf1638Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi143InputQChi innerPair2Input
    leaf1638InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1638LowerChecked :
    lowerCheck 24 leaf1638Box leaf1638Inputs = true := by
  rfl'

private theorem leaf1638CoversExact : CoversExact 8
    leaf1638Box leaf1638Certificate leaf1638InnerLog leaf1638Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi143RoundedFacts
    innerPair2RoundedFacts leaf1638RoundedFacts (by rfl)

private theorem leaf1638FlatSound : Sound leaf1638Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1638CertificateValid
    leaf1638InnerLogValid leaf1638CoversExact leaf1638LowerChecked

private noncomputable def leaf1639Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1639Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16777027) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (313095365/268435456) }, upper := { exponent := 0, mantissa := (1213/1024) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554275/33554054) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1639InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1639LocalValidity :
    LeafFacts leaf1639Box leaf1639Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1639Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16777027) }) = true
      norm_num [leaf1639Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1639CertificateValid :
    WideCertificateValid leaf1639Box leaf1639Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi144ValidityFacts
    leaf1639LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1639CoverageChecked :
    coverageCheck (innerAD leaf1639Box) leaf1639InnerLog = true := by
  rfl'

private theorem leaf1639InnerLogValid :
    leaf1639InnerLog.Valid 8 (innerAD leaf1639Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1639CoverageChecked

private noncomputable def leaf1639InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629191/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1639InputLogOnePlusV_eq :
    leaf1639InputLogOnePlusV = outerEnclosure 24
      (leaf1639Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1639RoundedFacts : LeafRoundedFacts 8
    leaf1639Certificate.logOnePlusV leaf1639InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1639InputLogOnePlusV_eq }

private noncomputable def leaf1639Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1639InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1639LowerChecked :
    lowerCheck 24 leaf1639Box leaf1639Inputs = true := by
  rfl'

private theorem leaf1639CoversExact : CoversExact 8
    leaf1639Box leaf1639Certificate leaf1639InnerLog leaf1639Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1639RoundedFacts (by rfl)

private theorem leaf1639FlatSound : Sound leaf1639Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1639CertificateValid
    leaf1639InnerLogValid leaf1639CoversExact leaf1639LowerChecked

private noncomputable def leaf1640Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/256), chiHi := (3/64) }

private noncomputable def leaf1640Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (65527/65536), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (313816215/268435456) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi144LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1640InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf1640LocalValidity :
    LeafFacts leaf1640Box leaf1640Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1640Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (524289/524282) }) = true
      norm_num [leaf1640Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1640CertificateValid :
    WideCertificateValid leaf1640Box leaf1640Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi144ValidityFacts
    leaf1640LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1640CoverageChecked :
    coverageCheck (innerAD leaf1640Box) leaf1640InnerLog = true := by
  rfl'

private theorem leaf1640InnerLogValid :
    leaf1640InnerLog.Valid 8 (innerAD leaf1640Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf1640CoverageChecked

private noncomputable def leaf1640InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1640InputLogOnePlusV_eq :
    leaf1640InputLogOnePlusV = outerEnclosure 24
      (leaf1640Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1640RoundedFacts : LeafRoundedFacts 8
    leaf1640Certificate.logOnePlusV leaf1640InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1640InputLogOnePlusV_eq }

private noncomputable def leaf1640Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi144InputQChi innerPair2Input
    leaf1640InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1640LowerChecked :
    lowerCheck 24 leaf1640Box leaf1640Inputs = true := by
  rfl'

private theorem leaf1640CoversExact : CoversExact 8
    leaf1640Box leaf1640Certificate leaf1640InnerLog leaf1640Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi144RoundedFacts
    innerPair2RoundedFacts leaf1640RoundedFacts (by rfl)

private theorem leaf1640FlatSound : Sound leaf1640Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1640CertificateValid
    leaf1640InnerLogValid leaf1640CoversExact leaf1640LowerChecked

private noncomputable def leaf1641Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/64), chiHi := (13/256) }

private noncomputable def leaf1641Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (22369664/22369357) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (315585583/268435456) }, upper := { exponent := 0, mantissa := (4889/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi159LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (44739021/44738714) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1641InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1641LocalValidity :
    LeafFacts leaf1641Box leaf1641Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1641Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22369664/22369357) }) = true
      norm_num [leaf1641Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1641CertificateValid :
    WideCertificateValid leaf1641Box leaf1641Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi159ValidityFacts
    leaf1641LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1641CoverageChecked :
    coverageCheck (innerAD leaf1641Box) leaf1641InnerLog = true := by
  rfl'

private theorem leaf1641InnerLogValid :
    leaf1641InnerLog.Valid 8 (innerAD leaf1641Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1641CoverageChecked

private noncomputable def leaf1641InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907299/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1641InputLogOnePlusV_eq :
    leaf1641InputLogOnePlusV = outerEnclosure 24
      (leaf1641Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1641RoundedFacts : LeafRoundedFacts 8
    leaf1641Certificate.logOnePlusV leaf1641InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1641InputLogOnePlusV_eq }

private noncomputable def leaf1641Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi159InputQChi innerPair3Input
    leaf1641InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1641LowerChecked :
    lowerCheck 24 leaf1641Box leaf1641Inputs = true := by
  rfl'

private theorem leaf1641CoversExact : CoversExact 8
    leaf1641Box leaf1641Certificate leaf1641InnerLog leaf1641Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi159RoundedFacts
    innerPair3RoundedFacts leaf1641RoundedFacts (by rfl)

private theorem leaf1641FlatSound : Sound leaf1641Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1641CertificateValid
    leaf1641InnerLogValid leaf1641CoversExact leaf1641LowerChecked

private noncomputable def leaf1642Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/256), chiHi := (7/128) }

private noncomputable def leaf1642Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554005) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (319517501/268435456) }, upper := { exponent := 0, mantissa := (2475/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi160LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108501/67108010) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1642InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1642LocalValidity :
    LeafFacts leaf1642Box leaf1642Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1642Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554005) }) = true
      norm_num [leaf1642Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1642CertificateValid :
    WideCertificateValid leaf1642Box leaf1642Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi160ValidityFacts
    leaf1642LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1642CoverageChecked :
    coverageCheck (innerAD leaf1642Box) leaf1642InnerLog = true := by
  rfl'

private theorem leaf1642InnerLogValid :
    leaf1642InnerLog.Valid 8 (innerAD leaf1642Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1642CoverageChecked

private noncomputable def leaf1642InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629203/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1642InputLogOnePlusV_eq :
    leaf1642InputLogOnePlusV = outerEnclosure 24
      (leaf1642Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1642RoundedFacts : LeafRoundedFacts 8
    leaf1642Certificate.logOnePlusV leaf1642InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1642InputLogOnePlusV_eq }

private noncomputable def leaf1642Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi160InputQChi innerPair12Input
    leaf1642InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1642LowerChecked :
    lowerCheck 24 leaf1642Box leaf1642Inputs = true := by
  rfl'

private theorem leaf1642CoversExact : CoversExact 8
    leaf1642Box leaf1642Certificate leaf1642InnerLog leaf1642Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi160RoundedFacts
    innerPair12RoundedFacts leaf1642RoundedFacts (by rfl)

private theorem leaf1642FlatSound : Sound leaf1642Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1642CertificateValid
    leaf1642InnerLogValid leaf1642CoversExact leaf1642LowerChecked

private noncomputable def leaf1643Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/64), chiHi := (13/256) }

private noncomputable def leaf1643Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33554029) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (316371965/268435456) }, upper := { exponent := 0, mantissa := (2451/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi159LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108525/67108058) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1643InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1643LocalValidity :
    LeafFacts leaf1643Box leaf1643Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1643Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33554029) }) = true
      norm_num [leaf1643Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1643CertificateValid :
    WideCertificateValid leaf1643Box leaf1643Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi159ValidityFacts
    leaf1643LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1643CoverageChecked :
    coverageCheck (innerAD leaf1643Box) leaf1643InnerLog = true := by
  rfl'

private theorem leaf1643InnerLogValid :
    leaf1643InnerLog.Valid 8 (innerAD leaf1643Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1643CoverageChecked

private noncomputable def leaf1643InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629197/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1643InputLogOnePlusV_eq :
    leaf1643InputLogOnePlusV = outerEnclosure 24
      (leaf1643Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1643RoundedFacts : LeafRoundedFacts 8
    leaf1643Certificate.logOnePlusV leaf1643InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1643InputLogOnePlusV_eq }

private noncomputable def leaf1643Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi159InputQChi innerPair3Input
    leaf1643InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1643LowerChecked :
    lowerCheck 24 leaf1643Box leaf1643Inputs = true := by
  rfl'

private theorem leaf1643CoversExact : CoversExact 8
    leaf1643Box leaf1643Certificate leaf1643InnerLog leaf1643Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi159RoundedFacts
    innerPair3RoundedFacts leaf1643RoundedFacts (by rfl)

private theorem leaf1643FlatSound : Sound leaf1643Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1643CertificateValid
    leaf1643InnerLogValid leaf1643CoversExact leaf1643LowerChecked

private noncomputable def leaf1644Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/256), chiHi := (7/128) }

private noncomputable def leaf1644Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (5592416/5592333) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (320369415/268435456) }, upper := { exponent := 0, mantissa := (1241/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi160LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11184749/11184666) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1644InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1644LocalValidity :
    LeafFacts leaf1644Box leaf1644Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1644Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5592416/5592333) }) = true
      norm_num [leaf1644Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1644CertificateValid :
    WideCertificateValid leaf1644Box leaf1644Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi160ValidityFacts
    leaf1644LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1644CoverageChecked :
    coverageCheck (innerAD leaf1644Box) leaf1644InnerLog = true := by
  rfl'

private theorem leaf1644InnerLogValid :
    leaf1644InnerLog.Valid 8 (innerAD leaf1644Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1644CoverageChecked

private noncomputable def leaf1644InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1644InputLogOnePlusV_eq :
    leaf1644InputLogOnePlusV = outerEnclosure 24
      (leaf1644Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1644RoundedFacts : LeafRoundedFacts 8
    leaf1644Certificate.logOnePlusV leaf1644InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1644InputLogOnePlusV_eq }

private noncomputable def leaf1644Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi160InputQChi innerPair12Input
    leaf1644InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1644LowerChecked :
    lowerCheck 24 leaf1644Box leaf1644Inputs = true := by
  rfl'

private theorem leaf1644CoversExact : CoversExact 8
    leaf1644Box leaf1644Certificate leaf1644InnerLog leaf1644Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi160RoundedFacts
    innerPair12RoundedFacts leaf1644RoundedFacts (by rfl)

private theorem leaf1644FlatSound : Sound leaf1644Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1644CertificateValid
    leaf1644InnerLogValid leaf1644CoversExact leaf1644LowerChecked

private noncomputable def leaf1645Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1645Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67107949) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (323449419/268435456) }, upper := { exponent := 0, mantissa := (5011/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216941/134215898) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1645InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1645LocalValidity :
    LeafFacts leaf1645Box leaf1645Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1645Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67107949) }) = true
      norm_num [leaf1645Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1645CertificateValid :
    WideCertificateValid leaf1645Box leaf1645Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi145ValidityFacts
    leaf1645LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1645CoverageChecked :
    coverageCheck (innerAD leaf1645Box) leaf1645InnerLog = true := by
  rfl'

private theorem leaf1645InnerLogValid :
    leaf1645InnerLog.Valid 8 (innerAD leaf1645Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1645CoverageChecked

private noncomputable def leaf1645InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1645InputLogOnePlusV_eq :
    leaf1645InputLogOnePlusV = outerEnclosure 24
      (leaf1645Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1645RoundedFacts : LeafRoundedFacts 8
    leaf1645Certificate.logOnePlusV leaf1645InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1645InputLogOnePlusV_eq }

private noncomputable def leaf1645Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1645InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1645LowerChecked :
    lowerCheck 24 leaf1645Box leaf1645Inputs = true := by
  rfl'

private theorem leaf1645CoversExact : CoversExact 8
    leaf1645Box leaf1645Certificate leaf1645InnerLog leaf1645Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1645RoundedFacts (by rfl)

private theorem leaf1645FlatSound : Sound leaf1645Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1645CertificateValid
    leaf1645InnerLogValid leaf1645CoversExact leaf1645LowerChecked

private noncomputable def leaf1646Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1646Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (8191/8192), upper := (1398104/1398081) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (327381337/268435456) }, upper := { exponent := 0, mantissa := (317/256) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2796185/2796162) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1646InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1646LocalValidity :
    LeafFacts leaf1646Box leaf1646Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1646Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1398104/1398081) }) = true
      norm_num [leaf1646Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1646CertificateValid :
    WideCertificateValid leaf1646Box leaf1646Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi146ValidityFacts
    leaf1646LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1646CoverageChecked :
    coverageCheck (innerAD leaf1646Box) leaf1646InnerLog = true := by
  rfl'

private theorem leaf1646InnerLogValid :
    leaf1646InnerLog.Valid 8 (innerAD leaf1646Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1646CoverageChecked

private noncomputable def leaf1646InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1646InputLogOnePlusV_eq :
    leaf1646InputLogOnePlusV = outerEnclosure 24
      (leaf1646Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1646RoundedFacts : LeafRoundedFacts 8
    leaf1646Certificate.logOnePlusV leaf1646InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1646InputLogOnePlusV_eq }

private noncomputable def leaf1646Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1646InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1646LowerChecked :
    lowerCheck 24 leaf1646Box leaf1646Inputs = true := by
  rfl'

private theorem leaf1646CoversExact : CoversExact 8
    leaf1646Box leaf1646Certificate leaf1646InnerLog leaf1646Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1646RoundedFacts (by rfl)

private theorem leaf1646FlatSound : Sound leaf1646Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1646CertificateValid
    leaf1646InnerLogValid leaf1646CoversExact leaf1646LowerChecked

private noncomputable def leaf1647Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1647Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33553967) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (324366865/268435456) }, upper := { exponent := 0, mantissa := (2513/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108463/67107934) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1647InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1647LocalValidity :
    LeafFacts leaf1647Box leaf1647Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1647Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33553967) }) = true
      norm_num [leaf1647Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1647CertificateValid :
    WideCertificateValid leaf1647Box leaf1647Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi145ValidityFacts
    leaf1647LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1647CoverageChecked :
    coverageCheck (innerAD leaf1647Box) leaf1647InnerLog = true := by
  rfl'

private theorem leaf1647InnerLogValid :
    leaf1647InnerLog.Valid 8 (innerAD leaf1647Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1647CoverageChecked

private noncomputable def leaf1647InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1647InputLogOnePlusV_eq :
    leaf1647InputLogOnePlusV = outerEnclosure 24
      (leaf1647Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1647RoundedFacts : LeafRoundedFacts 8
    leaf1647Certificate.logOnePlusV leaf1647InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1647InputLogOnePlusV_eq }

private noncomputable def leaf1647Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1647InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1647LowerChecked :
    lowerCheck 24 leaf1647Box leaf1647Inputs = true := by
  rfl'

private theorem leaf1647CoversExact : CoversExact 8
    leaf1647Box leaf1647Certificate leaf1647InnerLog leaf1647Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1647RoundedFacts (by rfl)

private theorem leaf1647FlatSound : Sound leaf1647Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1647CertificateValid
    leaf1647InnerLogValid leaf1647CoversExact leaf1647LowerChecked

private noncomputable def leaf1648Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1648Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435611/268435456) }, vSqrt := { lower := (8191/8192), upper := (2097156/2097121) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (328364315/268435456) }, upper := { exponent := 0, mantissa := (159/128) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4194277/4194242) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1648InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1648LocalValidity :
    LeafFacts leaf1648Box leaf1648Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1648Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2097156/2097121) }) = true
      norm_num [leaf1648Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1648CertificateValid :
    WideCertificateValid leaf1648Box leaf1648Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi146ValidityFacts
    leaf1648LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1648CoverageChecked :
    coverageCheck (innerAD leaf1648Box) leaf1648InnerLog = true := by
  rfl'

private theorem leaf1648InnerLogValid :
    leaf1648InnerLog.Valid 8 (innerAD leaf1648Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1648CoverageChecked

private noncomputable def leaf1648InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1648InputLogOnePlusV_eq :
    leaf1648InputLogOnePlusV = outerEnclosure 24
      (leaf1648Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1648RoundedFacts : LeafRoundedFacts 8
    leaf1648Certificate.logOnePlusV leaf1648InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1648InputLogOnePlusV_eq }

private noncomputable def leaf1648Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1648InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1648LowerChecked :
    lowerCheck 24 leaf1648Box leaf1648Inputs = true := by
  rfl'

private theorem leaf1648CoversExact : CoversExact 8
    leaf1648Box leaf1648Certificate leaf1648InnerLog leaf1648Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1648RoundedFacts (by rfl)

private theorem leaf1648FlatSound : Sound leaf1648Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1648CertificateValid
    leaf1648InnerLogValid leaf1648CoversExact leaf1648LowerChecked

private noncomputable def leaf1649Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/64), chiHi := (13/256) }

private noncomputable def leaf1649Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67108045) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (317158347/268435456) }, upper := { exponent := 0, mantissa := (4915/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi159LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134217037/134216090) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1649InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1649LocalValidity :
    LeafFacts leaf1649Box leaf1649Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1649Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67108045) }) = true
      norm_num [leaf1649Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1649CertificateValid :
    WideCertificateValid leaf1649Box leaf1649Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi159ValidityFacts
    leaf1649LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1649CoverageChecked :
    coverageCheck (innerAD leaf1649Box) leaf1649InnerLog = true := by
  rfl'

private theorem leaf1649InnerLogValid :
    leaf1649InnerLog.Valid 8 (innerAD leaf1649Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1649CoverageChecked

private noncomputable def leaf1649InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629199/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1649InputLogOnePlusV_eq :
    leaf1649InputLogOnePlusV = outerEnclosure 24
      (leaf1649Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1649RoundedFacts : LeafRoundedFacts 8
    leaf1649Certificate.logOnePlusV leaf1649InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1649InputLogOnePlusV_eq }

private noncomputable def leaf1649Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi159InputQChi innerPair3Input
    leaf1649InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1649LowerChecked :
    lowerCheck 24 leaf1649Box leaf1649Inputs = true := by
  rfl'

private theorem leaf1649CoversExact : CoversExact 8
    leaf1649Box leaf1649Certificate leaf1649InnerLog leaf1649Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi159RoundedFacts
    innerPair3RoundedFacts leaf1649RoundedFacts (by rfl)

private theorem leaf1649FlatSound : Sound leaf1649Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1649CertificateValid
    leaf1649InnerLogValid leaf1649CoversExact leaf1649LowerChecked

private noncomputable def leaf1650Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/64), chiHi := (13/256) }

private noncomputable def leaf1650Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (65527/65536), upper := (349526/349521) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (317944729/268435456) }, upper := { exponent := 0, mantissa := (77/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi159LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (699047/699042) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1650InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1650LocalValidity :
    LeafFacts leaf1650Box leaf1650Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1650Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (349526/349521) }) = true
      norm_num [leaf1650Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1650CertificateValid :
    WideCertificateValid leaf1650Box leaf1650Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi159ValidityFacts
    leaf1650LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1650CoverageChecked :
    coverageCheck (innerAD leaf1650Box) leaf1650InnerLog = true := by
  rfl'

private theorem leaf1650InnerLogValid :
    leaf1650InnerLog.Valid 8 (innerAD leaf1650Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1650CoverageChecked

private noncomputable def leaf1650InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629201/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1650InputLogOnePlusV_eq :
    leaf1650InputLogOnePlusV = outerEnclosure 24
      (leaf1650Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1650RoundedFacts : LeafRoundedFacts 8
    leaf1650Certificate.logOnePlusV leaf1650InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1650InputLogOnePlusV_eq }

private noncomputable def leaf1650Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi159InputQChi innerPair3Input
    leaf1650InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1650LowerChecked :
    lowerCheck 24 leaf1650Box leaf1650Inputs = true := by
  rfl'

private theorem leaf1650CoversExact : CoversExact 8
    leaf1650Box leaf1650Certificate leaf1650InnerLog leaf1650Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi159RoundedFacts
    innerPair3RoundedFacts leaf1650RoundedFacts (by rfl)

private theorem leaf1650FlatSound : Sound leaf1650Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1650CertificateValid
    leaf1650InnerLogValid leaf1650CoversExact leaf1650LowerChecked

private noncomputable def leaf1651Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/256), chiHi := (7/128) }

private noncomputable def leaf1651Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33553991) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (321221329/268435456) }, upper := { exponent := 0, mantissa := (2489/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi160LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108487/67107982) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1651InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1651LocalValidity :
    LeafFacts leaf1651Box leaf1651Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1651Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33553991) }) = true
      norm_num [leaf1651Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1651CertificateValid :
    WideCertificateValid leaf1651Box leaf1651Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi160ValidityFacts
    leaf1651LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1651CoverageChecked :
    coverageCheck (innerAD leaf1651Box) leaf1651InnerLog = true := by
  rfl'

private theorem leaf1651InnerLogValid :
    leaf1651InnerLog.Valid 8 (innerAD leaf1651Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1651CoverageChecked

private noncomputable def leaf1651InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1651InputLogOnePlusV_eq :
    leaf1651InputLogOnePlusV = outerEnclosure 24
      (leaf1651Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1651RoundedFacts : LeafRoundedFacts 8
    leaf1651Certificate.logOnePlusV leaf1651InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1651InputLogOnePlusV_eq }

private noncomputable def leaf1651Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi160InputQChi innerPair12Input
    leaf1651InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1651LowerChecked :
    lowerCheck 24 leaf1651Box leaf1651Inputs = true := by
  rfl'

private theorem leaf1651CoversExact : CoversExact 8
    leaf1651Box leaf1651Certificate leaf1651InnerLog leaf1651Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi160RoundedFacts
    innerPair12RoundedFacts leaf1651RoundedFacts (by rfl)

private theorem leaf1651FlatSound : Sound leaf1651Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1651CertificateValid
    leaf1651InnerLogValid leaf1651CoversExact leaf1651LowerChecked

private noncomputable def leaf1652Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/256), chiHi := (7/128) }

private noncomputable def leaf1652Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435611/268435456) }, vSqrt := { lower := (65527/65536), upper := (524289/524281) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (322073243/268435456) }, upper := { exponent := 0, mantissa := (39/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi160LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (524285/524281) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1652InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1652LocalValidity :
    LeafFacts leaf1652Box leaf1652Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1652Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (524289/524281) }) = true
      norm_num [leaf1652Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1652CertificateValid :
    WideCertificateValid leaf1652Box leaf1652Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi160ValidityFacts
    leaf1652LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1652CoverageChecked :
    coverageCheck (innerAD leaf1652Box) leaf1652InnerLog = true := by
  rfl'

private theorem leaf1652InnerLogValid :
    leaf1652InnerLog.Valid 8 (innerAD leaf1652Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1652CoverageChecked

private noncomputable def leaf1652InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1652InputLogOnePlusV_eq :
    leaf1652InputLogOnePlusV = outerEnclosure 24
      (leaf1652Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1652RoundedFacts : LeafRoundedFacts 8
    leaf1652Certificate.logOnePlusV leaf1652InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1652InputLogOnePlusV_eq }

private noncomputable def leaf1652Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi160InputQChi innerPair12Input
    leaf1652InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1652LowerChecked :
    lowerCheck 24 leaf1652Box leaf1652Inputs = true := by
  rfl'

private theorem leaf1652CoversExact : CoversExact 8
    leaf1652Box leaf1652Certificate leaf1652InnerLog leaf1652Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi160RoundedFacts
    innerPair12RoundedFacts leaf1652RoundedFacts (by rfl)

private theorem leaf1652FlatSound : Sound leaf1652Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1652CertificateValid
    leaf1652InnerLogValid leaf1652CoversExact leaf1652LowerChecked

private noncomputable def leaf1653Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1653Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435611/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67107919) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (325284311/268435456) }, upper := { exponent := 0, mantissa := (5041/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216911/134215838) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1653InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1653LocalValidity :
    LeafFacts leaf1653Box leaf1653Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1653Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67107919) }) = true
      norm_num [leaf1653Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1653CertificateValid :
    WideCertificateValid leaf1653Box leaf1653Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi145ValidityFacts
    leaf1653LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1653CoverageChecked :
    coverageCheck (innerAD leaf1653Box) leaf1653InnerLog = true := by
  rfl'

private theorem leaf1653InnerLogValid :
    leaf1653InnerLog.Valid 8 (innerAD leaf1653Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1653CoverageChecked

private noncomputable def leaf1653InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1653InputLogOnePlusV_eq :
    leaf1653InputLogOnePlusV = outerEnclosure 24
      (leaf1653Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1653RoundedFacts : LeafRoundedFacts 8
    leaf1653Certificate.logOnePlusV leaf1653InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1653InputLogOnePlusV_eq }

private noncomputable def leaf1653Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1653InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1653LowerChecked :
    lowerCheck 24 leaf1653Box leaf1653Inputs = true := by
  rfl'

private theorem leaf1653CoversExact : CoversExact 8
    leaf1653Box leaf1653Certificate leaf1653InnerLog leaf1653Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1653RoundedFacts (by rfl)

private theorem leaf1653FlatSound : Sound leaf1653Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1653CertificateValid
    leaf1653InnerLogValid leaf1653CoversExact leaf1653LowerChecked

private noncomputable def leaf1654Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1654Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435613/268435456) }, vSqrt := { lower := (8191/8192), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (329347293/268435456) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1654InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1654LocalValidity :
    LeafFacts leaf1654Box leaf1654Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1654Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194312/4194241) }) = true
      norm_num [leaf1654Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1654CertificateValid :
    WideCertificateValid leaf1654Box leaf1654Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi146ValidityFacts
    leaf1654LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1654CoverageChecked :
    coverageCheck (innerAD leaf1654Box) leaf1654InnerLog = true := by
  rfl'

private theorem leaf1654InnerLogValid :
    leaf1654InnerLog.Valid 8 (innerAD leaf1654Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1654CoverageChecked

private noncomputable def leaf1654InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1654InputLogOnePlusV_eq :
    leaf1654InputLogOnePlusV = outerEnclosure 24
      (leaf1654Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1654RoundedFacts : LeafRoundedFacts 8
    leaf1654Certificate.logOnePlusV leaf1654InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1654InputLogOnePlusV_eq }

private noncomputable def leaf1654Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1654InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1654LowerChecked :
    lowerCheck 24 leaf1654Box leaf1654Inputs = true := by
  rfl'

private theorem leaf1654CoversExact : CoversExact 8
    leaf1654Box leaf1654Certificate leaf1654InnerLog leaf1654Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1654RoundedFacts (by rfl)

private theorem leaf1654FlatSound : Sound leaf1654Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1654CertificateValid
    leaf1654InnerLogValid leaf1654CoversExact leaf1654LowerChecked

private noncomputable def leaf1655Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/128), chiHi := (15/256) }

private noncomputable def leaf1655Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435613/268435456) }, vSqrt := { lower := (65527/65536), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (326201757/268435456) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi145LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1655InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1655LocalValidity :
    LeafFacts leaf1655Box leaf1655Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1655Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048578/1048561) }) = true
      norm_num [leaf1655Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1655CertificateValid :
    WideCertificateValid leaf1655Box leaf1655Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi145ValidityFacts
    leaf1655LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1655CoverageChecked :
    coverageCheck (innerAD leaf1655Box) leaf1655InnerLog = true := by
  rfl'

private theorem leaf1655InnerLogValid :
    leaf1655InnerLog.Valid 8 (innerAD leaf1655Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1655CoverageChecked

private noncomputable def leaf1655InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1655InputLogOnePlusV_eq :
    leaf1655InputLogOnePlusV = outerEnclosure 24
      (leaf1655Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1655RoundedFacts : LeafRoundedFacts 8
    leaf1655Certificate.logOnePlusV leaf1655InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1655InputLogOnePlusV_eq }

private noncomputable def leaf1655Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi145InputQChi innerPair12Input
    leaf1655InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1655LowerChecked :
    lowerCheck 24 leaf1655Box leaf1655Inputs = true := by
  rfl'

private theorem leaf1655CoversExact : CoversExact 8
    leaf1655Box leaf1655Certificate leaf1655InnerLog leaf1655Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi145RoundedFacts
    innerPair12RoundedFacts leaf1655RoundedFacts (by rfl)

private theorem leaf1655FlatSound : Sound leaf1655Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1655CertificateValid
    leaf1655InnerLogValid leaf1655CoversExact leaf1655LowerChecked

private noncomputable def leaf1656Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/256), chiHi := (1/16) }

private noncomputable def leaf1656Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435615/268435456) }, vSqrt := { lower := (65527/65536), upper := (174763/174760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (330330271/268435456) }, upper := { exponent := 0, mantissa := (5/4) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi146LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (349523/349520) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1656InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1656LocalValidity :
    LeafFacts leaf1656Box leaf1656Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1656Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (174763/174760) }) = true
      norm_num [leaf1656Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1656CertificateValid :
    WideCertificateValid leaf1656Box leaf1656Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi146ValidityFacts
    leaf1656LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1656CoverageChecked :
    coverageCheck (innerAD leaf1656Box) leaf1656InnerLog = true := by
  rfl'

private theorem leaf1656InnerLogValid :
    leaf1656InnerLog.Valid 8 (innerAD leaf1656Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1656CoverageChecked

private noncomputable def leaf1656InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1656InputLogOnePlusV_eq :
    leaf1656InputLogOnePlusV = outerEnclosure 24
      (leaf1656Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1656RoundedFacts : LeafRoundedFacts 8
    leaf1656Certificate.logOnePlusV leaf1656InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1656InputLogOnePlusV_eq }

private noncomputable def leaf1656Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi146InputQChi innerPair12Input
    leaf1656InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1656LowerChecked :
    lowerCheck 24 leaf1656Box leaf1656Inputs = true := by
  rfl'

private theorem leaf1656CoversExact : CoversExact 8
    leaf1656Box leaf1656Certificate leaf1656InnerLog leaf1656Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi146RoundedFacts
    innerPair12RoundedFacts leaf1656RoundedFacts (by rfl)

private theorem leaf1656FlatSound : Sound leaf1656Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1656CertificateValid
    leaf1656InnerLogValid leaf1656CoversExact leaf1656LowerChecked

private noncomputable def component37Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/32), chiHi := (9/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node0_sound : Sound component37Node0Box :=
  sound_of_literal_split component37Node0Box leaf1596Box leaf1597Box
    .k (57/16) (by rfl) (by rfl)
    leaf1596FlatSound leaf1597FlatSound

private noncomputable def component37Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node1_sound : Sound component37Node1Box :=
  sound_of_literal_split component37Node1Box leaf1598Box leaf1599Box
    .k (57/16) (by rfl) (by rfl)
    leaf1598FlatSound leaf1599FlatSound

private noncomputable def component37Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node2_sound : Sound component37Node2Box :=
  sound_of_literal_split component37Node2Box component37Node0Box component37Node1Box
    .chi (9/256) (by rfl) (by rfl)
    component37Node0_sound component37Node1_sound

private noncomputable def component37Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/128), chiHi := (11/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node3_sound : Sound component37Node3Box :=
  sound_of_literal_split component37Node3Box leaf1600Box leaf1601Box
    .k (57/16) (by rfl) (by rfl)
    leaf1600FlatSound leaf1601FlatSound

private noncomputable def component37Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/256), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node4_sound : Sound component37Node4Box :=
  sound_of_literal_split component37Node4Box leaf1602Box leaf1603Box
    .k (57/16) (by rfl) (by rfl)
    leaf1602FlatSound leaf1603FlatSound

private noncomputable def component37Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node5_sound : Sound component37Node5Box :=
  sound_of_literal_split component37Node5Box component37Node3Box component37Node4Box
    .chi (11/256) (by rfl) (by rfl)
    component37Node3_sound component37Node4_sound

private noncomputable def component37Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node6_sound : Sound component37Node6Box :=
  sound_of_literal_split component37Node6Box component37Node2Box component37Node5Box
    .chi (5/128) (by rfl) (by rfl)
    component37Node2_sound component37Node5_sound

private noncomputable def component37Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/32), chiHi := (9/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node7_sound : Sound component37Node7Box :=
  sound_of_literal_split component37Node7Box leaf1604Box leaf1605Box
    .k (59/16) (by rfl) (by rfl)
    leaf1604FlatSound leaf1605FlatSound

private noncomputable def component37Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node8_sound : Sound component37Node8Box :=
  sound_of_literal_split component37Node8Box leaf1606Box leaf1607Box
    .k (59/16) (by rfl) (by rfl)
    leaf1606FlatSound leaf1607FlatSound

private noncomputable def component37Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node9_sound : Sound component37Node9Box :=
  sound_of_literal_split component37Node9Box component37Node7Box component37Node8Box
    .chi (9/256) (by rfl) (by rfl)
    component37Node7_sound component37Node8_sound

private noncomputable def component37Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/128), chiHi := (11/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node10_sound : Sound component37Node10Box :=
  sound_of_literal_split component37Node10Box leaf1608Box leaf1609Box
    .k (59/16) (by rfl) (by rfl)
    leaf1608FlatSound leaf1609FlatSound

private noncomputable def component37Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/256), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node11_sound : Sound component37Node11Box :=
  sound_of_literal_split component37Node11Box leaf1610Box leaf1611Box
    .k (59/16) (by rfl) (by rfl)
    leaf1610FlatSound leaf1611FlatSound

private noncomputable def component37Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node12_sound : Sound component37Node12Box :=
  sound_of_literal_split component37Node12Box component37Node10Box component37Node11Box
    .chi (11/256) (by rfl) (by rfl)
    component37Node10_sound component37Node11_sound

private noncomputable def component37Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node13_sound : Sound component37Node13Box :=
  sound_of_literal_split component37Node13Box component37Node9Box component37Node12Box
    .chi (5/128) (by rfl) (by rfl)
    component37Node9_sound component37Node12_sound

private noncomputable def component37Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node14_sound : Sound component37Node14Box :=
  sound_of_literal_split component37Node14Box component37Node6Box component37Node13Box
    .k (29/8) (by rfl) (by rfl)
    component37Node6_sound component37Node13_sound

private noncomputable def component37Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node15_sound : Sound component37Node15Box :=
  sound_of_literal_split component37Node15Box leaf1612Box leaf1613Box
    .k (57/16) (by rfl) (by rfl)
    leaf1612FlatSound leaf1613FlatSound

private noncomputable def component37Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node16_sound : Sound component37Node16Box :=
  sound_of_literal_split component37Node16Box leaf1614Box leaf1615Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1614FlatSound leaf1615FlatSound

private noncomputable def component37Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node17_sound : Sound component37Node17Box :=
  sound_of_literal_split component37Node17Box leaf1616Box leaf1617Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1616FlatSound leaf1617FlatSound

private noncomputable def component37Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node18_sound : Sound component37Node18Box :=
  sound_of_literal_split component37Node18Box component37Node16Box component37Node17Box
    .k (57/16) (by rfl) (by rfl)
    component37Node16_sound component37Node17_sound

private noncomputable def component37Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node19_sound : Sound component37Node19Box :=
  sound_of_literal_split component37Node19Box component37Node15Box component37Node18Box
    .chi (7/128) (by rfl) (by rfl)
    component37Node15_sound component37Node18_sound

private noncomputable def component37Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node20_sound : Sound component37Node20Box :=
  sound_of_literal_split component37Node20Box leaf1619Box leaf1620Box
    .chi (13/256) (by rfl) (by rfl)
    leaf1619FlatSound leaf1620FlatSound

private noncomputable def component37Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node21_sound : Sound component37Node21Box :=
  sound_of_literal_split component37Node21Box leaf1618Box component37Node20Box
    .k (59/16) (by rfl) (by rfl)
    leaf1618FlatSound component37Node20_sound

private noncomputable def component37Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node22_sound : Sound component37Node22Box :=
  sound_of_literal_split component37Node22Box leaf1621Box leaf1622Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1621FlatSound leaf1622FlatSound

private noncomputable def component37Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node23_sound : Sound component37Node23Box :=
  sound_of_literal_split component37Node23Box leaf1623Box leaf1624Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1623FlatSound leaf1624FlatSound

private noncomputable def component37Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node24_sound : Sound component37Node24Box :=
  sound_of_literal_split component37Node24Box component37Node22Box component37Node23Box
    .k (59/16) (by rfl) (by rfl)
    component37Node22_sound component37Node23_sound

private noncomputable def component37Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node25_sound : Sound component37Node25Box :=
  sound_of_literal_split component37Node25Box component37Node21Box component37Node24Box
    .chi (7/128) (by rfl) (by rfl)
    component37Node21_sound component37Node24_sound

private noncomputable def component37Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node26_sound : Sound component37Node26Box :=
  sound_of_literal_split component37Node26Box component37Node19Box component37Node25Box
    .k (29/8) (by rfl) (by rfl)
    component37Node19_sound component37Node25_sound

private noncomputable def component37Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node27_sound : Sound component37Node27Box :=
  sound_of_literal_split component37Node27Box component37Node14Box component37Node26Box
    .chi (3/64) (by rfl) (by rfl)
    component37Node14_sound component37Node26_sound

private noncomputable def component37Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/32), chiHi := (9/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node28_sound : Sound component37Node28Box :=
  sound_of_literal_split component37Node28Box leaf1625Box leaf1626Box
    .k (61/16) (by rfl) (by rfl)
    leaf1625FlatSound leaf1626FlatSound

private noncomputable def component37Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node29_sound : Sound component37Node29Box :=
  sound_of_literal_split component37Node29Box leaf1627Box leaf1628Box
    .k (61/16) (by rfl) (by rfl)
    leaf1627FlatSound leaf1628FlatSound

private noncomputable def component37Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node30_sound : Sound component37Node30Box :=
  sound_of_literal_split component37Node30Box component37Node28Box component37Node29Box
    .chi (9/256) (by rfl) (by rfl)
    component37Node28_sound component37Node29_sound

private noncomputable def component37Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/128), chiHi := (11/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node31_sound : Sound component37Node31Box :=
  sound_of_literal_split component37Node31Box leaf1629Box leaf1630Box
    .k (61/16) (by rfl) (by rfl)
    leaf1629FlatSound leaf1630FlatSound

private noncomputable def component37Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (11/256), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node32_sound : Sound component37Node32Box :=
  sound_of_literal_split component37Node32Box leaf1631Box leaf1632Box
    .k (61/16) (by rfl) (by rfl)
    leaf1631FlatSound leaf1632FlatSound

private noncomputable def component37Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node33_sound : Sound component37Node33Box :=
  sound_of_literal_split component37Node33Box component37Node31Box component37Node32Box
    .chi (11/256) (by rfl) (by rfl)
    component37Node31_sound component37Node32_sound

private noncomputable def component37Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node34_sound : Sound component37Node34Box :=
  sound_of_literal_split component37Node34Box component37Node30Box component37Node33Box
    .chi (5/128) (by rfl) (by rfl)
    component37Node30_sound component37Node33_sound

private noncomputable def component37Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/32), chiHi := (9/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node35_sound : Sound component37Node35Box :=
  sound_of_literal_split component37Node35Box leaf1633Box leaf1634Box
    .k (63/16) (by rfl) (by rfl)
    leaf1633FlatSound leaf1634FlatSound

private noncomputable def component37Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (9/256), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node36_sound : Sound component37Node36Box :=
  sound_of_literal_split component37Node36Box leaf1635Box leaf1636Box
    .k (63/16) (by rfl) (by rfl)
    leaf1635FlatSound leaf1636FlatSound

private noncomputable def component37Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node37_sound : Sound component37Node37Box :=
  sound_of_literal_split component37Node37Box component37Node35Box component37Node36Box
    .chi (9/256) (by rfl) (by rfl)
    component37Node35_sound component37Node36_sound

private noncomputable def component37Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/128), chiHi := (11/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node38_sound : Sound component37Node38Box :=
  sound_of_literal_split component37Node38Box leaf1637Box leaf1638Box
    .k (63/16) (by rfl) (by rfl)
    leaf1637FlatSound leaf1638FlatSound

private noncomputable def component37Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (11/256), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node39_sound : Sound component37Node39Box :=
  sound_of_literal_split component37Node39Box leaf1639Box leaf1640Box
    .k (63/16) (by rfl) (by rfl)
    leaf1639FlatSound leaf1640FlatSound

private noncomputable def component37Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node40_sound : Sound component37Node40Box :=
  sound_of_literal_split component37Node40Box component37Node38Box component37Node39Box
    .chi (11/256) (by rfl) (by rfl)
    component37Node38_sound component37Node39_sound

private noncomputable def component37Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node41_sound : Sound component37Node41Box :=
  sound_of_literal_split component37Node41Box component37Node37Box component37Node40Box
    .chi (5/128) (by rfl) (by rfl)
    component37Node37_sound component37Node40_sound

private noncomputable def component37Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component37Node42_sound : Sound component37Node42Box :=
  sound_of_literal_split component37Node42Box component37Node34Box component37Node41Box
    .k (31/8) (by rfl) (by rfl)
    component37Node34_sound component37Node41_sound

private noncomputable def component37Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node43_sound : Sound component37Node43Box :=
  sound_of_literal_split component37Node43Box leaf1641Box leaf1642Box
    .chi (13/256) (by rfl) (by rfl)
    leaf1641FlatSound leaf1642FlatSound

private noncomputable def component37Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node44_sound : Sound component37Node44Box :=
  sound_of_literal_split component37Node44Box leaf1643Box leaf1644Box
    .chi (13/256) (by rfl) (by rfl)
    leaf1643FlatSound leaf1644FlatSound

private noncomputable def component37Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node45_sound : Sound component37Node45Box :=
  sound_of_literal_split component37Node45Box component37Node43Box component37Node44Box
    .k (61/16) (by rfl) (by rfl)
    component37Node43_sound component37Node44_sound

private noncomputable def component37Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node46_sound : Sound component37Node46Box :=
  sound_of_literal_split component37Node46Box leaf1645Box leaf1646Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1645FlatSound leaf1646FlatSound

private noncomputable def component37Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node47_sound : Sound component37Node47Box :=
  sound_of_literal_split component37Node47Box leaf1647Box leaf1648Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1647FlatSound leaf1648FlatSound

private noncomputable def component37Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node48_sound : Sound component37Node48Box :=
  sound_of_literal_split component37Node48Box component37Node46Box component37Node47Box
    .k (61/16) (by rfl) (by rfl)
    component37Node46_sound component37Node47_sound

private noncomputable def component37Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node49_sound : Sound component37Node49Box :=
  sound_of_literal_split component37Node49Box component37Node45Box component37Node48Box
    .chi (7/128) (by rfl) (by rfl)
    component37Node45_sound component37Node48_sound

private noncomputable def component37Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/64), chiHi := (13/256) }

set_option maxRecDepth 1000000 in
private theorem component37Node50_sound : Sound component37Node50Box :=
  sound_of_literal_split component37Node50Box leaf1649Box leaf1650Box
    .k (63/16) (by rfl) (by rfl)
    leaf1649FlatSound leaf1650FlatSound

private noncomputable def component37Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/256), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node51_sound : Sound component37Node51Box :=
  sound_of_literal_split component37Node51Box leaf1651Box leaf1652Box
    .k (63/16) (by rfl) (by rfl)
    leaf1651FlatSound leaf1652FlatSound

private noncomputable def component37Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component37Node52_sound : Sound component37Node52Box :=
  sound_of_literal_split component37Node52Box component37Node50Box component37Node51Box
    .chi (13/256) (by rfl) (by rfl)
    component37Node50_sound component37Node51_sound

private noncomputable def component37Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node53_sound : Sound component37Node53Box :=
  sound_of_literal_split component37Node53Box leaf1653Box leaf1654Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1653FlatSound leaf1654FlatSound

private noncomputable def component37Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node54_sound : Sound component37Node54Box :=
  sound_of_literal_split component37Node54Box leaf1655Box leaf1656Box
    .chi (15/256) (by rfl) (by rfl)
    leaf1655FlatSound leaf1656FlatSound

private noncomputable def component37Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node55_sound : Sound component37Node55Box :=
  sound_of_literal_split component37Node55Box component37Node53Box component37Node54Box
    .k (63/16) (by rfl) (by rfl)
    component37Node53_sound component37Node54_sound

private noncomputable def component37Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node56_sound : Sound component37Node56Box :=
  sound_of_literal_split component37Node56Box component37Node52Box component37Node55Box
    .chi (7/128) (by rfl) (by rfl)
    component37Node52_sound component37Node55_sound

private noncomputable def component37Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node57_sound : Sound component37Node57Box :=
  sound_of_literal_split component37Node57Box component37Node49Box component37Node56Box
    .k (31/8) (by rfl) (by rfl)
    component37Node49_sound component37Node56_sound

private noncomputable def component37Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component37Node58_sound : Sound component37Node58Box :=
  sound_of_literal_split component37Node58Box component37Node42Box component37Node57Box
    .chi (3/64) (by rfl) (by rfl)
    component37Node42_sound component37Node57_sound

noncomputable def component37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
theorem component37_sound : Sound component37Box :=
  sound_of_literal_split component37Box component37Node27Box component37Node58Box
    .k (15/4) (by rfl) (by rfl)
    component37Node27_sound component37Node58_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
