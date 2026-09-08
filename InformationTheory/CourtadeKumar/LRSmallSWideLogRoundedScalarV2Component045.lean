import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf2037Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2037Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214263) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (754928367/536870912) }, upper := { exponent := 0, mantissa := (11657/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432119/268428526) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2037InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf2037LocalValidity :
    LeafFacts leaf2037Box leaf2037Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2037Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214263) }) = true
      norm_num [leaf2037Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2037CertificateValid :
    WideCertificateValid leaf2037Box leaf2037Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi181ValidityFacts
    leaf2037LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2037CoverageChecked :
    coverageCheck (innerAD leaf2037Box) leaf2037InnerLog = true := by
  rfl'

private theorem leaf2037InnerLogValid :
    leaf2037InnerLog.Valid 8 (innerAD leaf2037Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf2037CoverageChecked

private noncomputable def leaf2037InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2037InputLogOnePlusV_eq :
    leaf2037InputLogOnePlusV = outerEnclosure 24
      (leaf2037Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2037RoundedFacts : LeafRoundedFacts 8
    leaf2037Certificate.logOnePlusV leaf2037InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2037InputLogOnePlusV_eq }

private noncomputable def leaf2037Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi181InputQChi innerPair26Input
    leaf2037InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2037LowerChecked :
    lowerCheck 24 leaf2037Box leaf2037Inputs = true := by
  rfl'

private theorem leaf2037CoversExact : CoversExact 8
    leaf2037Box leaf2037Certificate leaf2037InnerLog leaf2037Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi181RoundedFacts
    innerPair26RoundedFacts leaf2037RoundedFacts (by rfl)

private theorem leaf2037FlatSound : Sound leaf2037Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2037CertificateValid
    leaf2037InnerLogValid leaf2037CoversExact leaf2037LowerChecked

private noncomputable def leaf2038Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2038Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107079) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (761743693/536870912) }, upper := { exponent := 0, mantissa := (5881/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216007/134214158) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2038InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf2038LocalValidity :
    LeafFacts leaf2038Box leaf2038Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2038Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107079) }) = true
      norm_num [leaf2038Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2038CertificateValid :
    WideCertificateValid leaf2038Box leaf2038Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi182ValidityFacts
    leaf2038LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2038CoverageChecked :
    coverageCheck (innerAD leaf2038Box) leaf2038InnerLog = true := by
  rfl'

private theorem leaf2038InnerLogValid :
    leaf2038InnerLog.Valid 8 (innerAD leaf2038Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf2038CoverageChecked

private noncomputable def leaf2038InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (45427/65536) }

set_option maxRecDepth 1000000 in
private theorem leaf2038InputLogOnePlusV_eq :
    leaf2038InputLogOnePlusV = outerEnclosure 24
      (leaf2038Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2038RoundedFacts : LeafRoundedFacts 8
    leaf2038Certificate.logOnePlusV leaf2038InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2038InputLogOnePlusV_eq }

private noncomputable def leaf2038Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi182InputQChi innerPair26Input
    leaf2038InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2038LowerChecked :
    lowerCheck 24 leaf2038Box leaf2038Inputs = true := by
  rfl'

private theorem leaf2038CoversExact : CoversExact 8
    leaf2038Box leaf2038Certificate leaf2038InnerLog leaf2038Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi182RoundedFacts
    innerPair26RoundedFacts leaf2038RoundedFacts (by rfl)

private theorem leaf2038FlatSound : Sound leaf2038Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2038CertificateValid
    leaf2038InnerLogValid leaf2038CoversExact leaf2038LowerChecked

private noncomputable def leaf2039Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2039Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107115) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (757025389/536870912) }, upper := { exponent := 0, mantissa := (5845/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216043/134214230) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2039InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf2039LocalValidity :
    LeafFacts leaf2039Box leaf2039Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2039Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107115) }) = true
      norm_num [leaf2039Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2039CertificateValid :
    WideCertificateValid leaf2039Box leaf2039Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi181ValidityFacts
    leaf2039LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2039CoverageChecked :
    coverageCheck (innerAD leaf2039Box) leaf2039InnerLog = true := by
  rfl'

private theorem leaf2039InnerLogValid :
    leaf2039InnerLog.Valid 8 (innerAD leaf2039Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf2039CoverageChecked

private noncomputable def leaf2039InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2039InputLogOnePlusV_eq :
    leaf2039InputLogOnePlusV = outerEnclosure 24
      (leaf2039Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2039RoundedFacts : LeafRoundedFacts 8
    leaf2039Certificate.logOnePlusV leaf2039InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2039InputLogOnePlusV_eq }

private noncomputable def leaf2039Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi181InputQChi innerPair26Input
    leaf2039InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2039LowerChecked :
    lowerCheck 24 leaf2039Box leaf2039Inputs = true := by
  rfl'

private theorem leaf2039CoversExact : CoversExact 8
    leaf2039Box leaf2039Certificate leaf2039InnerLog leaf2039Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi181RoundedFacts
    innerPair26RoundedFacts leaf2039RoundedFacts (by rfl)

private theorem leaf2039FlatSound : Sound leaf2039Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2039CertificateValid
    leaf2039InnerLogValid leaf2039CoversExact leaf2039LowerChecked

private noncomputable def leaf2040Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2040Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553531) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (763906247/536870912) }, upper := { exponent := 0, mantissa := (2949/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107995/67107062) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2040InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2040LocalValidity :
    LeafFacts leaf2040Box leaf2040Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2040Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553531) }) = true
      norm_num [leaf2040Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2040CertificateValid :
    WideCertificateValid leaf2040Box leaf2040Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi182ValidityFacts
    leaf2040LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2040CoverageChecked :
    coverageCheck (innerAD leaf2040Box) leaf2040InnerLog = true := by
  rfl'

private theorem leaf2040InnerLogValid :
    leaf2040InnerLog.Valid 8 (innerAD leaf2040Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2040CoverageChecked

private noncomputable def leaf2040InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2040InputLogOnePlusV_eq :
    leaf2040InputLogOnePlusV = outerEnclosure 24
      (leaf2040Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2040RoundedFacts : LeafRoundedFacts 8
    leaf2040Certificate.logOnePlusV leaf2040InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2040InputLogOnePlusV_eq }

private noncomputable def leaf2040Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi182InputQChi innerPair27Input
    leaf2040InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2040LowerChecked :
    lowerCheck 24 leaf2040Box leaf2040Inputs = true := by
  rfl'

private theorem leaf2040CoversExact : CoversExact 8
    leaf2040Box leaf2040Certificate leaf2040InnerLog leaf2040Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi182RoundedFacts
    innerPair27RoundedFacts leaf2040RoundedFacts (by rfl)

private theorem leaf2040FlatSound : Sound leaf2040Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2040CertificateValid
    leaf2040InnerLogValid leaf2040CoversExact leaf2040LowerChecked

private noncomputable def leaf2041Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2041Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214053) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (768559019/536870912) }, upper := { exponent := 0, mantissa := (11867/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431909/268428106) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2041InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2041LocalValidity :
    LeafFacts leaf2041Box leaf2041Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2041Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214053) }) = true
      norm_num [leaf2041Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2041CertificateValid :
    WideCertificateValid leaf2041Box leaf2041Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi179ValidityFacts
    leaf2041LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2041CoverageChecked :
    coverageCheck (innerAD leaf2041Box) leaf2041InnerLog = true := by
  rfl'

private theorem leaf2041InnerLogValid :
    leaf2041InnerLog.Valid 8 (innerAD leaf2041Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2041CoverageChecked

private noncomputable def leaf2041InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2041InputLogOnePlusV_eq :
    leaf2041InputLogOnePlusV = outerEnclosure 24
      (leaf2041Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2041RoundedFacts : LeafRoundedFacts 8
    leaf2041Certificate.logOnePlusV leaf2041InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2041InputLogOnePlusV_eq }

private noncomputable def leaf2041Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi179InputQChi innerPair27Input
    leaf2041InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2041LowerChecked :
    lowerCheck 24 leaf2041Box leaf2041Inputs = true := by
  rfl'

private theorem leaf2041CoversExact : CoversExact 8
    leaf2041Box leaf2041Certificate leaf2041InnerLog leaf2041Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi179RoundedFacts
    innerPair27RoundedFacts leaf2041RoundedFacts (by rfl)

private theorem leaf2041FlatSound : Sound leaf2041Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2041CertificateValid
    leaf2041InnerLogValid leaf2041CoversExact leaf2041LowerChecked

private noncomputable def leaf2042Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2042Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (775374345/536870912) }, upper := { exponent := 0, mantissa := (2993/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107951/67106974) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2042InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2042LocalValidity :
    LeafFacts leaf2042Box leaf2042Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2042Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553487) }) = true
      norm_num [leaf2042Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2042CertificateValid :
    WideCertificateValid leaf2042Box leaf2042Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi180ValidityFacts
    leaf2042LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2042CoverageChecked :
    coverageCheck (innerAD leaf2042Box) leaf2042InnerLog = true := by
  rfl'

private theorem leaf2042InnerLogValid :
    leaf2042InnerLog.Valid 8 (innerAD leaf2042Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2042CoverageChecked

private noncomputable def leaf2042InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2042InputLogOnePlusV_eq :
    leaf2042InputLogOnePlusV = outerEnclosure 24
      (leaf2042Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2042RoundedFacts : LeafRoundedFacts 8
    leaf2042Certificate.logOnePlusV leaf2042InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2042InputLogOnePlusV_eq }

private noncomputable def leaf2042Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2042InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2042LowerChecked :
    lowerCheck 24 leaf2042Box leaf2042Inputs = true := by
  rfl'

private theorem leaf2042CoversExact : CoversExact 8
    leaf2042Box leaf2042Certificate leaf2042InnerLog leaf2042Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2042RoundedFacts (by rfl)

private theorem leaf2042FlatSound : Sound leaf2042Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2042CertificateValid
    leaf2042InnerLogValid leaf2042CoversExact leaf2042LowerChecked

private noncomputable def leaf2043Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2043Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107009) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (770787105/536870912) }, upper := { exponent := 0, mantissa := (5951/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215937/134214018) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2043InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2043LocalValidity :
    LeafFacts leaf2043Box leaf2043Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2043Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107009) }) = true
      norm_num [leaf2043Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2043CertificateValid :
    WideCertificateValid leaf2043Box leaf2043Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi179ValidityFacts
    leaf2043LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2043CoverageChecked :
    coverageCheck (innerAD leaf2043Box) leaf2043InnerLog = true := by
  rfl'

private theorem leaf2043InnerLogValid :
    leaf2043InnerLog.Valid 8 (innerAD leaf2043Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2043CoverageChecked

private noncomputable def leaf2043InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2043InputLogOnePlusV_eq :
    leaf2043InputLogOnePlusV = outerEnclosure 24
      (leaf2043Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2043RoundedFacts : LeafRoundedFacts 8
    leaf2043Certificate.logOnePlusV leaf2043InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2043InputLogOnePlusV_eq }

private noncomputable def leaf2043Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi179InputQChi innerPair27Input
    leaf2043InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2043LowerChecked :
    lowerCheck 24 leaf2043Box leaf2043Inputs = true := by
  rfl'

private theorem leaf2043CoversExact : CoversExact 8
    leaf2043Box leaf2043Certificate leaf2043InnerLog leaf2043Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi179RoundedFacts
    innerPair27RoundedFacts leaf2043RoundedFacts (by rfl)

private theorem leaf2043FlatSound : Sound leaf2043Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2043CertificateValid
    leaf2043InnerLogValid leaf2043CoversExact leaf2043LowerChecked

private noncomputable def leaf2044Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2044Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (986896/986867) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (777667963/536870912) }, upper := { exponent := 0, mantissa := (1501/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1973763/1973734) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2044InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2044LocalValidity :
    LeafFacts leaf2044Box leaf2044Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2044Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (986896/986867) }) = true
      norm_num [leaf2044Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2044CertificateValid :
    WideCertificateValid leaf2044Box leaf2044Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi180ValidityFacts
    leaf2044LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2044CoverageChecked :
    coverageCheck (innerAD leaf2044Box) leaf2044InnerLog = true := by
  rfl'

private theorem leaf2044InnerLogValid :
    leaf2044InnerLog.Valid 8 (innerAD leaf2044Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2044CoverageChecked

private noncomputable def leaf2044InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2044InputLogOnePlusV_eq :
    leaf2044InputLogOnePlusV = outerEnclosure 24
      (leaf2044Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2044RoundedFacts : LeafRoundedFacts 8
    leaf2044Certificate.logOnePlusV leaf2044InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2044InputLogOnePlusV_eq }

private noncomputable def leaf2044Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2044InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2044LowerChecked :
    lowerCheck 24 leaf2044Box leaf2044Inputs = true := by
  rfl'

private theorem leaf2044CoversExact : CoversExact 8
    leaf2044Box leaf2044Certificate leaf2044InnerLog leaf2044Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2044RoundedFacts (by rfl)

private theorem leaf2044FlatSound : Sound leaf2044Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2044CertificateValid
    leaf2044InnerLogValid leaf2044CoversExact leaf2044LowerChecked

private noncomputable def leaf2045Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2045Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214197) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (759122411/536870912) }, upper := { exponent := 0, mantissa := (11723/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432053/268428394) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2045InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf2045LocalValidity :
    LeafFacts leaf2045Box leaf2045Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2045Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214197) }) = true
      norm_num [leaf2045Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2045CertificateValid :
    WideCertificateValid leaf2045Box leaf2045Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi181ValidityFacts
    leaf2045LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2045CoverageChecked :
    coverageCheck (innerAD leaf2045Box) leaf2045InnerLog = true := by
  rfl'

private theorem leaf2045InnerLogValid :
    leaf2045InnerLog.Valid 8 (innerAD leaf2045Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf2045CoverageChecked

private noncomputable def leaf2045InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2045InputLogOnePlusV_eq :
    leaf2045InputLogOnePlusV = outerEnclosure 24
      (leaf2045Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2045RoundedFacts : LeafRoundedFacts 8
    leaf2045Certificate.logOnePlusV leaf2045InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2045InputLogOnePlusV_eq }

private noncomputable def leaf2045Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi181InputQChi innerPair26Input
    leaf2045InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2045LowerChecked :
    lowerCheck 24 leaf2045Box leaf2045Inputs = true := by
  rfl'

private theorem leaf2045CoversExact : CoversExact 8
    leaf2045Box leaf2045Certificate leaf2045InnerLog leaf2045Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi181RoundedFacts
    innerPair26RoundedFacts leaf2045RoundedFacts (by rfl)

private theorem leaf2045FlatSound : Sound leaf2045Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2045CertificateValid
    leaf2045InnerLogValid leaf2045CoversExact leaf2045LowerChecked

private noncomputable def leaf2046Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2046Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107045) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (766068801/536870912) }, upper := { exponent := 0, mantissa := (5915/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215973/134214090) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2046InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2046LocalValidity :
    LeafFacts leaf2046Box leaf2046Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2046Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107045) }) = true
      norm_num [leaf2046Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2046CertificateValid :
    WideCertificateValid leaf2046Box leaf2046Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi182ValidityFacts
    leaf2046LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2046CoverageChecked :
    coverageCheck (innerAD leaf2046Box) leaf2046InnerLog = true := by
  rfl'

private theorem leaf2046InnerLogValid :
    leaf2046InnerLog.Valid 8 (innerAD leaf2046Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2046CoverageChecked

private noncomputable def leaf2046InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2046InputLogOnePlusV_eq :
    leaf2046InputLogOnePlusV = outerEnclosure 24
      (leaf2046Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2046RoundedFacts : LeafRoundedFacts 8
    leaf2046Certificate.logOnePlusV leaf2046InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2046InputLogOnePlusV_eq }

private noncomputable def leaf2046Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi182InputQChi innerPair27Input
    leaf2046InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2046LowerChecked :
    lowerCheck 24 leaf2046Box leaf2046Inputs = true := by
  rfl'

private theorem leaf2046CoversExact : CoversExact 8
    leaf2046Box leaf2046Certificate leaf2046InnerLog leaf2046Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi182RoundedFacts
    innerPair27RoundedFacts leaf2046RoundedFacts (by rfl)

private theorem leaf2046FlatSound : Sound leaf2046Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2046CertificateValid
    leaf2046InnerLogValid leaf2046CoversExact leaf2046LowerChecked

private noncomputable def leaf2047Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2047Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553541) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (761219433/536870912) }, upper := { exponent := 0, mantissa := (2939/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108005/67107082) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2047InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf2047LocalValidity :
    LeafFacts leaf2047Box leaf2047Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2047Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553541) }) = true
      norm_num [leaf2047Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2047CertificateValid :
    WideCertificateValid leaf2047Box leaf2047Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi181ValidityFacts
    leaf2047LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2047CoverageChecked :
    coverageCheck (innerAD leaf2047Box) leaf2047InnerLog = true := by
  rfl'

private theorem leaf2047InnerLogValid :
    leaf2047InnerLog.Valid 8 (innerAD leaf2047Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf2047CoverageChecked

private noncomputable def leaf2047InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2047InputLogOnePlusV_eq :
    leaf2047InputLogOnePlusV = outerEnclosure 24
      (leaf2047Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2047RoundedFacts : LeafRoundedFacts 8
    leaf2047Certificate.logOnePlusV leaf2047InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2047InputLogOnePlusV_eq }

private noncomputable def leaf2047Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi181InputQChi innerPair26Input
    leaf2047InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2047LowerChecked :
    lowerCheck 24 leaf2047Box leaf2047Inputs = true := by
  rfl'

private theorem leaf2047CoversExact : CoversExact 8
    leaf2047Box leaf2047Certificate leaf2047InnerLog leaf2047Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi181RoundedFacts
    innerPair26RoundedFacts leaf2047RoundedFacts (by rfl)

private theorem leaf2047FlatSound : Sound leaf2047Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2047CertificateValid
    leaf2047InnerLogValid leaf2047CoversExact leaf2047LowerChecked

private noncomputable def leaf2048Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2048Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776757) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (768231355/536870912) }, upper := { exponent := 0, mantissa := (1483/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553989/33553514) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2048InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2048LocalValidity :
    LeafFacts leaf2048Box leaf2048Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2048Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776757) }) = true
      norm_num [leaf2048Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2048CertificateValid :
    WideCertificateValid leaf2048Box leaf2048Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi182ValidityFacts
    leaf2048LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2048CoverageChecked :
    coverageCheck (innerAD leaf2048Box) leaf2048InnerLog = true := by
  rfl'

private theorem leaf2048InnerLogValid :
    leaf2048InnerLog.Valid 8 (innerAD leaf2048Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2048CoverageChecked

private noncomputable def leaf2048InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2048InputLogOnePlusV_eq :
    leaf2048InputLogOnePlusV = outerEnclosure 24
      (leaf2048Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2048RoundedFacts : LeafRoundedFacts 8
    leaf2048Certificate.logOnePlusV leaf2048InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2048InputLogOnePlusV_eq }

private noncomputable def leaf2048Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi182InputQChi innerPair27Input
    leaf2048InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2048LowerChecked :
    lowerCheck 24 leaf2048Box leaf2048Inputs = true := by
  rfl'

private theorem leaf2048CoversExact : CoversExact 8
    leaf2048Box leaf2048Certificate leaf2048InnerLog leaf2048Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi182RoundedFacts
    innerPair27RoundedFacts leaf2048RoundedFacts (by rfl)

private theorem leaf2048FlatSound : Sound leaf2048Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2048CertificateValid
    leaf2048InnerLogValid leaf2048CoversExact leaf2048LowerChecked

private noncomputable def leaf2049Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2049Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213983) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (773015191/536870912) }, upper := { exponent := 0, mantissa := (11937/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431839/268427966) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2049InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2049LocalValidity :
    LeafFacts leaf2049Box leaf2049Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2049Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213983) }) = true
      norm_num [leaf2049Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2049CertificateValid :
    WideCertificateValid leaf2049Box leaf2049Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi179ValidityFacts
    leaf2049LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2049CoverageChecked :
    coverageCheck (innerAD leaf2049Box) leaf2049InnerLog = true := by
  rfl'

private theorem leaf2049InnerLogValid :
    leaf2049InnerLog.Valid 8 (innerAD leaf2049Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2049CoverageChecked

private noncomputable def leaf2049InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2049InputLogOnePlusV_eq :
    leaf2049InputLogOnePlusV = outerEnclosure 24
      (leaf2049Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2049RoundedFacts : LeafRoundedFacts 8
    leaf2049Certificate.logOnePlusV leaf2049InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2049InputLogOnePlusV_eq }

private noncomputable def leaf2049Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2049InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2049LowerChecked :
    lowerCheck 24 leaf2049Box leaf2049Inputs = true := by
  rfl'

private theorem leaf2049CoversExact : CoversExact 8
    leaf2049Box leaf2049Certificate leaf2049InnerLog leaf2049Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2049RoundedFacts (by rfl)

private theorem leaf2049FlatSound : Sound leaf2049Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2049CertificateValid
    leaf2049InnerLogValid leaf2049CoversExact leaf2049LowerChecked

private noncomputable def leaf2050Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2050Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553469) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (779961581/536870912) }, upper := { exponent := 0, mantissa := (3011/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107933/67106938) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2050InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2050LocalValidity :
    LeafFacts leaf2050Box leaf2050Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2050Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553469) }) = true
      norm_num [leaf2050Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2050CertificateValid :
    WideCertificateValid leaf2050Box leaf2050Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi180ValidityFacts
    leaf2050LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2050CoverageChecked :
    coverageCheck (innerAD leaf2050Box) leaf2050InnerLog = true := by
  rfl'

private theorem leaf2050InnerLogValid :
    leaf2050InnerLog.Valid 8 (innerAD leaf2050Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2050CoverageChecked

private noncomputable def leaf2050InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2050InputLogOnePlusV_eq :
    leaf2050InputLogOnePlusV = outerEnclosure 24
      (leaf2050Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2050RoundedFacts : LeafRoundedFacts 8
    leaf2050Certificate.logOnePlusV leaf2050InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2050InputLogOnePlusV_eq }

private noncomputable def leaf2050Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2050InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2050LowerChecked :
    lowerCheck 24 leaf2050Box leaf2050Inputs = true := by
  rfl'

private theorem leaf2050CoversExact : CoversExact 8
    leaf2050Box leaf2050Certificate leaf2050InnerLog leaf2050Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2050RoundedFacts (by rfl)

private theorem leaf2050FlatSound : Sound leaf2050Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2050CertificateValid
    leaf2050InnerLogValid leaf2050CoversExact leaf2050LowerChecked

private noncomputable def leaf2051Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2051Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (775243277/536870912) }, upper := { exponent := 0, mantissa := (2993/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107951/67106974) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2051InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2051LocalValidity :
    LeafFacts leaf2051Box leaf2051Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2051Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553487) }) = true
      norm_num [leaf2051Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2051CertificateValid :
    WideCertificateValid leaf2051Box leaf2051Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi179ValidityFacts
    leaf2051LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2051CoverageChecked :
    coverageCheck (innerAD leaf2051Box) leaf2051InnerLog = true := by
  rfl'

private theorem leaf2051InnerLogValid :
    leaf2051InnerLog.Valid 8 (innerAD leaf2051Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2051CoverageChecked

private noncomputable def leaf2051InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2051InputLogOnePlusV_eq :
    leaf2051InputLogOnePlusV = outerEnclosure 24
      (leaf2051Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2051RoundedFacts : LeafRoundedFacts 8
    leaf2051Certificate.logOnePlusV leaf2051InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2051InputLogOnePlusV_eq }

private noncomputable def leaf2051Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2051InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2051LowerChecked :
    lowerCheck 24 leaf2051Box leaf2051Inputs = true := by
  rfl'

private theorem leaf2051CoversExact : CoversExact 8
    leaf2051Box leaf2051Certificate leaf2051InnerLog leaf2051Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2051RoundedFacts (by rfl)

private theorem leaf2051FlatSound : Sound leaf2051Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2051CertificateValid
    leaf2051InnerLogValid leaf2051CoversExact leaf2051LowerChecked

private noncomputable def leaf2052Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2052Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388365) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (782255199/536870912) }, upper := { exponent := 0, mantissa := (755/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16776981/16776730) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2052InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2052LocalValidity :
    LeafFacts leaf2052Box leaf2052Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2052Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388365) }) = true
      norm_num [leaf2052Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2052CertificateValid :
    WideCertificateValid leaf2052Box leaf2052Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi180ValidityFacts
    leaf2052LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2052CoverageChecked :
    coverageCheck (innerAD leaf2052Box) leaf2052InnerLog = true := by
  rfl'

private theorem leaf2052InnerLogValid :
    leaf2052InnerLog.Valid 8 (innerAD leaf2052Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2052CoverageChecked

private noncomputable def leaf2052InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2052InputLogOnePlusV_eq :
    leaf2052InputLogOnePlusV = outerEnclosure 24
      (leaf2052Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2052RoundedFacts : LeafRoundedFacts 8
    leaf2052Certificate.logOnePlusV leaf2052InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2052InputLogOnePlusV_eq }

private noncomputable def leaf2052Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2052InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2052LowerChecked :
    lowerCheck 24 leaf2052Box leaf2052Inputs = true := by
  rfl'

private theorem leaf2052CoversExact : CoversExact 8
    leaf2052Box leaf2052Certificate leaf2052InnerLog leaf2052Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2052RoundedFacts (by rfl)

private theorem leaf2052FlatSound : Sound leaf2052Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2052CertificateValid
    leaf2052InnerLogValid leaf2052CoversExact leaf2052LowerChecked

private noncomputable def leaf2053Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2053Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213843) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (782189671/536870912) }, upper := { exponent := 0, mantissa := (12077/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431699/268427686) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2053InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2053LocalValidity :
    LeafFacts leaf2053Box leaf2053Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2053Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213843) }) = true
      norm_num [leaf2053Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2053CertificateValid :
    WideCertificateValid leaf2053Box leaf2053Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi175ValidityFacts
    leaf2053LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2053CoverageChecked :
    coverageCheck (innerAD leaf2053Box) leaf2053InnerLog = true := by
  rfl'

private theorem leaf2053InnerLogValid :
    leaf2053InnerLog.Valid 8 (innerAD leaf2053Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2053CoverageChecked

private noncomputable def leaf2053InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2053InputLogOnePlusV_eq :
    leaf2053InputLogOnePlusV = outerEnclosure 24
      (leaf2053Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2053RoundedFacts : LeafRoundedFacts 8
    leaf2053Certificate.logOnePlusV leaf2053InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2053InputLogOnePlusV_eq }

private noncomputable def leaf2053Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi175InputQChi innerPair34Input
    leaf2053InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2053LowerChecked :
    lowerCheck 24 leaf2053Box leaf2053Inputs = true := by
  rfl'

private theorem leaf2053CoversExact : CoversExact 8
    leaf2053Box leaf2053Certificate leaf2053InnerLog leaf2053Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf2053RoundedFacts (by rfl)

private theorem leaf2053FlatSound : Sound leaf2053Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2053CertificateValid
    leaf2053InnerLogValid leaf2053CoversExact leaf2053LowerChecked

private noncomputable def leaf2054Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2054Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717433856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (789004997/536870912) }, upper := { exponent := 0, mantissa := (6091/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435927551/137434867712) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2054InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2054LocalValidity :
    LeafFacts leaf2054Box leaf2054Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2054Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717433856) }) = true
      norm_num [leaf2054Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2054CertificateValid :
    WideCertificateValid leaf2054Box leaf2054Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi176ValidityFacts
    leaf2054LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2054CoverageChecked :
    coverageCheck (innerAD leaf2054Box) leaf2054InnerLog = true := by
  rfl'

private theorem leaf2054InnerLogValid :
    leaf2054InnerLog.Valid 8 (innerAD leaf2054Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2054CoverageChecked

private noncomputable def leaf2054InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2054InputLogOnePlusV_eq :
    leaf2054InputLogOnePlusV = outerEnclosure 24
      (leaf2054Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2054RoundedFacts : LeafRoundedFacts 8
    leaf2054Certificate.logOnePlusV leaf2054InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2054InputLogOnePlusV_eq }

private noncomputable def leaf2054Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi176InputQChi innerPair34Input
    leaf2054InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2054LowerChecked :
    lowerCheck 24 leaf2054Box leaf2054Inputs = true := by
  rfl'

private theorem leaf2054CoversExact : CoversExact 8
    leaf2054Box leaf2054Certificate leaf2054InnerLog leaf2054Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf2054RoundedFacts (by rfl)

private theorem leaf2054FlatSound : Sound leaf2054Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2054CertificateValid
    leaf2054InnerLogValid leaf2054CoversExact leaf2054LowerChecked

private noncomputable def leaf2055Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2055Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67106903) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (784548821/536870912) }, upper := { exponent := 0, mantissa := (6057/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215831/134213806) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2055InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2055LocalValidity :
    LeafFacts leaf2055Box leaf2055Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2055Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67106903) }) = true
      norm_num [leaf2055Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2055CertificateValid :
    WideCertificateValid leaf2055Box leaf2055Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi175ValidityFacts
    leaf2055LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2055CoverageChecked :
    coverageCheck (innerAD leaf2055Box) leaf2055InnerLog = true := by
  rfl'

private theorem leaf2055InnerLogValid :
    leaf2055InnerLog.Valid 8 (innerAD leaf2055Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2055CoverageChecked

private noncomputable def leaf2055InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2055InputLogOnePlusV_eq :
    leaf2055InputLogOnePlusV = outerEnclosure 24
      (leaf2055Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2055RoundedFacts : LeafRoundedFacts 8
    leaf2055Certificate.logOnePlusV leaf2055InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2055InputLogOnePlusV_eq }

private noncomputable def leaf2055Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi175InputQChi innerPair34Input
    leaf2055InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2055LowerChecked :
    lowerCheck 24 leaf2055Box leaf2055Inputs = true := by
  rfl'

private theorem leaf2055CoversExact : CoversExact 8
    leaf2055Box leaf2055Certificate leaf2055InnerLog leaf2055Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf2055RoundedFacts (by rfl)

private theorem leaf2055FlatSound : Sound leaf2055Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2055CertificateValid
    leaf2055InnerLogValid leaf2055CoversExact leaf2055LowerChecked

private noncomputable def leaf2056Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2056Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (4581232913/4581160960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (791429679/536870912) }, upper := { exponent := 0, mantissa := (3055/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (9162393873/9162321920) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2056InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2056LocalValidity :
    LeafFacts leaf2056Box leaf2056Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2056Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4581232913/4581160960) }) = true
      norm_num [leaf2056Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2056CertificateValid :
    WideCertificateValid leaf2056Box leaf2056Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi176ValidityFacts
    leaf2056LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2056CoverageChecked :
    coverageCheck (innerAD leaf2056Box) leaf2056InnerLog = true := by
  rfl'

private theorem leaf2056InnerLogValid :
    leaf2056InnerLog.Valid 8 (innerAD leaf2056Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2056CoverageChecked

private noncomputable def leaf2056InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2056InputLogOnePlusV_eq :
    leaf2056InputLogOnePlusV = outerEnclosure 24
      (leaf2056Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2056RoundedFacts : LeafRoundedFacts 8
    leaf2056Certificate.logOnePlusV leaf2056InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2056InputLogOnePlusV_eq }

private noncomputable def leaf2056Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi176InputQChi innerPair34Input
    leaf2056InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2056LowerChecked :
    lowerCheck 24 leaf2056Box leaf2056Inputs = true := by
  rfl'

private theorem leaf2056CoversExact : CoversExact 8
    leaf2056Box leaf2056Certificate leaf2056InnerLog leaf2056Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf2056RoundedFacts (by rfl)

private theorem leaf2056FlatSound : Sound leaf2056Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2056CertificateValid
    leaf2056InnerLogValid leaf2056CoversExact leaf2056LowerChecked

private noncomputable def leaf2057Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2057Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717380096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (795820323/536870912) }, upper := { exponent := 0, mantissa := (12287/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435873791/137434760192) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2057InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2057LocalValidity :
    LeafFacts leaf2057Box leaf2057Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2057Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717380096) }) = true
      norm_num [leaf2057Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2057CertificateValid :
    WideCertificateValid leaf2057Box leaf2057Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi177ValidityFacts
    leaf2057LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2057CoverageChecked :
    coverageCheck (innerAD leaf2057Box) leaf2057InnerLog = true := by
  rfl'

private theorem leaf2057InnerLogValid :
    leaf2057InnerLog.Valid 8 (innerAD leaf2057Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2057CoverageChecked

private noncomputable def leaf2057InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2057InputLogOnePlusV_eq :
    leaf2057InputLogOnePlusV = outerEnclosure 24
      (leaf2057Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2057RoundedFacts : LeafRoundedFacts 8
    leaf2057Certificate.logOnePlusV leaf2057InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2057InputLogOnePlusV_eq }

private noncomputable def leaf2057Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi177InputQChi innerPair34Input
    leaf2057InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2057LowerChecked :
    lowerCheck 24 leaf2057Box leaf2057Inputs = true := by
  rfl'

private theorem leaf2057CoversExact : CoversExact 8
    leaf2057Box leaf2057Certificate leaf2057InnerLog leaf2057Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi177RoundedFacts
    innerPair34RoundedFacts leaf2057RoundedFacts (by rfl)

private theorem leaf2057FlatSound : Sound leaf2057Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2057CertificateValid
    leaf2057InnerLogValid leaf2057CoversExact leaf2057LowerChecked

private noncomputable def leaf2058Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2058Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717326336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (802635649/536870912) }, upper := { exponent := 0, mantissa := (1549/1024) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435820031/137434652672) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2058InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2058LocalValidity :
    LeafFacts leaf2058Box leaf2058Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2058Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717326336) }) = true
      norm_num [leaf2058Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2058CertificateValid :
    WideCertificateValid leaf2058Box leaf2058Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi178ValidityFacts
    leaf2058LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2058CoverageChecked :
    coverageCheck (innerAD leaf2058Box) leaf2058InnerLog = true := by
  rfl'

private theorem leaf2058InnerLogValid :
    leaf2058InnerLog.Valid 8 (innerAD leaf2058Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2058CoverageChecked

private noncomputable def leaf2058InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2058InputLogOnePlusV_eq :
    leaf2058InputLogOnePlusV = outerEnclosure 24
      (leaf2058Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2058RoundedFacts : LeafRoundedFacts 8
    leaf2058Certificate.logOnePlusV leaf2058InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2058InputLogOnePlusV_eq }

private noncomputable def leaf2058Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi178InputQChi innerPair409Input
    leaf2058InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2058LowerChecked :
    lowerCheck 24 leaf2058Box leaf2058Inputs = true := by
  rfl'

private theorem leaf2058CoversExact : CoversExact 8
    leaf2058Box leaf2058Certificate leaf2058InnerLog leaf2058Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi178RoundedFacts
    innerPair409RoundedFacts leaf2058RoundedFacts (by rfl)

private theorem leaf2058FlatSound : Sound leaf2058Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2058CertificateValid
    leaf2058InnerLogValid leaf2058CoversExact leaf2058LowerChecked

private noncomputable def leaf2059Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2059Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717360128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (798310537/536870912) }, upper := { exponent := 0, mantissa := (6163/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435853823/137434720256) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2059InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2059LocalValidity :
    LeafFacts leaf2059Box leaf2059Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2059Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717360128) }) = true
      norm_num [leaf2059Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2059CertificateValid :
    WideCertificateValid leaf2059Box leaf2059Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi177ValidityFacts
    leaf2059LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2059CoverageChecked :
    coverageCheck (innerAD leaf2059Box) leaf2059InnerLog = true := by
  rfl'

private theorem leaf2059InnerLogValid :
    leaf2059InnerLog.Valid 8 (innerAD leaf2059Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2059CoverageChecked

private noncomputable def leaf2059InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2059InputLogOnePlusV_eq :
    leaf2059InputLogOnePlusV = outerEnclosure 24
      (leaf2059Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2059RoundedFacts : LeafRoundedFacts 8
    leaf2059Certificate.logOnePlusV leaf2059InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2059InputLogOnePlusV_eq }

private noncomputable def leaf2059Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi177InputQChi innerPair409Input
    leaf2059InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2059LowerChecked :
    lowerCheck 24 leaf2059Box leaf2059Inputs = true := by
  rfl'

private theorem leaf2059CoversExact : CoversExact 8
    leaf2059Box leaf2059Certificate leaf2059InnerLog leaf2059Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi177RoundedFacts
    innerPair409RoundedFacts leaf2059RoundedFacts (by rfl)

private theorem leaf2059FlatSound : Sound leaf2059Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2059CertificateValid
    leaf2059InnerLogValid leaf2059CoversExact leaf2059LowerChecked

private noncomputable def leaf2060Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2060Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717305856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (805191395/536870912) }, upper := { exponent := 0, mantissa := (777/512) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435799551/137434611712) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2060InnerLog : WideLogData :=
  innerPair408Data

set_option maxRecDepth 1000000 in
private theorem leaf2060LocalValidity :
    LeafFacts leaf2060Box leaf2060Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2060Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717305856) }) = true
      norm_num [leaf2060Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2060CertificateValid :
    WideCertificateValid leaf2060Box leaf2060Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi178ValidityFacts
    leaf2060LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2060CoverageChecked :
    coverageCheck (innerAD leaf2060Box) leaf2060InnerLog = true := by
  rfl'

private theorem leaf2060InnerLogValid :
    leaf2060InnerLog.Valid 8 (innerAD leaf2060Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint19PositiveFacts.valid leaf2060CoverageChecked

private noncomputable def leaf2060InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2060InputLogOnePlusV_eq :
    leaf2060InputLogOnePlusV = outerEnclosure 24
      (leaf2060Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2060RoundedFacts : LeafRoundedFacts 8
    leaf2060Certificate.logOnePlusV leaf2060InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2060InputLogOnePlusV_eq }

private noncomputable def leaf2060Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi178InputQChi innerPair408Input
    leaf2060InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2060LowerChecked :
    lowerCheck 24 leaf2060Box leaf2060Inputs = true := by
  rfl'

private theorem leaf2060CoversExact : CoversExact 8
    leaf2060Box leaf2060Certificate leaf2060InnerLog leaf2060Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi178RoundedFacts
    innerPair408RoundedFacts leaf2060RoundedFacts (by rfl)

private theorem leaf2060FlatSound : Sound leaf2060Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2060CertificateValid
    leaf2060InnerLogValid leaf2060CoversExact leaf2060LowerChecked

private noncomputable def leaf2061Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2061Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213769) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (786907971/536870912) }, upper := { exponent := 0, mantissa := (12151/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431625/268427538) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2061InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2061LocalValidity :
    LeafFacts leaf2061Box leaf2061Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2061Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213769) }) = true
      norm_num [leaf2061Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2061CertificateValid :
    WideCertificateValid leaf2061Box leaf2061Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi175ValidityFacts
    leaf2061LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2061CoverageChecked :
    coverageCheck (innerAD leaf2061Box) leaf2061InnerLog = true := by
  rfl'

private theorem leaf2061InnerLogValid :
    leaf2061InnerLog.Valid 8 (innerAD leaf2061Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2061CoverageChecked

private noncomputable def leaf2061InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2061InputLogOnePlusV_eq :
    leaf2061InputLogOnePlusV = outerEnclosure 24
      (leaf2061Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2061RoundedFacts : LeafRoundedFacts 8
    leaf2061Certificate.logOnePlusV leaf2061InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2061InputLogOnePlusV_eq }

private noncomputable def leaf2061Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi175InputQChi innerPair34Input
    leaf2061InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2061LowerChecked :
    lowerCheck 24 leaf2061Box leaf2061Inputs = true := by
  rfl'

private theorem leaf2061CoversExact : CoversExact 8
    leaf2061Box leaf2061Certificate leaf2061InnerLog leaf2061Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf2061RoundedFacts (by rfl)

private theorem leaf2061FlatSound : Sound leaf2061Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2061CertificateValid
    leaf2061InnerLogValid leaf2061CoversExact leaf2061LowerChecked

private noncomputable def leaf2062Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2062Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717394944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (793854361/536870912) }, upper := { exponent := 0, mantissa := (6129/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435888639/137434789888) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2062InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2062LocalValidity :
    LeafFacts leaf2062Box leaf2062Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2062Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717394944) }) = true
      norm_num [leaf2062Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2062CertificateValid :
    WideCertificateValid leaf2062Box leaf2062Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi176ValidityFacts
    leaf2062LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2062CoverageChecked :
    coverageCheck (innerAD leaf2062Box) leaf2062InnerLog = true := by
  rfl'

private theorem leaf2062InnerLogValid :
    leaf2062InnerLog.Valid 8 (innerAD leaf2062Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2062CoverageChecked

private noncomputable def leaf2062InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2062InputLogOnePlusV_eq :
    leaf2062InputLogOnePlusV = outerEnclosure 24
      (leaf2062Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2062RoundedFacts : LeafRoundedFacts 8
    leaf2062Certificate.logOnePlusV leaf2062InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2062InputLogOnePlusV_eq }

private noncomputable def leaf2062Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi176InputQChi innerPair34Input
    leaf2062InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2062LowerChecked :
    lowerCheck 24 leaf2062Box leaf2062Inputs = true := by
  rfl'

private theorem leaf2062CoversExact : CoversExact 8
    leaf2062Box leaf2062Certificate leaf2062InnerLog leaf2062Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi176RoundedFacts
    innerPair34RoundedFacts leaf2062RoundedFacts (by rfl)

private theorem leaf2062FlatSound : Sound leaf2062Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2062CertificateValid
    leaf2062InnerLogValid leaf2062CoversExact leaf2062LowerChecked

private noncomputable def leaf2063Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2063Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717430784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (789267121/536870912) }, upper := { exponent := 0, mantissa := (3047/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435924479/137434861568) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2063InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2063LocalValidity :
    LeafFacts leaf2063Box leaf2063Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2063Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717430784) }) = true
      norm_num [leaf2063Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2063CertificateValid :
    WideCertificateValid leaf2063Box leaf2063Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi175ValidityFacts
    leaf2063LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2063CoverageChecked :
    coverageCheck (innerAD leaf2063Box) leaf2063InnerLog = true := by
  rfl'

private theorem leaf2063InnerLogValid :
    leaf2063InnerLog.Valid 8 (innerAD leaf2063Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2063CoverageChecked

private noncomputable def leaf2063InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2063InputLogOnePlusV_eq :
    leaf2063InputLogOnePlusV = outerEnclosure 24
      (leaf2063Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2063RoundedFacts : LeafRoundedFacts 8
    leaf2063Certificate.logOnePlusV leaf2063InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2063InputLogOnePlusV_eq }

private noncomputable def leaf2063Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi175InputQChi innerPair34Input
    leaf2063InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2063LowerChecked :
    lowerCheck 24 leaf2063Box leaf2063Inputs = true := by
  rfl'

private theorem leaf2063CoversExact : CoversExact 8
    leaf2063Box leaf2063Certificate leaf2063InnerLog leaf2063Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf2063RoundedFacts (by rfl)

private theorem leaf2063FlatSound : Sound leaf2063Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2063CertificateValid
    leaf2063InnerLogValid leaf2063CoversExact leaf2063LowerChecked

private noncomputable def leaf2064Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2064Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (267387135/267382784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (796279043/536870912) }, upper := { exponent := 0, mantissa := (1537/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (534769919/534765568) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2064InnerLog : WideLogData :=
  innerPair153Data

set_option maxRecDepth 1000000 in
private theorem leaf2064LocalValidity :
    LeafFacts leaf2064Box leaf2064Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2064Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (267387135/267382784) }) = true
      norm_num [leaf2064Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2064CertificateValid :
    WideCertificateValid leaf2064Box leaf2064Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi176ValidityFacts
    leaf2064LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2064CoverageChecked :
    coverageCheck (innerAD leaf2064Box) leaf2064InnerLog = true := by
  rfl'

private theorem leaf2064InnerLogValid :
    leaf2064InnerLog.Valid 8 (innerAD leaf2064Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint49PositiveFacts.valid leaf2064CoverageChecked

private noncomputable def leaf2064InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2064InputLogOnePlusV_eq :
    leaf2064InputLogOnePlusV = outerEnclosure 24
      (leaf2064Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2064RoundedFacts : LeafRoundedFacts 8
    leaf2064Certificate.logOnePlusV leaf2064InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2064InputLogOnePlusV_eq }

private noncomputable def leaf2064Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi176InputQChi innerPair153Input
    leaf2064InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2064LowerChecked :
    lowerCheck 24 leaf2064Box leaf2064Inputs = true := by
  rfl'

private theorem leaf2064CoversExact : CoversExact 8
    leaf2064Box leaf2064Certificate leaf2064InnerLog leaf2064Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi176RoundedFacts
    innerPair153RoundedFacts leaf2064RoundedFacts (by rfl)

private theorem leaf2064FlatSound : Sound leaf2064Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2064CertificateValid
    leaf2064InnerLogValid leaf2064CoversExact leaf2064LowerChecked

private noncomputable def leaf2065Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2065Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (808452867/808439296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (800800751/536870912) }, upper := { exponent := 0, mantissa := (12365/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1616892163/1616878592) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2065InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2065LocalValidity :
    LeafFacts leaf2065Box leaf2065Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2065Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (808452867/808439296) }) = true
      norm_num [leaf2065Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2065CertificateValid :
    WideCertificateValid leaf2065Box leaf2065Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi177ValidityFacts
    leaf2065LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2065CoverageChecked :
    coverageCheck (innerAD leaf2065Box) leaf2065InnerLog = true := by
  rfl'

private theorem leaf2065InnerLogValid :
    leaf2065InnerLog.Valid 8 (innerAD leaf2065Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2065CoverageChecked

private noncomputable def leaf2065InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2065InputLogOnePlusV_eq :
    leaf2065InputLogOnePlusV = outerEnclosure 24
      (leaf2065Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2065RoundedFacts : LeafRoundedFacts 8
    leaf2065Certificate.logOnePlusV leaf2065InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2065InputLogOnePlusV_eq }

private noncomputable def leaf2065Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi177InputQChi innerPair409Input
    leaf2065InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2065LowerChecked :
    lowerCheck 24 leaf2065Box leaf2065Inputs = true := by
  rfl'

private theorem leaf2065CoversExact : CoversExact 8
    leaf2065Box leaf2065Certificate leaf2065InnerLog leaf2065Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi177RoundedFacts
    innerPair409RoundedFacts leaf2065RoundedFacts (by rfl)

private theorem leaf2065FlatSound : Sound leaf2065Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2065CertificateValid
    leaf2065InnerLogValid leaf2065CoversExact leaf2065LowerChecked

private noncomputable def leaf2066Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2066Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905761792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (807747141/536870912) }, upper := { exponent := 0, mantissa := (1559/1024) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811926357/45811523584) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2066InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2066LocalValidity :
    LeafFacts leaf2066Box leaf2066Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2066Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905761792) }) = true
      norm_num [leaf2066Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2066CertificateValid :
    WideCertificateValid leaf2066Box leaf2066Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi178ValidityFacts
    leaf2066LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2066CoverageChecked :
    coverageCheck (innerAD leaf2066Box) leaf2066InnerLog = true := by
  rfl'

private theorem leaf2066InnerLogValid :
    leaf2066InnerLog.Valid 8 (innerAD leaf2066Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2066CoverageChecked

private noncomputable def leaf2066InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2066InputLogOnePlusV_eq :
    leaf2066InputLogOnePlusV = outerEnclosure 24
      (leaf2066Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2066RoundedFacts : LeafRoundedFacts 8
    leaf2066Certificate.logOnePlusV leaf2066InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2066InputLogOnePlusV_eq }

private noncomputable def leaf2066Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi178InputQChi innerPair44Input
    leaf2066InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2066LowerChecked :
    lowerCheck 24 leaf2066Box leaf2066Inputs = true := by
  rfl'

private theorem leaf2066CoversExact : CoversExact 8
    leaf2066Box leaf2066Certificate leaf2066InnerLog leaf2066Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi178RoundedFacts
    innerPair44RoundedFacts leaf2066RoundedFacts (by rfl)

private theorem leaf2066FlatSound : Sound leaf2066Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2066CertificateValid
    leaf2066InnerLogValid leaf2066CoversExact leaf2066LowerChecked

private noncomputable def leaf2067Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2067Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717320192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (803290965/536870912) }, upper := { exponent := 0, mantissa := (3101/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435813887/137434640384) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2067InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2067LocalValidity :
    LeafFacts leaf2067Box leaf2067Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2067Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717320192) }) = true
      norm_num [leaf2067Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2067CertificateValid :
    WideCertificateValid leaf2067Box leaf2067Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi177ValidityFacts
    leaf2067LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2067CoverageChecked :
    coverageCheck (innerAD leaf2067Box) leaf2067InnerLog = true := by
  rfl'

private theorem leaf2067InnerLogValid :
    leaf2067InnerLog.Valid 8 (innerAD leaf2067Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2067CoverageChecked

private noncomputable def leaf2067InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2067InputLogOnePlusV_eq :
    leaf2067InputLogOnePlusV = outerEnclosure 24
      (leaf2067Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2067RoundedFacts : LeafRoundedFacts 8
    leaf2067Certificate.logOnePlusV leaf2067InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2067InputLogOnePlusV_eq }

private noncomputable def leaf2067Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi177InputQChi innerPair409Input
    leaf2067InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2067LowerChecked :
    lowerCheck 24 leaf2067Box leaf2067Inputs = true := by
  rfl'

private theorem leaf2067CoversExact : CoversExact 8
    leaf2067Box leaf2067Certificate leaf2067InnerLog leaf2067Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi177RoundedFacts
    innerPair409RoundedFacts leaf2067RoundedFacts (by rfl)

private theorem leaf2067FlatSound : Sound leaf2067Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2067CertificateValid
    leaf2067InnerLogValid leaf2067CoversExact leaf2067LowerChecked

private noncomputable def leaf2068Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2068Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717264896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (810302887/536870912) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435758591/137434529792) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2068InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2068LocalValidity :
    LeafFacts leaf2068Box leaf2068Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2068Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717264896) }) = true
      norm_num [leaf2068Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2068CertificateValid :
    WideCertificateValid leaf2068Box leaf2068Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi178ValidityFacts
    leaf2068LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2068CoverageChecked :
    coverageCheck (innerAD leaf2068Box) leaf2068InnerLog = true := by
  rfl'

private theorem leaf2068InnerLogValid :
    leaf2068InnerLog.Valid 8 (innerAD leaf2068Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2068CoverageChecked

private noncomputable def leaf2068InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2068InputLogOnePlusV_eq :
    leaf2068InputLogOnePlusV = outerEnclosure 24
      (leaf2068Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2068RoundedFacts : LeafRoundedFacts 8
    leaf2068Certificate.logOnePlusV leaf2068InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2068InputLogOnePlusV_eq }

private noncomputable def leaf2068Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi178InputQChi innerPair44Input
    leaf2068InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2068LowerChecked :
    lowerCheck 24 leaf2068Box leaf2068Inputs = true := by
  rfl'

private theorem leaf2068CoversExact : CoversExact 8
    leaf2068Box leaf2068Certificate leaf2068InnerLog leaf2068Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi178RoundedFacts
    innerPair44RoundedFacts leaf2068RoundedFacts (by rfl)

private theorem leaf2068FlatSound : Sound leaf2068Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2068CertificateValid
    leaf2068InnerLogValid leaf2068CoversExact leaf2068LowerChecked

private noncomputable def leaf2069Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2069Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (763316455/536870912) }, upper := { exponent := 0, mantissa := (11789/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431987/268428262) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2069InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2069LocalValidity :
    LeafFacts leaf2069Box leaf2069Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2069Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214131) }) = true
      norm_num [leaf2069Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2069CertificateValid :
    WideCertificateValid leaf2069Box leaf2069Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi181ValidityFacts
    leaf2069LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2069CoverageChecked :
    coverageCheck (innerAD leaf2069Box) leaf2069InnerLog = true := by
  rfl'

private theorem leaf2069InnerLogValid :
    leaf2069InnerLog.Valid 8 (innerAD leaf2069Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2069CoverageChecked

private noncomputable def leaf2069InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2069InputLogOnePlusV_eq :
    leaf2069InputLogOnePlusV = outerEnclosure 24
      (leaf2069Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2069RoundedFacts : LeafRoundedFacts 8
    leaf2069Certificate.logOnePlusV leaf2069InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2069InputLogOnePlusV_eq }

private noncomputable def leaf2069Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi181InputQChi innerPair27Input
    leaf2069InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2069LowerChecked :
    lowerCheck 24 leaf2069Box leaf2069Inputs = true := by
  rfl'

private theorem leaf2069CoversExact : CoversExact 8
    leaf2069Box leaf2069Certificate leaf2069InnerLog leaf2069Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi181RoundedFacts
    innerPair27RoundedFacts leaf2069RoundedFacts (by rfl)

private theorem leaf2069FlatSound : Sound leaf2069Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2069CertificateValid
    leaf2069InnerLogValid leaf2069CoversExact leaf2069LowerChecked

private noncomputable def leaf2070Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2070Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107011) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (770393909/536870912) }, upper := { exponent := 0, mantissa := (5949/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215939/134214022) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2070InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2070LocalValidity :
    LeafFacts leaf2070Box leaf2070Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2070Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107011) }) = true
      norm_num [leaf2070Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2070CertificateValid :
    WideCertificateValid leaf2070Box leaf2070Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi182ValidityFacts
    leaf2070LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2070CoverageChecked :
    coverageCheck (innerAD leaf2070Box) leaf2070InnerLog = true := by
  rfl'

private theorem leaf2070InnerLogValid :
    leaf2070InnerLog.Valid 8 (innerAD leaf2070Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2070CoverageChecked

private noncomputable def leaf2070InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2070InputLogOnePlusV_eq :
    leaf2070InputLogOnePlusV = outerEnclosure 24
      (leaf2070Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2070RoundedFacts : LeafRoundedFacts 8
    leaf2070Certificate.logOnePlusV leaf2070InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2070InputLogOnePlusV_eq }

private noncomputable def leaf2070Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi182InputQChi innerPair27Input
    leaf2070InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2070LowerChecked :
    lowerCheck 24 leaf2070Box leaf2070Inputs = true := by
  rfl'

private theorem leaf2070CoversExact : CoversExact 8
    leaf2070Box leaf2070Certificate leaf2070InnerLog leaf2070Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi182RoundedFacts
    innerPair27RoundedFacts leaf2070RoundedFacts (by rfl)

private theorem leaf2070FlatSound : Sound leaf2070Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2070CertificateValid
    leaf2070InnerLogValid leaf2070CoversExact leaf2070LowerChecked

private noncomputable def leaf2071Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2071Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107049) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (765413477/536870912) }, upper := { exponent := 0, mantissa := (5911/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215977/134214098) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2071InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2071LocalValidity :
    LeafFacts leaf2071Box leaf2071Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2071Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107049) }) = true
      norm_num [leaf2071Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2071CertificateValid :
    WideCertificateValid leaf2071Box leaf2071Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi181ValidityFacts
    leaf2071LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2071CoverageChecked :
    coverageCheck (innerAD leaf2071Box) leaf2071InnerLog = true := by
  rfl'

private theorem leaf2071InnerLogValid :
    leaf2071InnerLog.Valid 8 (innerAD leaf2071Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2071CoverageChecked

private noncomputable def leaf2071InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2071InputLogOnePlusV_eq :
    leaf2071InputLogOnePlusV = outerEnclosure 24
      (leaf2071Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2071RoundedFacts : LeafRoundedFacts 8
    leaf2071Certificate.logOnePlusV leaf2071InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2071InputLogOnePlusV_eq }

private noncomputable def leaf2071Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi181InputQChi innerPair27Input
    leaf2071InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2071LowerChecked :
    lowerCheck 24 leaf2071Box leaf2071Inputs = true := by
  rfl'

private theorem leaf2071CoversExact : CoversExact 8
    leaf2071Box leaf2071Certificate leaf2071InnerLog leaf2071Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi181RoundedFacts
    innerPair27RoundedFacts leaf2071RoundedFacts (by rfl)

private theorem leaf2071FlatSound : Sound leaf2071Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2071CertificateValid
    leaf2071InnerLogValid leaf2071CoversExact leaf2071LowerChecked

private noncomputable def leaf2072Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2072Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553497) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (772556463/536870912) }, upper := { exponent := 0, mantissa := (2983/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107961/67106994) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2072InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2072LocalValidity :
    LeafFacts leaf2072Box leaf2072Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2072Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553497) }) = true
      norm_num [leaf2072Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2072CertificateValid :
    WideCertificateValid leaf2072Box leaf2072Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi182ValidityFacts
    leaf2072LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2072CoverageChecked :
    coverageCheck (innerAD leaf2072Box) leaf2072InnerLog = true := by
  rfl'

private theorem leaf2072InnerLogValid :
    leaf2072InnerLog.Valid 8 (innerAD leaf2072Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2072CoverageChecked

private noncomputable def leaf2072InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2072InputLogOnePlusV_eq :
    leaf2072InputLogOnePlusV = outerEnclosure 24
      (leaf2072Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2072RoundedFacts : LeafRoundedFacts 8
    leaf2072Certificate.logOnePlusV leaf2072InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2072InputLogOnePlusV_eq }

private noncomputable def leaf2072Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi182InputQChi innerPair34Input
    leaf2072InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2072LowerChecked :
    lowerCheck 24 leaf2072Box leaf2072Inputs = true := by
  rfl'

private theorem leaf2072CoversExact : CoversExact 8
    leaf2072Box leaf2072Certificate leaf2072InnerLog leaf2072Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi182RoundedFacts
    innerPair34RoundedFacts leaf2072RoundedFacts (by rfl)

private theorem leaf2072FlatSound : Sound leaf2072Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2072CertificateValid
    leaf2072InnerLogValid leaf2072CoversExact leaf2072LowerChecked

private noncomputable def leaf2073Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2073Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213913) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (777471363/536870912) }, upper := { exponent := 0, mantissa := (12007/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431769/268427826) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2073InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2073LocalValidity :
    LeafFacts leaf2073Box leaf2073Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2073Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213913) }) = true
      norm_num [leaf2073Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2073CertificateValid :
    WideCertificateValid leaf2073Box leaf2073Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi179ValidityFacts
    leaf2073LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2073CoverageChecked :
    coverageCheck (innerAD leaf2073Box) leaf2073InnerLog = true := by
  rfl'

private theorem leaf2073InnerLogValid :
    leaf2073InnerLog.Valid 8 (innerAD leaf2073Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2073CoverageChecked

private noncomputable def leaf2073InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2073InputLogOnePlusV_eq :
    leaf2073InputLogOnePlusV = outerEnclosure 24
      (leaf2073Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2073RoundedFacts : LeafRoundedFacts 8
    leaf2073Certificate.logOnePlusV leaf2073InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2073InputLogOnePlusV_eq }

private noncomputable def leaf2073Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2073InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2073LowerChecked :
    lowerCheck 24 leaf2073Box leaf2073Inputs = true := by
  rfl'

private theorem leaf2073CoversExact : CoversExact 8
    leaf2073Box leaf2073Certificate leaf2073InnerLog leaf2073Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2073RoundedFacts (by rfl)

private theorem leaf2073FlatSound : Sound leaf2073Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2073CertificateValid
    leaf2073InnerLogValid leaf2073CoversExact leaf2073LowerChecked

private noncomputable def leaf2074Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2074Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553451) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (784548817/536870912) }, upper := { exponent := 0, mantissa := (3029/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67107915/67106902) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2074InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2074LocalValidity :
    LeafFacts leaf2074Box leaf2074Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2074Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553451) }) = true
      norm_num [leaf2074Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2074CertificateValid :
    WideCertificateValid leaf2074Box leaf2074Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi180ValidityFacts
    leaf2074LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2074CoverageChecked :
    coverageCheck (innerAD leaf2074Box) leaf2074InnerLog = true := by
  rfl'

private theorem leaf2074InnerLogValid :
    leaf2074InnerLog.Valid 8 (innerAD leaf2074Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2074CoverageChecked

private noncomputable def leaf2074InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2074InputLogOnePlusV_eq :
    leaf2074InputLogOnePlusV = outerEnclosure 24
      (leaf2074Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2074RoundedFacts : LeafRoundedFacts 8
    leaf2074Certificate.logOnePlusV leaf2074InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2074InputLogOnePlusV_eq }

private noncomputable def leaf2074Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2074InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2074LowerChecked :
    lowerCheck 24 leaf2074Box leaf2074Inputs = true := by
  rfl'

private theorem leaf2074CoversExact : CoversExact 8
    leaf2074Box leaf2074Certificate leaf2074InnerLog leaf2074Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2074RoundedFacts (by rfl)

private theorem leaf2074FlatSound : Sound leaf2074Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2074CertificateValid
    leaf2074InnerLogValid leaf2074CoversExact leaf2074LowerChecked

private noncomputable def leaf2075Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2075Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (3947584/3947467) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (779699449/536870912) }, upper := { exponent := 0, mantissa := (6021/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (7895051/7894934) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2075InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2075LocalValidity :
    LeafFacts leaf2075Box leaf2075Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2075Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3947584/3947467) }) = true
      norm_num [leaf2075Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2075CertificateValid :
    WideCertificateValid leaf2075Box leaf2075Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi179ValidityFacts
    leaf2075LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2075CoverageChecked :
    coverageCheck (innerAD leaf2075Box) leaf2075InnerLog = true := by
  rfl'

private theorem leaf2075InnerLogValid :
    leaf2075InnerLog.Valid 8 (innerAD leaf2075Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2075CoverageChecked

private noncomputable def leaf2075InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2075InputLogOnePlusV_eq :
    leaf2075InputLogOnePlusV = outerEnclosure 24
      (leaf2075Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2075RoundedFacts : LeafRoundedFacts 8
    leaf2075Certificate.logOnePlusV leaf2075InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2075InputLogOnePlusV_eq }

private noncomputable def leaf2075Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2075InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2075LowerChecked :
    lowerCheck 24 leaf2075Box leaf2075Inputs = true := by
  rfl'

private theorem leaf2075CoversExact : CoversExact 8
    leaf2075Box leaf2075Certificate leaf2075InnerLog leaf2075Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2075RoundedFacts (by rfl)

private theorem leaf2075FlatSound : Sound leaf2075Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2075CertificateValid
    leaf2075InnerLogValid leaf2075CoversExact leaf2075LowerChecked

private noncomputable def leaf2076Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2076Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776721) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (786842435/536870912) }, upper := { exponent := 0, mantissa := (1519/1024) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33553953/33553442) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2076InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2076LocalValidity :
    LeafFacts leaf2076Box leaf2076Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2076Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776721) }) = true
      norm_num [leaf2076Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2076CertificateValid :
    WideCertificateValid leaf2076Box leaf2076Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi180ValidityFacts
    leaf2076LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2076CoverageChecked :
    coverageCheck (innerAD leaf2076Box) leaf2076InnerLog = true := by
  rfl'

private theorem leaf2076InnerLogValid :
    leaf2076InnerLog.Valid 8 (innerAD leaf2076Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2076CoverageChecked

private noncomputable def leaf2076InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2076InputLogOnePlusV_eq :
    leaf2076InputLogOnePlusV = outerEnclosure 24
      (leaf2076Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2076RoundedFacts : LeafRoundedFacts 8
    leaf2076Certificate.logOnePlusV leaf2076InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2076InputLogOnePlusV_eq }

private noncomputable def leaf2076Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2076InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2076LowerChecked :
    lowerCheck 24 leaf2076Box leaf2076Inputs = true := by
  rfl'

private theorem leaf2076CoversExact : CoversExact 8
    leaf2076Box leaf2076Certificate leaf2076InnerLog leaf2076Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2076RoundedFacts (by rfl)

private theorem leaf2076FlatSound : Sound leaf2076Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2076CertificateValid
    leaf2076InnerLogValid leaf2076CoversExact leaf2076LowerChecked

private noncomputable def leaf2077Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2077Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (7895168/7894945) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (767510499/536870912) }, upper := { exponent := 0, mantissa := (11855/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (15790113/15789890) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2077InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf2077LocalValidity :
    LeafFacts leaf2077Box leaf2077Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2077Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (7895168/7894945) }) = true
      norm_num [leaf2077Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2077CertificateValid :
    WideCertificateValid leaf2077Box leaf2077Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi181ValidityFacts
    leaf2077LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2077CoverageChecked :
    coverageCheck (innerAD leaf2077Box) leaf2077InnerLog = true := by
  rfl'

private theorem leaf2077InnerLogValid :
    leaf2077InnerLog.Valid 8 (innerAD leaf2077Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf2077CoverageChecked

private noncomputable def leaf2077InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814659/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2077InputLogOnePlusV_eq :
    leaf2077InputLogOnePlusV = outerEnclosure 24
      (leaf2077Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2077RoundedFacts : LeafRoundedFacts 8
    leaf2077Certificate.logOnePlusV leaf2077InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2077InputLogOnePlusV_eq }

private noncomputable def leaf2077Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi181InputQChi innerPair27Input
    leaf2077InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2077LowerChecked :
    lowerCheck 24 leaf2077Box leaf2077Inputs = true := by
  rfl'

private theorem leaf2077CoversExact : CoversExact 8
    leaf2077Box leaf2077Certificate leaf2077InnerLog leaf2077Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi181RoundedFacts
    innerPair27RoundedFacts leaf2077RoundedFacts (by rfl)

private theorem leaf2077FlatSound : Sound leaf2077Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2077CertificateValid
    leaf2077InnerLogValid leaf2077CoversExact leaf2077LowerChecked

private noncomputable def leaf2078Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2078Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67106977) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (774719017/536870912) }, upper := { exponent := 0, mantissa := (5983/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134215905/134213954) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2078InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2078LocalValidity :
    LeafFacts leaf2078Box leaf2078Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2078Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67106977) }) = true
      norm_num [leaf2078Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2078CertificateValid :
    WideCertificateValid leaf2078Box leaf2078Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi182ValidityFacts
    leaf2078LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2078CoverageChecked :
    coverageCheck (innerAD leaf2078Box) leaf2078InnerLog = true := by
  rfl'

private theorem leaf2078InnerLogValid :
    leaf2078InnerLog.Valid 8 (innerAD leaf2078Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2078CoverageChecked

private noncomputable def leaf2078InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2078InputLogOnePlusV_eq :
    leaf2078InputLogOnePlusV = outerEnclosure 24
      (leaf2078Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2078RoundedFacts : LeafRoundedFacts 8
    leaf2078Certificate.logOnePlusV leaf2078InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2078InputLogOnePlusV_eq }

private noncomputable def leaf2078Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi182InputQChi innerPair34Input
    leaf2078InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2078LowerChecked :
    lowerCheck 24 leaf2078Box leaf2078Inputs = true := by
  rfl'

private theorem leaf2078CoversExact : CoversExact 8
    leaf2078Box leaf2078Certificate leaf2078InnerLog leaf2078Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi182RoundedFacts
    innerPair34RoundedFacts leaf2078RoundedFacts (by rfl)

private theorem leaf2078FlatSound : Sound leaf2078Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2078CertificateValid
    leaf2078InnerLogValid leaf2078CoversExact leaf2078LowerChecked

private noncomputable def leaf2079Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (1/8), chiHi := (33/256) }

private noncomputable def leaf2079Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388377) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (769607521/536870912) }, upper := { exponent := 0, mantissa := (743/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi181LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16776993/16776754) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2079InnerLog : WideLogData :=
  innerPair405Data

set_option maxRecDepth 1000000 in
private theorem leaf2079LocalValidity :
    LeafFacts leaf2079Box leaf2079Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2079Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388377) }) = true
      norm_num [leaf2079Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2079CertificateValid :
    WideCertificateValid leaf2079Box leaf2079Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi181ValidityFacts
    leaf2079LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2079CoverageChecked :
    coverageCheck (innerAD leaf2079Box) leaf2079InnerLog = true := by
  rfl'

private theorem leaf2079InnerLogValid :
    leaf2079InnerLog.Valid 8 (innerAD leaf2079Box) :=
  wideLogDataValid_of_cachedCheck endpoint119PositiveFacts
    endpoint41PositiveFacts.valid leaf2079CoverageChecked

private noncomputable def leaf2079InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2079InputLogOnePlusV_eq :
    leaf2079InputLogOnePlusV = outerEnclosure 24
      (leaf2079Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2079RoundedFacts : LeafRoundedFacts 8
    leaf2079Certificate.logOnePlusV leaf2079InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2079InputLogOnePlusV_eq }

private noncomputable def leaf2079Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi181InputQChi innerPair405Input
    leaf2079InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2079LowerChecked :
    lowerCheck 24 leaf2079Box leaf2079Inputs = true := by
  rfl'

private theorem leaf2079CoversExact : CoversExact 8
    leaf2079Box leaf2079Certificate leaf2079InnerLog leaf2079Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi181RoundedFacts
    innerPair405RoundedFacts leaf2079RoundedFacts (by rfl)

private theorem leaf2079FlatSound : Sound leaf2079Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2079CertificateValid
    leaf2079InnerLogValid leaf2079CoversExact leaf2079LowerChecked

private noncomputable def leaf2080Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (33/256), chiHi := (17/128) }

private noncomputable def leaf2080Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194185) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (776881571/536870912) }, upper := { exponent := 0, mantissa := (375/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi182LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388493/8388370) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2080InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2080LocalValidity :
    LeafFacts leaf2080Box leaf2080Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2080Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194185) }) = true
      norm_num [leaf2080Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2080CertificateValid :
    WideCertificateValid leaf2080Box leaf2080Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi182ValidityFacts
    leaf2080LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2080CoverageChecked :
    coverageCheck (innerAD leaf2080Box) leaf2080InnerLog = true := by
  rfl'

private theorem leaf2080InnerLogValid :
    leaf2080InnerLog.Valid 8 (innerAD leaf2080Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2080CoverageChecked

private noncomputable def leaf2080InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2080InputLogOnePlusV_eq :
    leaf2080InputLogOnePlusV = outerEnclosure 24
      (leaf2080Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2080RoundedFacts : LeafRoundedFacts 8
    leaf2080Certificate.logOnePlusV leaf2080InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2080InputLogOnePlusV_eq }

private noncomputable def leaf2080Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi182InputQChi innerPair34Input
    leaf2080InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2080LowerChecked :
    lowerCheck 24 leaf2080Box leaf2080Inputs = true := by
  rfl'

private theorem leaf2080CoversExact : CoversExact 8
    leaf2080Box leaf2080Certificate leaf2080InnerLog leaf2080Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi182RoundedFacts
    innerPair34RoundedFacts leaf2080RoundedFacts (by rfl)

private theorem leaf2080FlatSound : Sound leaf2080Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2080CertificateValid
    leaf2080InnerLogValid leaf2080CoversExact leaf2080LowerChecked

private noncomputable def leaf2081Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2081Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134213843) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (781927535/536870912) }, upper := { exponent := 0, mantissa := (12077/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268431699/268427686) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2081InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2081LocalValidity :
    LeafFacts leaf2081Box leaf2081Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2081Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134213843) }) = true
      norm_num [leaf2081Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2081CertificateValid :
    WideCertificateValid leaf2081Box leaf2081Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi179ValidityFacts
    leaf2081LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2081CoverageChecked :
    coverageCheck (innerAD leaf2081Box) leaf2081InnerLog = true := by
  rfl'

private theorem leaf2081InnerLogValid :
    leaf2081InnerLog.Valid 8 (innerAD leaf2081Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2081CoverageChecked

private noncomputable def leaf2081InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2081InputLogOnePlusV_eq :
    leaf2081InputLogOnePlusV = outerEnclosure 24
      (leaf2081Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2081RoundedFacts : LeafRoundedFacts 8
    leaf2081Certificate.logOnePlusV leaf2081InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2081InputLogOnePlusV_eq }

private noncomputable def leaf2081Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2081InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2081LowerChecked :
    lowerCheck 24 leaf2081Box leaf2081Inputs = true := by
  rfl'

private theorem leaf2081CoversExact : CoversExact 8
    leaf2081Box leaf2081Certificate leaf2081InnerLog leaf2081Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2081RoundedFacts (by rfl)

private theorem leaf2081FlatSound : Sound leaf2081Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2081CertificateValid
    leaf2081InnerLogValid leaf2081CoversExact leaf2081LowerChecked

private noncomputable def leaf2082Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2082Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717430784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (789136053/536870912) }, upper := { exponent := 0, mantissa := (3047/2048) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435924479/137434861568) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2082InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2082LocalValidity :
    LeafFacts leaf2082Box leaf2082Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2082Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717430784) }) = true
      norm_num [leaf2082Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2082CertificateValid :
    WideCertificateValid leaf2082Box leaf2082Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi180ValidityFacts
    leaf2082LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2082CoverageChecked :
    coverageCheck (innerAD leaf2082Box) leaf2082InnerLog = true := by
  rfl'

private theorem leaf2082InnerLogValid :
    leaf2082InnerLog.Valid 8 (innerAD leaf2082Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2082CoverageChecked

private noncomputable def leaf2082InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2082InputLogOnePlusV_eq :
    leaf2082InputLogOnePlusV = outerEnclosure 24
      (leaf2082Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2082RoundedFacts : LeafRoundedFacts 8
    leaf2082Certificate.logOnePlusV leaf2082InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2082InputLogOnePlusV_eq }

private noncomputable def leaf2082Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2082InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2082LowerChecked :
    lowerCheck 24 leaf2082Box leaf2082Inputs = true := by
  rfl'

private theorem leaf2082CoversExact : CoversExact 8
    leaf2082Box leaf2082Certificate leaf2082InnerLog leaf2082Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2082RoundedFacts (by rfl)

private theorem leaf2082FlatSound : Sound leaf2082Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2082CertificateValid
    leaf2082InnerLogValid leaf2082CoversExact leaf2082LowerChecked

private noncomputable def leaf2083Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (17/128), chiHi := (35/256) }

private noncomputable def leaf2083Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388363) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (784155621/536870912) }, upper := { exponent := 0, mantissa := (757/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi179LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16776979/16776726) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2083InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2083LocalValidity :
    LeafFacts leaf2083Box leaf2083Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2083Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388363) }) = true
      norm_num [leaf2083Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2083CertificateValid :
    WideCertificateValid leaf2083Box leaf2083Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi179ValidityFacts
    leaf2083LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2083CoverageChecked :
    coverageCheck (innerAD leaf2083Box) leaf2083InnerLog = true := by
  rfl'

private theorem leaf2083InnerLogValid :
    leaf2083InnerLog.Valid 8 (innerAD leaf2083Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2083CoverageChecked

private noncomputable def leaf2083InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814667/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2083InputLogOnePlusV_eq :
    leaf2083InputLogOnePlusV = outerEnclosure 24
      (leaf2083Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2083RoundedFacts : LeafRoundedFacts 8
    leaf2083Certificate.logOnePlusV leaf2083InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2083InputLogOnePlusV_eq }

private noncomputable def leaf2083Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi179InputQChi innerPair34Input
    leaf2083InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2083LowerChecked :
    lowerCheck 24 leaf2083Box leaf2083Inputs = true := by
  rfl'

private theorem leaf2083CoversExact : CoversExact 8
    leaf2083Box leaf2083Certificate leaf2083InnerLog leaf2083Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi179RoundedFacts
    innerPair34RoundedFacts leaf2083RoundedFacts (by rfl)

private theorem leaf2083FlatSound : Sound leaf2083Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2083CertificateValid
    leaf2083InnerLogValid leaf2083CoversExact leaf2083LowerChecked

private noncomputable def leaf2084Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2084Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717412352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (791429671/536870912) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435906047/137434824704) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2084InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2084LocalValidity :
    LeafFacts leaf2084Box leaf2084Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2084Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717412352) }) = true
      norm_num [leaf2084Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2084CertificateValid :
    WideCertificateValid leaf2084Box leaf2084Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi180ValidityFacts
    leaf2084LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2084CoverageChecked :
    coverageCheck (innerAD leaf2084Box) leaf2084InnerLog = true := by
  rfl'

private theorem leaf2084InnerLogValid :
    leaf2084InnerLog.Valid 8 (innerAD leaf2084Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2084CoverageChecked

private noncomputable def leaf2084InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2084InputLogOnePlusV_eq :
    leaf2084InputLogOnePlusV = outerEnclosure 24
      (leaf2084Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2084RoundedFacts : LeafRoundedFacts 8
    leaf2084Certificate.logOnePlusV leaf2084InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2084InputLogOnePlusV_eq }

private noncomputable def leaf2084Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi180InputQChi innerPair34Input
    leaf2084InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2084LowerChecked :
    lowerCheck 24 leaf2084Box leaf2084Inputs = true := by
  rfl'

private theorem leaf2084CoversExact : CoversExact 8
    leaf2084Box leaf2084Certificate leaf2084InnerLog leaf2084Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi180RoundedFacts
    innerPair34RoundedFacts leaf2084RoundedFacts (by rfl)

private theorem leaf2084FlatSound : Sound leaf2084Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2084CertificateValid
    leaf2084InnerLogValid leaf2084CoversExact leaf2084LowerChecked

private noncomputable def leaf2085Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2085Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743482368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (791626271/536870912) }, upper := { exponent := 0, mantissa := (12225/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487181107/27486964736) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2085InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2085LocalValidity :
    LeafFacts leaf2085Box leaf2085Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2085Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743482368) }) = true
      norm_num [leaf2085Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2085CertificateValid :
    WideCertificateValid leaf2085Box leaf2085Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi175ValidityFacts
    leaf2085LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2085CoverageChecked :
    coverageCheck (innerAD leaf2085Box) leaf2085InnerLog = true := by
  rfl'

private theorem leaf2085InnerLogValid :
    leaf2085InnerLog.Valid 8 (innerAD leaf2085Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2085CoverageChecked

private noncomputable def leaf2085InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2085InputLogOnePlusV_eq :
    leaf2085InputLogOnePlusV = outerEnclosure 24
      (leaf2085Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2085RoundedFacts : LeafRoundedFacts 8
    leaf2085Certificate.logOnePlusV leaf2085InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2085InputLogOnePlusV_eq }

private noncomputable def leaf2085Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi175InputQChi innerPair34Input
    leaf2085InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2085LowerChecked :
    lowerCheck 24 leaf2085Box leaf2085Inputs = true := by
  rfl'

private theorem leaf2085CoversExact : CoversExact 8
    leaf2085Box leaf2085Certificate leaf2085InnerLog leaf2085Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf2085RoundedFacts (by rfl)

private theorem leaf2085FlatSound : Sound leaf2085Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2085CertificateValid
    leaf2085InnerLogValid leaf2085CoversExact leaf2085LowerChecked

private noncomputable def leaf2086Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2086Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905785344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (798703725/536870912) }, upper := { exponent := 0, mantissa := (6167/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811949909/45811570688) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2086InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2086LocalValidity :
    LeafFacts leaf2086Box leaf2086Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2086Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905785344) }) = true
      norm_num [leaf2086Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2086CertificateValid :
    WideCertificateValid leaf2086Box leaf2086Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi176ValidityFacts
    leaf2086LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2086CoverageChecked :
    coverageCheck (innerAD leaf2086Box) leaf2086InnerLog = true := by
  rfl'

private theorem leaf2086InnerLogValid :
    leaf2086InnerLog.Valid 8 (innerAD leaf2086Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2086CoverageChecked

private noncomputable def leaf2086InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2086InputLogOnePlusV_eq :
    leaf2086InputLogOnePlusV = outerEnclosure 24
      (leaf2086Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2086RoundedFacts : LeafRoundedFacts 8
    leaf2086Certificate.logOnePlusV leaf2086InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2086InputLogOnePlusV_eq }

private noncomputable def leaf2086Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi176InputQChi innerPair409Input
    leaf2086InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2086LowerChecked :
    lowerCheck 24 leaf2086Box leaf2086Inputs = true := by
  rfl'

private theorem leaf2086CoversExact : CoversExact 8
    leaf2086Box leaf2086Certificate leaf2086InnerLog leaf2086Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi176RoundedFacts
    innerPair409RoundedFacts leaf2086RoundedFacts (by rfl)

private theorem leaf2086FlatSound : Sound leaf2086Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2086CertificateValid
    leaf2086InnerLogValid leaf2086CoversExact leaf2086LowerChecked

private noncomputable def leaf2087Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2087Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905797632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (793985421/536870912) }, upper := { exponent := 0, mantissa := (6131/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811962197/45811595264) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2087InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2087LocalValidity :
    LeafFacts leaf2087Box leaf2087Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2087Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905797632) }) = true
      norm_num [leaf2087Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2087CertificateValid :
    WideCertificateValid leaf2087Box leaf2087Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi175ValidityFacts
    leaf2087LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2087CoverageChecked :
    coverageCheck (innerAD leaf2087Box) leaf2087InnerLog = true := by
  rfl'

private theorem leaf2087InnerLogValid :
    leaf2087InnerLog.Valid 8 (innerAD leaf2087Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2087CoverageChecked

private noncomputable def leaf2087InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2087InputLogOnePlusV_eq :
    leaf2087InputLogOnePlusV = outerEnclosure 24
      (leaf2087Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2087RoundedFacts : LeafRoundedFacts 8
    leaf2087Certificate.logOnePlusV leaf2087InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2087InputLogOnePlusV_eq }

private noncomputable def leaf2087Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi175InputQChi innerPair34Input
    leaf2087InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2087LowerChecked :
    lowerCheck 24 leaf2087Box leaf2087Inputs = true := by
  rfl'

private theorem leaf2087CoversExact : CoversExact 8
    leaf2087Box leaf2087Certificate leaf2087InnerLog leaf2087Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi175RoundedFacts
    innerPair34RoundedFacts leaf2087RoundedFacts (by rfl)

private theorem leaf2087FlatSound : Sound leaf2087Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2087CertificateValid
    leaf2087InnerLogValid leaf2087CoversExact leaf2087LowerChecked

private noncomputable def leaf2088Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2088Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717336576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (801128407/536870912) }, upper := { exponent := 0, mantissa := (3093/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435830271/137434673152) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2088InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2088LocalValidity :
    LeafFacts leaf2088Box leaf2088Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2088Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717336576) }) = true
      norm_num [leaf2088Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2088CertificateValid :
    WideCertificateValid leaf2088Box leaf2088Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi176ValidityFacts
    leaf2088LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2088CoverageChecked :
    coverageCheck (innerAD leaf2088Box) leaf2088InnerLog = true := by
  rfl'

private theorem leaf2088InnerLogValid :
    leaf2088InnerLog.Valid 8 (innerAD leaf2088Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2088CoverageChecked

private noncomputable def leaf2088InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2088InputLogOnePlusV_eq :
    leaf2088InputLogOnePlusV = outerEnclosure 24
      (leaf2088Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2088RoundedFacts : LeafRoundedFacts 8
    leaf2088Certificate.logOnePlusV leaf2088InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2088InputLogOnePlusV_eq }

private noncomputable def leaf2088Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi176InputQChi innerPair409Input
    leaf2088InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2088LowerChecked :
    lowerCheck 24 leaf2088Box leaf2088Inputs = true := by
  rfl'

private theorem leaf2088CoversExact : CoversExact 8
    leaf2088Box leaf2088Certificate leaf2088InnerLog leaf2088Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi176RoundedFacts
    innerPair409RoundedFacts leaf2088RoundedFacts (by rfl)

private theorem leaf2088FlatSound : Sound leaf2088Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2088CertificateValid
    leaf2088InnerLogValid leaf2088CoversExact leaf2088LowerChecked

private noncomputable def leaf2089Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2089Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717300224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (805781179/536870912) }, upper := { exponent := 0, mantissa := (12443/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435793919/137434600448) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2089InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2089LocalValidity :
    LeafFacts leaf2089Box leaf2089Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2089Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717300224) }) = true
      norm_num [leaf2089Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2089CertificateValid :
    WideCertificateValid leaf2089Box leaf2089Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi177ValidityFacts
    leaf2089LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2089CoverageChecked :
    coverageCheck (innerAD leaf2089Box) leaf2089InnerLog = true := by
  rfl'

private theorem leaf2089InnerLogValid :
    leaf2089InnerLog.Valid 8 (innerAD leaf2089Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2089CoverageChecked

private noncomputable def leaf2089InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2089InputLogOnePlusV_eq :
    leaf2089InputLogOnePlusV = outerEnclosure 24
      (leaf2089Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2089RoundedFacts : LeafRoundedFacts 8
    leaf2089Certificate.logOnePlusV leaf2089InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2089InputLogOnePlusV_eq }

private noncomputable def leaf2089Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi177InputQChi innerPair44Input
    leaf2089InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2089LowerChecked :
    lowerCheck 24 leaf2089Box leaf2089Inputs = true := by
  rfl'

private theorem leaf2089CoversExact : CoversExact 8
    leaf2089Box leaf2089Certificate leaf2089InnerLog leaf2089Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi177RoundedFacts
    innerPair44RoundedFacts leaf2089RoundedFacts (by rfl)

private theorem leaf2089FlatSound : Sound leaf2089Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2089CertificateValid
    leaf2089InnerLogValid leaf2089CoversExact leaf2089LowerChecked

private noncomputable def leaf2090Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2090Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042190848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (812858633/536870912) }, upper := { exponent := 0, mantissa := (1569/1024) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084455183/8084381696) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf2090InnerLog : WideLogData :=
  innerPair45Data

set_option maxRecDepth 1000000 in
private theorem leaf2090LocalValidity :
    LeafFacts leaf2090Box leaf2090Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2090Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042190848) }) = true
      norm_num [leaf2090Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2090CertificateValid :
    WideCertificateValid leaf2090Box leaf2090Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi178ValidityFacts
    leaf2090LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2090CoverageChecked :
    coverageCheck (innerAD leaf2090Box) leaf2090InnerLog = true := by
  rfl'

private theorem leaf2090InnerLogValid :
    leaf2090InnerLog.Valid 8 (innerAD leaf2090Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint43PositiveFacts.valid leaf2090CoverageChecked

private noncomputable def leaf2090InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2090InputLogOnePlusV_eq :
    leaf2090InputLogOnePlusV = outerEnclosure 24
      (leaf2090Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2090RoundedFacts : LeafRoundedFacts 8
    leaf2090Certificate.logOnePlusV leaf2090InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2090InputLogOnePlusV_eq }

private noncomputable def leaf2090Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi178InputQChi innerPair45Input
    leaf2090InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2090LowerChecked :
    lowerCheck 24 leaf2090Box leaf2090Inputs = true := by
  rfl'

private theorem leaf2090CoversExact : CoversExact 8
    leaf2090Box leaf2090Certificate leaf2090InnerLog leaf2090Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi178RoundedFacts
    innerPair45RoundedFacts leaf2090RoundedFacts (by rfl)

private theorem leaf2090FlatSound : Sound leaf2090Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2090CertificateValid
    leaf2090InnerLogValid leaf2090CoversExact leaf2090LowerChecked

private noncomputable def leaf2091Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2091Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717280256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (808271393/536870912) }, upper := { exponent := 0, mantissa := (6241/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435773951/137434560512) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2091InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2091LocalValidity :
    LeafFacts leaf2091Box leaf2091Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2091Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717280256) }) = true
      norm_num [leaf2091Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2091CertificateValid :
    WideCertificateValid leaf2091Box leaf2091Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi177ValidityFacts
    leaf2091LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2091CoverageChecked :
    coverageCheck (innerAD leaf2091Box) leaf2091InnerLog = true := by
  rfl'

private theorem leaf2091InnerLogValid :
    leaf2091InnerLog.Valid 8 (innerAD leaf2091Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2091CoverageChecked

private noncomputable def leaf2091InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2091InputLogOnePlusV_eq :
    leaf2091InputLogOnePlusV = outerEnclosure 24
      (leaf2091Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2091RoundedFacts : LeafRoundedFacts 8
    leaf2091Certificate.logOnePlusV leaf2091InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2091InputLogOnePlusV_eq }

private noncomputable def leaf2091Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi177InputQChi innerPair44Input
    leaf2091InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2091LowerChecked :
    lowerCheck 24 leaf2091Box leaf2091Inputs = true := by
  rfl'

private theorem leaf2091CoversExact : CoversExact 8
    leaf2091Box leaf2091Certificate leaf2091InnerLog leaf2091Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi177RoundedFacts
    innerPair44RoundedFacts leaf2091RoundedFacts (by rfl)

private theorem leaf2091FlatSound : Sound leaf2091Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2091CertificateValid
    leaf2091InnerLogValid leaf2091CoversExact leaf2091LowerChecked

private noncomputable def leaf2092Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2092Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905741312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (815414379/536870912) }, upper := { exponent := 0, mantissa := (787/512) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811905877/45811482624) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf2092InnerLog : WideLogData :=
  innerPair177Data

set_option maxRecDepth 1000000 in
private theorem leaf2092LocalValidity :
    LeafFacts leaf2092Box leaf2092Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2092Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905741312) }) = true
      norm_num [leaf2092Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2092CertificateValid :
    WideCertificateValid leaf2092Box leaf2092Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi178ValidityFacts
    leaf2092LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2092CoverageChecked :
    coverageCheck (innerAD leaf2092Box) leaf2092InnerLog = true := by
  rfl'

private theorem leaf2092InnerLogValid :
    leaf2092InnerLog.Valid 8 (innerAD leaf2092Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint43PositiveFacts.valid leaf2092CoverageChecked

private noncomputable def leaf2092InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2092InputLogOnePlusV_eq :
    leaf2092InputLogOnePlusV = outerEnclosure 24
      (leaf2092Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2092RoundedFacts : LeafRoundedFacts 8
    leaf2092Certificate.logOnePlusV leaf2092InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2092InputLogOnePlusV_eq }

private noncomputable def leaf2092Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi178InputQChi innerPair177Input
    leaf2092InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2092LowerChecked :
    lowerCheck 24 leaf2092Box leaf2092Inputs = true := by
  rfl'

private theorem leaf2092CoversExact : CoversExact 8
    leaf2092Box leaf2092Certificate leaf2092InnerLog leaf2092Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi178RoundedFacts
    innerPair177RoundedFacts leaf2092RoundedFacts (by rfl)

private theorem leaf2092FlatSound : Sound leaf2092Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2092CertificateValid
    leaf2092InnerLogValid leaf2092CoversExact leaf2092LowerChecked

private noncomputable def leaf2093Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2093Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717373952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (796344571/536870912) }, upper := { exponent := 0, mantissa := (12299/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435867647/137434747904) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2093InnerLog : WideLogData :=
  innerPair153Data

set_option maxRecDepth 1000000 in
private theorem leaf2093LocalValidity :
    LeafFacts leaf2093Box leaf2093Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2093Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717373952) }) = true
      norm_num [leaf2093Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2093CertificateValid :
    WideCertificateValid leaf2093Box leaf2093Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi175ValidityFacts
    leaf2093LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2093CoverageChecked :
    coverageCheck (innerAD leaf2093Box) leaf2093InnerLog = true := by
  rfl'

private theorem leaf2093InnerLogValid :
    leaf2093InnerLog.Valid 8 (innerAD leaf2093Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint49PositiveFacts.valid leaf2093CoverageChecked

private noncomputable def leaf2093InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2093InputLogOnePlusV_eq :
    leaf2093InputLogOnePlusV = outerEnclosure 24
      (leaf2093Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2093RoundedFacts : LeafRoundedFacts 8
    leaf2093Certificate.logOnePlusV leaf2093InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2093InputLogOnePlusV_eq }

private noncomputable def leaf2093Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi175InputQChi innerPair153Input
    leaf2093InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2093LowerChecked :
    lowerCheck 24 leaf2093Box leaf2093Inputs = true := by
  rfl'

private theorem leaf2093CoversExact : CoversExact 8
    leaf2093Box leaf2093Certificate leaf2093InnerLog leaf2093Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi175RoundedFacts
    innerPair153RoundedFacts leaf2093RoundedFacts (by rfl)

private theorem leaf2093FlatSound : Sound leaf2093Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2093CertificateValid
    leaf2093InnerLogValid leaf2093CoversExact leaf2093LowerChecked

private noncomputable def leaf2094Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2094Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743463424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (803553089/536870912) }, upper := { exponent := 0, mantissa := (6205/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487162163/27486926848) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2094InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2094LocalValidity :
    LeafFacts leaf2094Box leaf2094Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2094Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743463424) }) = true
      norm_num [leaf2094Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2094CertificateValid :
    WideCertificateValid leaf2094Box leaf2094Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi176ValidityFacts
    leaf2094LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2094CoverageChecked :
    coverageCheck (innerAD leaf2094Box) leaf2094InnerLog = true := by
  rfl'

private theorem leaf2094InnerLogValid :
    leaf2094InnerLog.Valid 8 (innerAD leaf2094Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2094CoverageChecked

private noncomputable def leaf2094InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2094InputLogOnePlusV_eq :
    leaf2094InputLogOnePlusV = outerEnclosure 24
      (leaf2094Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2094RoundedFacts : LeafRoundedFacts 8
    leaf2094Certificate.logOnePlusV leaf2094InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2094InputLogOnePlusV_eq }

private noncomputable def leaf2094Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi176InputQChi innerPair409Input
    leaf2094InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2094LowerChecked :
    lowerCheck 24 leaf2094Box leaf2094Inputs = true := by
  rfl'

private theorem leaf2094CoversExact : CoversExact 8
    leaf2094Box leaf2094Certificate leaf2094InnerLog leaf2094Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi176RoundedFacts
    innerPair409RoundedFacts leaf2094RoundedFacts (by rfl)

private theorem leaf2094FlatSound : Sound leaf2094Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2094CertificateValid
    leaf2094InnerLogValid leaf2094CoversExact leaf2094LowerChecked

private noncomputable def leaf2095Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2095Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717355008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (798703721/536870912) }, upper := { exponent := 0, mantissa := (771/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435848703/137434710016) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2095InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2095LocalValidity :
    LeafFacts leaf2095Box leaf2095Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2095Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717355008) }) = true
      norm_num [leaf2095Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2095CertificateValid :
    WideCertificateValid leaf2095Box leaf2095Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi175ValidityFacts
    leaf2095LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2095CoverageChecked :
    coverageCheck (innerAD leaf2095Box) leaf2095InnerLog = true := by
  rfl'

private theorem leaf2095InnerLogValid :
    leaf2095InnerLog.Valid 8 (innerAD leaf2095Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2095CoverageChecked

private noncomputable def leaf2095InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2095InputLogOnePlusV_eq :
    leaf2095InputLogOnePlusV = outerEnclosure 24
      (leaf2095Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2095RoundedFacts : LeafRoundedFacts 8
    leaf2095Certificate.logOnePlusV leaf2095InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2095InputLogOnePlusV_eq }

private noncomputable def leaf2095Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi175InputQChi innerPair409Input
    leaf2095InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2095LowerChecked :
    lowerCheck 24 leaf2095Box leaf2095Inputs = true := by
  rfl'

private theorem leaf2095CoversExact : CoversExact 8
    leaf2095Box leaf2095Certificate leaf2095InnerLog leaf2095Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi175RoundedFacts
    innerPair409RoundedFacts leaf2095RoundedFacts (by rfl)

private theorem leaf2095FlatSound : Sound leaf2095Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2095CertificateValid
    leaf2095InnerLogValid leaf2095CoversExact leaf2095LowerChecked

private noncomputable def leaf2096Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2096Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905765888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (805977771/536870912) }, upper := { exponent := 0, mantissa := (389/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811930453/45811531776) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2096InnerLog : WideLogData :=
  innerPair48Data

set_option maxRecDepth 1000000 in
private theorem leaf2096LocalValidity :
    LeafFacts leaf2096Box leaf2096Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2096Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905765888) }) = true
      norm_num [leaf2096Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2096CertificateValid :
    WideCertificateValid leaf2096Box leaf2096Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi176ValidityFacts
    leaf2096LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2096CoverageChecked :
    coverageCheck (innerAD leaf2096Box) leaf2096InnerLog = true := by
  rfl'

private theorem leaf2096InnerLogValid :
    leaf2096InnerLog.Valid 8 (innerAD leaf2096Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint121PositiveFacts.valid leaf2096CoverageChecked

private noncomputable def leaf2096InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2096InputLogOnePlusV_eq :
    leaf2096InputLogOnePlusV = outerEnclosure 24
      (leaf2096Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2096RoundedFacts : LeafRoundedFacts 8
    leaf2096Certificate.logOnePlusV leaf2096InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2096InputLogOnePlusV_eq }

private noncomputable def leaf2096Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi176InputQChi innerPair48Input
    leaf2096InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2096LowerChecked :
    lowerCheck 24 leaf2096Box leaf2096Inputs = true := by
  rfl'

private theorem leaf2096CoversExact : CoversExact 8
    leaf2096Box leaf2096Certificate leaf2096InnerLog leaf2096Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi176RoundedFacts
    innerPair48RoundedFacts leaf2096RoundedFacts (by rfl)

private theorem leaf2096FlatSound : Sound leaf2096Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2096CertificateValid
    leaf2096InnerLogValid leaf2096CoversExact leaf2096LowerChecked

private noncomputable def leaf2097Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2097Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717260288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (810761607/536870912) }, upper := { exponent := 0, mantissa := (12521/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435753983/137434520576) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2097InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2097LocalValidity :
    LeafFacts leaf2097Box leaf2097Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2097Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717260288) }) = true
      norm_num [leaf2097Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2097CertificateValid :
    WideCertificateValid leaf2097Box leaf2097Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi177ValidityFacts
    leaf2097LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2097CoverageChecked :
    coverageCheck (innerAD leaf2097Box) leaf2097InnerLog = true := by
  rfl'

private theorem leaf2097InnerLogValid :
    leaf2097InnerLog.Valid 8 (innerAD leaf2097Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2097CoverageChecked

private noncomputable def leaf2097InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2097InputLogOnePlusV_eq :
    leaf2097InputLogOnePlusV = outerEnclosure 24
      (leaf2097Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2097RoundedFacts : LeafRoundedFacts 8
    leaf2097Certificate.logOnePlusV leaf2097InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2097InputLogOnePlusV_eq }

private noncomputable def leaf2097Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi177InputQChi innerPair44Input
    leaf2097InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2097LowerChecked :
    lowerCheck 24 leaf2097Box leaf2097Inputs = true := by
  rfl'

private theorem leaf2097CoversExact : CoversExact 8
    leaf2097Box leaf2097Certificate leaf2097InnerLog leaf2097Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi177RoundedFacts
    innerPair44RoundedFacts leaf2097RoundedFacts (by rfl)

private theorem leaf2097FlatSound : Sound leaf2097Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2097CertificateValid
    leaf2097InnerLogValid leaf2097CoversExact leaf2097LowerChecked

private noncomputable def leaf2098Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2098Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717203456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (817970125/536870912) }, upper := { exponent := 0, mantissa := (1579/1024) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435697151/137434406912) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf2098InnerLog : WideLogData :=
  innerPair177Data

set_option maxRecDepth 1000000 in
private theorem leaf2098LocalValidity :
    LeafFacts leaf2098Box leaf2098Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2098Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717203456) }) = true
      norm_num [leaf2098Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2098CertificateValid :
    WideCertificateValid leaf2098Box leaf2098Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi178ValidityFacts
    leaf2098LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2098CoverageChecked :
    coverageCheck (innerAD leaf2098Box) leaf2098InnerLog = true := by
  rfl'

private theorem leaf2098InnerLogValid :
    leaf2098InnerLog.Valid 8 (innerAD leaf2098Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint43PositiveFacts.valid leaf2098CoverageChecked

private noncomputable def leaf2098InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2098InputLogOnePlusV_eq :
    leaf2098InputLogOnePlusV = outerEnclosure 24
      (leaf2098Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2098RoundedFacts : LeafRoundedFacts 8
    leaf2098Certificate.logOnePlusV leaf2098InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2098InputLogOnePlusV_eq }

private noncomputable def leaf2098Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi178InputQChi innerPair177Input
    leaf2098InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2098LowerChecked :
    lowerCheck 24 leaf2098Box leaf2098Inputs = true := by
  rfl'

private theorem leaf2098CoversExact : CoversExact 8
    leaf2098Box leaf2098Certificate leaf2098InnerLog leaf2098Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi178RoundedFacts
    innerPair177RoundedFacts leaf2098RoundedFacts (by rfl)

private theorem leaf2098FlatSound : Sound leaf2098Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2098CertificateValid
    leaf2098InnerLogValid leaf2098CoversExact leaf2098LowerChecked

private noncomputable def leaf2099Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2099Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743448064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (813251821/536870912) }, upper := { exponent := 0, mantissa := (785/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487146803/27486896128) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2099InnerLog : WideLogData :=
  innerPair449Data

set_option maxRecDepth 1000000 in
private theorem leaf2099LocalValidity :
    LeafFacts leaf2099Box leaf2099Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2099Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743448064) }) = true
      norm_num [leaf2099Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2099CertificateValid :
    WideCertificateValid leaf2099Box leaf2099Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi177ValidityFacts
    leaf2099LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2099CoverageChecked :
    coverageCheck (innerAD leaf2099Box) leaf2099InnerLog = true := by
  rfl'

private theorem leaf2099InnerLogValid :
    leaf2099InnerLog.Valid 8 (innerAD leaf2099Box) :=
  wideLogDataValid_of_cachedCheck endpoint164PositiveFacts
    endpoint124PositiveFacts.valid leaf2099CoverageChecked

private noncomputable def leaf2099InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2099InputLogOnePlusV_eq :
    leaf2099InputLogOnePlusV = outerEnclosure 24
      (leaf2099Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2099RoundedFacts : LeafRoundedFacts 8
    leaf2099Certificate.logOnePlusV leaf2099InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2099InputLogOnePlusV_eq }

private noncomputable def leaf2099Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi177InputQChi innerPair449Input
    leaf2099InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2099LowerChecked :
    lowerCheck 24 leaf2099Box leaf2099Inputs = true := by
  rfl'

private theorem leaf2099CoversExact : CoversExact 8
    leaf2099Box leaf2099Certificate leaf2099InnerLog leaf2099Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi177RoundedFacts
    innerPair449RoundedFacts leaf2099RoundedFacts (by rfl)

private theorem leaf2099FlatSound : Sound leaf2099Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2099CertificateValid
    leaf2099InnerLogValid leaf2099CoversExact leaf2099LowerChecked

private noncomputable def leaf2100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717182976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (820525871/536870912) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435676671/137434365952) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf2100InnerLog : WideLogData :=
  innerPair177Data

set_option maxRecDepth 1000000 in
private theorem leaf2100LocalValidity :
    LeafFacts leaf2100Box leaf2100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717182976) }) = true
      norm_num [leaf2100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2100CertificateValid :
    WideCertificateValid leaf2100Box leaf2100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi178ValidityFacts
    leaf2100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2100CoverageChecked :
    coverageCheck (innerAD leaf2100Box) leaf2100InnerLog = true := by
  rfl'

private theorem leaf2100InnerLogValid :
    leaf2100InnerLog.Valid 8 (innerAD leaf2100Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint43PositiveFacts.valid leaf2100CoverageChecked

private noncomputable def leaf2100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2100InputLogOnePlusV_eq :
    leaf2100InputLogOnePlusV = outerEnclosure 24
      (leaf2100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2100RoundedFacts : LeafRoundedFacts 8
    leaf2100Certificate.logOnePlusV leaf2100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2100InputLogOnePlusV_eq }

private noncomputable def leaf2100Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi178InputQChi innerPair177Input
    leaf2100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2100LowerChecked :
    lowerCheck 24 leaf2100Box leaf2100Inputs = true := by
  rfl'

private theorem leaf2100CoversExact : CoversExact 8
    leaf2100Box leaf2100Certificate leaf2100InnerLog leaf2100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi178RoundedFacts
    innerPair177RoundedFacts leaf2100RoundedFacts (by rfl)

private theorem leaf2100FlatSound : Sound leaf2100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2100CertificateValid
    leaf2100InnerLogValid leaf2100CoversExact leaf2100LowerChecked

private noncomputable def component45Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node0_sound : Sound component45Node0Box :=
  sound_of_literal_split component45Node0Box leaf2037Box leaf2038Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2037FlatSound leaf2038FlatSound

private noncomputable def component45Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node1_sound : Sound component45Node1Box :=
  sound_of_literal_split component45Node1Box leaf2039Box leaf2040Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2039FlatSound leaf2040FlatSound

private noncomputable def component45Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node2_sound : Sound component45Node2Box :=
  sound_of_literal_split component45Node2Box component45Node0Box component45Node1Box
    .k (105/32) (by rfl) (by rfl)
    component45Node0_sound component45Node1_sound

private noncomputable def component45Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node3_sound : Sound component45Node3Box :=
  sound_of_literal_split component45Node3Box leaf2041Box leaf2042Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2041FlatSound leaf2042FlatSound

private noncomputable def component45Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node4_sound : Sound component45Node4Box :=
  sound_of_literal_split component45Node4Box leaf2043Box leaf2044Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2043FlatSound leaf2044FlatSound

private noncomputable def component45Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node5_sound : Sound component45Node5Box :=
  sound_of_literal_split component45Node5Box component45Node3Box component45Node4Box
    .k (105/32) (by rfl) (by rfl)
    component45Node3_sound component45Node4_sound

private noncomputable def component45Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node6_sound : Sound component45Node6Box :=
  sound_of_literal_split component45Node6Box component45Node2Box component45Node5Box
    .chi (17/128) (by rfl) (by rfl)
    component45Node2_sound component45Node5_sound

private noncomputable def component45Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node7_sound : Sound component45Node7Box :=
  sound_of_literal_split component45Node7Box leaf2045Box leaf2046Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2045FlatSound leaf2046FlatSound

private noncomputable def component45Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node8_sound : Sound component45Node8Box :=
  sound_of_literal_split component45Node8Box leaf2047Box leaf2048Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2047FlatSound leaf2048FlatSound

private noncomputable def component45Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node9_sound : Sound component45Node9Box :=
  sound_of_literal_split component45Node9Box component45Node7Box component45Node8Box
    .k (107/32) (by rfl) (by rfl)
    component45Node7_sound component45Node8_sound

private noncomputable def component45Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node10_sound : Sound component45Node10Box :=
  sound_of_literal_split component45Node10Box leaf2049Box leaf2050Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2049FlatSound leaf2050FlatSound

private noncomputable def component45Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node11_sound : Sound component45Node11Box :=
  sound_of_literal_split component45Node11Box leaf2051Box leaf2052Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2051FlatSound leaf2052FlatSound

private noncomputable def component45Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node12_sound : Sound component45Node12Box :=
  sound_of_literal_split component45Node12Box component45Node10Box component45Node11Box
    .k (107/32) (by rfl) (by rfl)
    component45Node10_sound component45Node11_sound

private noncomputable def component45Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node13_sound : Sound component45Node13Box :=
  sound_of_literal_split component45Node13Box component45Node9Box component45Node12Box
    .chi (17/128) (by rfl) (by rfl)
    component45Node9_sound component45Node12_sound

private noncomputable def component45Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node14_sound : Sound component45Node14Box :=
  sound_of_literal_split component45Node14Box component45Node6Box component45Node13Box
    .k (53/16) (by rfl) (by rfl)
    component45Node6_sound component45Node13_sound

private noncomputable def component45Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node15_sound : Sound component45Node15Box :=
  sound_of_literal_split component45Node15Box leaf2053Box leaf2054Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2053FlatSound leaf2054FlatSound

private noncomputable def component45Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node16_sound : Sound component45Node16Box :=
  sound_of_literal_split component45Node16Box leaf2055Box leaf2056Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2055FlatSound leaf2056FlatSound

private noncomputable def component45Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node17_sound : Sound component45Node17Box :=
  sound_of_literal_split component45Node17Box component45Node15Box component45Node16Box
    .k (105/32) (by rfl) (by rfl)
    component45Node15_sound component45Node16_sound

private noncomputable def component45Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node18_sound : Sound component45Node18Box :=
  sound_of_literal_split component45Node18Box leaf2057Box leaf2058Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2057FlatSound leaf2058FlatSound

private noncomputable def component45Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node19_sound : Sound component45Node19Box :=
  sound_of_literal_split component45Node19Box leaf2059Box leaf2060Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2059FlatSound leaf2060FlatSound

private noncomputable def component45Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node20_sound : Sound component45Node20Box :=
  sound_of_literal_split component45Node20Box component45Node18Box component45Node19Box
    .k (105/32) (by rfl) (by rfl)
    component45Node18_sound component45Node19_sound

private noncomputable def component45Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node21_sound : Sound component45Node21Box :=
  sound_of_literal_split component45Node21Box component45Node17Box component45Node20Box
    .chi (19/128) (by rfl) (by rfl)
    component45Node17_sound component45Node20_sound

private noncomputable def component45Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node22_sound : Sound component45Node22Box :=
  sound_of_literal_split component45Node22Box leaf2061Box leaf2062Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2061FlatSound leaf2062FlatSound

private noncomputable def component45Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node23_sound : Sound component45Node23Box :=
  sound_of_literal_split component45Node23Box leaf2063Box leaf2064Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2063FlatSound leaf2064FlatSound

private noncomputable def component45Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node24_sound : Sound component45Node24Box :=
  sound_of_literal_split component45Node24Box component45Node22Box component45Node23Box
    .k (107/32) (by rfl) (by rfl)
    component45Node22_sound component45Node23_sound

private noncomputable def component45Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node25_sound : Sound component45Node25Box :=
  sound_of_literal_split component45Node25Box leaf2065Box leaf2066Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2065FlatSound leaf2066FlatSound

private noncomputable def component45Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node26_sound : Sound component45Node26Box :=
  sound_of_literal_split component45Node26Box leaf2067Box leaf2068Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2067FlatSound leaf2068FlatSound

private noncomputable def component45Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node27_sound : Sound component45Node27Box :=
  sound_of_literal_split component45Node27Box component45Node25Box component45Node26Box
    .k (107/32) (by rfl) (by rfl)
    component45Node25_sound component45Node26_sound

private noncomputable def component45Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node28_sound : Sound component45Node28Box :=
  sound_of_literal_split component45Node28Box component45Node24Box component45Node27Box
    .chi (19/128) (by rfl) (by rfl)
    component45Node24_sound component45Node27_sound

private noncomputable def component45Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node29_sound : Sound component45Node29Box :=
  sound_of_literal_split component45Node29Box component45Node21Box component45Node28Box
    .k (53/16) (by rfl) (by rfl)
    component45Node21_sound component45Node28_sound

private noncomputable def component45Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node30_sound : Sound component45Node30Box :=
  sound_of_literal_split component45Node30Box component45Node14Box component45Node29Box
    .chi (9/64) (by rfl) (by rfl)
    component45Node14_sound component45Node29_sound

private noncomputable def component45Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node31_sound : Sound component45Node31Box :=
  sound_of_literal_split component45Node31Box leaf2069Box leaf2070Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2069FlatSound leaf2070FlatSound

private noncomputable def component45Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node32_sound : Sound component45Node32Box :=
  sound_of_literal_split component45Node32Box leaf2071Box leaf2072Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2071FlatSound leaf2072FlatSound

private noncomputable def component45Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node33_sound : Sound component45Node33Box :=
  sound_of_literal_split component45Node33Box component45Node31Box component45Node32Box
    .k (109/32) (by rfl) (by rfl)
    component45Node31_sound component45Node32_sound

private noncomputable def component45Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node34_sound : Sound component45Node34Box :=
  sound_of_literal_split component45Node34Box leaf2073Box leaf2074Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2073FlatSound leaf2074FlatSound

private noncomputable def component45Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node35_sound : Sound component45Node35Box :=
  sound_of_literal_split component45Node35Box leaf2075Box leaf2076Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2075FlatSound leaf2076FlatSound

private noncomputable def component45Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node36_sound : Sound component45Node36Box :=
  sound_of_literal_split component45Node36Box component45Node34Box component45Node35Box
    .k (109/32) (by rfl) (by rfl)
    component45Node34_sound component45Node35_sound

private noncomputable def component45Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node37_sound : Sound component45Node37Box :=
  sound_of_literal_split component45Node37Box component45Node33Box component45Node36Box
    .chi (17/128) (by rfl) (by rfl)
    component45Node33_sound component45Node36_sound

private noncomputable def component45Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node38_sound : Sound component45Node38Box :=
  sound_of_literal_split component45Node38Box leaf2077Box leaf2078Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2077FlatSound leaf2078FlatSound

private noncomputable def component45Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node39_sound : Sound component45Node39Box :=
  sound_of_literal_split component45Node39Box leaf2079Box leaf2080Box
    .chi (33/256) (by rfl) (by rfl)
    leaf2079FlatSound leaf2080FlatSound

private noncomputable def component45Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node40_sound : Sound component45Node40Box :=
  sound_of_literal_split component45Node40Box component45Node38Box component45Node39Box
    .k (111/32) (by rfl) (by rfl)
    component45Node38_sound component45Node39_sound

private noncomputable def component45Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node41_sound : Sound component45Node41Box :=
  sound_of_literal_split component45Node41Box leaf2081Box leaf2082Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2081FlatSound leaf2082FlatSound

private noncomputable def component45Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node42_sound : Sound component45Node42Box :=
  sound_of_literal_split component45Node42Box leaf2083Box leaf2084Box
    .chi (35/256) (by rfl) (by rfl)
    leaf2083FlatSound leaf2084FlatSound

private noncomputable def component45Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node43_sound : Sound component45Node43Box :=
  sound_of_literal_split component45Node43Box component45Node41Box component45Node42Box
    .k (111/32) (by rfl) (by rfl)
    component45Node41_sound component45Node42_sound

private noncomputable def component45Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node44_sound : Sound component45Node44Box :=
  sound_of_literal_split component45Node44Box component45Node40Box component45Node43Box
    .chi (17/128) (by rfl) (by rfl)
    component45Node40_sound component45Node43_sound

private noncomputable def component45Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component45Node45_sound : Sound component45Node45Box :=
  sound_of_literal_split component45Node45Box component45Node37Box component45Node44Box
    .k (55/16) (by rfl) (by rfl)
    component45Node37_sound component45Node44_sound

private noncomputable def component45Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node46_sound : Sound component45Node46Box :=
  sound_of_literal_split component45Node46Box leaf2085Box leaf2086Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2085FlatSound leaf2086FlatSound

private noncomputable def component45Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node47_sound : Sound component45Node47Box :=
  sound_of_literal_split component45Node47Box leaf2087Box leaf2088Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2087FlatSound leaf2088FlatSound

private noncomputable def component45Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node48_sound : Sound component45Node48Box :=
  sound_of_literal_split component45Node48Box component45Node46Box component45Node47Box
    .k (109/32) (by rfl) (by rfl)
    component45Node46_sound component45Node47_sound

private noncomputable def component45Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node49_sound : Sound component45Node49Box :=
  sound_of_literal_split component45Node49Box leaf2089Box leaf2090Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2089FlatSound leaf2090FlatSound

private noncomputable def component45Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node50_sound : Sound component45Node50Box :=
  sound_of_literal_split component45Node50Box leaf2091Box leaf2092Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2091FlatSound leaf2092FlatSound

private noncomputable def component45Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node51_sound : Sound component45Node51Box :=
  sound_of_literal_split component45Node51Box component45Node49Box component45Node50Box
    .k (109/32) (by rfl) (by rfl)
    component45Node49_sound component45Node50_sound

private noncomputable def component45Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node52_sound : Sound component45Node52Box :=
  sound_of_literal_split component45Node52Box component45Node48Box component45Node51Box
    .chi (19/128) (by rfl) (by rfl)
    component45Node48_sound component45Node51_sound

private noncomputable def component45Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node53_sound : Sound component45Node53Box :=
  sound_of_literal_split component45Node53Box leaf2093Box leaf2094Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2093FlatSound leaf2094FlatSound

private noncomputable def component45Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node54_sound : Sound component45Node54Box :=
  sound_of_literal_split component45Node54Box leaf2095Box leaf2096Box
    .chi (37/256) (by rfl) (by rfl)
    leaf2095FlatSound leaf2096FlatSound

private noncomputable def component45Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component45Node55_sound : Sound component45Node55Box :=
  sound_of_literal_split component45Node55Box component45Node53Box component45Node54Box
    .k (111/32) (by rfl) (by rfl)
    component45Node53_sound component45Node54_sound

private noncomputable def component45Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node56_sound : Sound component45Node56Box :=
  sound_of_literal_split component45Node56Box leaf2097Box leaf2098Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2097FlatSound leaf2098FlatSound

private noncomputable def component45Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node57_sound : Sound component45Node57Box :=
  sound_of_literal_split component45Node57Box leaf2099Box leaf2100Box
    .chi (39/256) (by rfl) (by rfl)
    leaf2099FlatSound leaf2100FlatSound

private noncomputable def component45Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node58_sound : Sound component45Node58Box :=
  sound_of_literal_split component45Node58Box component45Node56Box component45Node57Box
    .k (111/32) (by rfl) (by rfl)
    component45Node56_sound component45Node57_sound

private noncomputable def component45Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node59_sound : Sound component45Node59Box :=
  sound_of_literal_split component45Node59Box component45Node55Box component45Node58Box
    .chi (19/128) (by rfl) (by rfl)
    component45Node55_sound component45Node58_sound

private noncomputable def component45Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node60_sound : Sound component45Node60Box :=
  sound_of_literal_split component45Node60Box component45Node52Box component45Node59Box
    .k (55/16) (by rfl) (by rfl)
    component45Node52_sound component45Node59_sound

private noncomputable def component45Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component45Node61_sound : Sound component45Node61Box :=
  sound_of_literal_split component45Node61Box component45Node45Box component45Node60Box
    .chi (9/64) (by rfl) (by rfl)
    component45Node45_sound component45Node60_sound

noncomputable def component45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
theorem component45_sound : Sound component45Box :=
  sound_of_literal_split component45Box component45Node30Box component45Node61Box
    .k (27/8) (by rfl) (by rfl)
    component45Node30_sound component45Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
