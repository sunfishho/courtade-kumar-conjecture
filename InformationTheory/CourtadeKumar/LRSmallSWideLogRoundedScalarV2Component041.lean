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

private noncomputable def leaf1836Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1836Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214703) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (725570015/536870912) }, upper := { exponent := 0, mantissa := (11217/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432559/268429406) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1836InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1836LocalValidity :
    LeafFacts leaf1836Box leaf1836Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1836Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214703) }) = true
      norm_num [leaf1836Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1836CertificateValid :
    WideCertificateValid leaf1836Box leaf1836Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi131ValidityFacts
    leaf1836LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1836CoverageChecked :
    coverageCheck (innerAD leaf1836Box) leaf1836InnerLog = true := by
  rfl'

private theorem leaf1836InnerLogValid :
    leaf1836InnerLog.Valid 8 (innerAD leaf1836Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1836CoverageChecked

private noncomputable def leaf1836InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1836InputLogOnePlusV_eq :
    leaf1836InputLogOnePlusV = outerEnclosure 24
      (leaf1836Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1836RoundedFacts : LeafRoundedFacts 8
    leaf1836Certificate.logOnePlusV leaf1836InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1836InputLogOnePlusV_eq }

private noncomputable def leaf1836Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1836InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1836LowerChecked :
    lowerCheck 24 leaf1836Box leaf1836Inputs = true := by
  rfl'

private theorem leaf1836CoversExact : CoversExact 8
    leaf1836Box leaf1836Certificate leaf1836InnerLog leaf1836Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1836RoundedFacts (by rfl)

private theorem leaf1836FlatSound : Sound leaf1836Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1836CertificateValid
    leaf1836InnerLogValid leaf1836CoversExact leaf1836LowerChecked

private noncomputable def leaf1837Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1837Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107339) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (727142781/536870912) }, upper := { exponent := 0, mantissa := (5621/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216267/134214678) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1837InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1837LocalValidity :
    LeafFacts leaf1837Box leaf1837Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1837Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107339) }) = true
      norm_num [leaf1837Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1837CertificateValid :
    WideCertificateValid leaf1837Box leaf1837Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi131ValidityFacts
    leaf1837LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1837CoverageChecked :
    coverageCheck (innerAD leaf1837Box) leaf1837InnerLog = true := by
  rfl'

private theorem leaf1837InnerLogValid :
    leaf1837InnerLog.Valid 8 (innerAD leaf1837Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1837CoverageChecked

private noncomputable def leaf1837InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1837InputLogOnePlusV_eq :
    leaf1837InputLogOnePlusV = outerEnclosure 24
      (leaf1837Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1837RoundedFacts : LeafRoundedFacts 8
    leaf1837Certificate.logOnePlusV leaf1837InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1837InputLogOnePlusV_eq }

private noncomputable def leaf1837Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1837InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1837LowerChecked :
    lowerCheck 24 leaf1837Box leaf1837Inputs = true := by
  rfl'

private theorem leaf1837CoversExact : CoversExact 8
    leaf1837Box leaf1837Certificate leaf1837InnerLog leaf1837Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1837RoundedFacts (by rfl)

private theorem leaf1837FlatSound : Sound leaf1837Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1837CertificateValid
    leaf1837InnerLogValid leaf1837CoversExact leaf1837LowerChecked

private noncomputable def leaf1838Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1838Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107291) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (733433853/536870912) }, upper := { exponent := 0, mantissa := (5669/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216219/134214582) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1838InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1838LocalValidity :
    LeafFacts leaf1838Box leaf1838Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1838Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107291) }) = true
      norm_num [leaf1838Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1838CertificateValid :
    WideCertificateValid leaf1838Box leaf1838Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi132ValidityFacts
    leaf1838LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1838CoverageChecked :
    coverageCheck (innerAD leaf1838Box) leaf1838InnerLog = true := by
  rfl'

private theorem leaf1838InnerLogValid :
    leaf1838InnerLog.Valid 8 (innerAD leaf1838Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1838CoverageChecked

private noncomputable def leaf1838InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1838InputLogOnePlusV_eq :
    leaf1838InputLogOnePlusV = outerEnclosure 24
      (leaf1838Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1838RoundedFacts : LeafRoundedFacts 8
    leaf1838Certificate.logOnePlusV leaf1838InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1838InputLogOnePlusV_eq }

private noncomputable def leaf1838Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi132InputQChi innerPair22Input
    leaf1838InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1838LowerChecked :
    lowerCheck 24 leaf1838Box leaf1838Inputs = true := by
  rfl'

private theorem leaf1838CoversExact : CoversExact 8
    leaf1838Box leaf1838Certificate leaf1838InnerLog leaf1838Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi132RoundedFacts
    innerPair22RoundedFacts leaf1838RoundedFacts (by rfl)

private theorem leaf1838FlatSound : Sound leaf1838Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1838CertificateValid
    leaf1838InnerLogValid leaf1838CoversExact leaf1838LowerChecked

private noncomputable def leaf1839Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1839Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553639) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (735072151/536870912) }, upper := { exponent := 0, mantissa := (2841/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108103/67107278) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1839InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1839LocalValidity :
    LeafFacts leaf1839Box leaf1839Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1839Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553639) }) = true
      norm_num [leaf1839Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1839CertificateValid :
    WideCertificateValid leaf1839Box leaf1839Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi132ValidityFacts
    leaf1839LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1839CoverageChecked :
    coverageCheck (innerAD leaf1839Box) leaf1839InnerLog = true := by
  rfl'

private theorem leaf1839InnerLogValid :
    leaf1839InnerLog.Valid 8 (innerAD leaf1839Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1839CoverageChecked

private noncomputable def leaf1839InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1839InputLogOnePlusV_eq :
    leaf1839InputLogOnePlusV = outerEnclosure 24
      (leaf1839Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1839RoundedFacts : LeafRoundedFacts 8
    leaf1839Certificate.logOnePlusV leaf1839InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1839InputLogOnePlusV_eq }

private noncomputable def leaf1839Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi132InputQChi innerPair22Input
    leaf1839InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1839LowerChecked :
    lowerCheck 24 leaf1839Box leaf1839Inputs = true := by
  rfl'

private theorem leaf1839CoversExact : CoversExact 8
    leaf1839Box leaf1839Certificate leaf1839InnerLog leaf1839Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi132RoundedFacts
    innerPair22RoundedFacts leaf1839RoundedFacts (by rfl)

private theorem leaf1839FlatSound : Sound leaf1839Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1839CertificateValid
    leaf1839InnerLogValid leaf1839CoversExact leaf1839LowerChecked

private noncomputable def leaf1840Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1840Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214653) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (728715547/536870912) }, upper := { exponent := 0, mantissa := (11267/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432509/268429306) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1840InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1840LocalValidity :
    LeafFacts leaf1840Box leaf1840Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1840Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214653) }) = true
      norm_num [leaf1840Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1840CertificateValid :
    WideCertificateValid leaf1840Box leaf1840Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi131ValidityFacts
    leaf1840LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1840CoverageChecked :
    coverageCheck (innerAD leaf1840Box) leaf1840InnerLog = true := by
  rfl'

private theorem leaf1840InnerLogValid :
    leaf1840InnerLog.Valid 8 (innerAD leaf1840Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1840CoverageChecked

private noncomputable def leaf1840InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1840InputLogOnePlusV_eq :
    leaf1840InputLogOnePlusV = outerEnclosure 24
      (leaf1840Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1840RoundedFacts : LeafRoundedFacts 8
    leaf1840Certificate.logOnePlusV leaf1840InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1840InputLogOnePlusV_eq }

private noncomputable def leaf1840Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi131InputQChi innerPair22Input
    leaf1840InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1840LowerChecked :
    lowerCheck 24 leaf1840Box leaf1840Inputs = true := by
  rfl'

private theorem leaf1840CoversExact : CoversExact 8
    leaf1840Box leaf1840Certificate leaf1840InnerLog leaf1840Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi131RoundedFacts
    innerPair22RoundedFacts leaf1840RoundedFacts (by rfl)

private theorem leaf1840FlatSound : Sound leaf1840Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1840CertificateValid
    leaf1840InnerLogValid leaf1840CoversExact leaf1840LowerChecked

private noncomputable def leaf1841Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1841Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553657) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (730288313/536870912) }, upper := { exponent := 0, mantissa := (2823/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108121/67107314) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1841InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1841LocalValidity :
    LeafFacts leaf1841Box leaf1841Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1841Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553657) }) = true
      norm_num [leaf1841Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1841CertificateValid :
    WideCertificateValid leaf1841Box leaf1841Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi131ValidityFacts
    leaf1841LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1841CoverageChecked :
    coverageCheck (innerAD leaf1841Box) leaf1841InnerLog = true := by
  rfl'

private theorem leaf1841InnerLogValid :
    leaf1841InnerLog.Valid 8 (innerAD leaf1841Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1841CoverageChecked

private noncomputable def leaf1841InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1841InputLogOnePlusV_eq :
    leaf1841InputLogOnePlusV = outerEnclosure 24
      (leaf1841Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1841RoundedFacts : LeafRoundedFacts 8
    leaf1841Certificate.logOnePlusV leaf1841InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1841InputLogOnePlusV_eq }

private noncomputable def leaf1841Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi131InputQChi innerPair22Input
    leaf1841InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1841LowerChecked :
    lowerCheck 24 leaf1841Box leaf1841Inputs = true := by
  rfl'

private theorem leaf1841CoversExact : CoversExact 8
    leaf1841Box leaf1841Certificate leaf1841InnerLog leaf1841Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi131RoundedFacts
    innerPair22RoundedFacts leaf1841RoundedFacts (by rfl)

private theorem leaf1841FlatSound : Sound leaf1841Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1841CertificateValid
    leaf1841InnerLogValid leaf1841CoversExact leaf1841LowerChecked

private noncomputable def leaf1842Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1842Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107265) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (736710449/536870912) }, upper := { exponent := 0, mantissa := (5695/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216193/134214530) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1842InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1842LocalValidity :
    LeafFacts leaf1842Box leaf1842Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1842Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107265) }) = true
      norm_num [leaf1842Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1842CertificateValid :
    WideCertificateValid leaf1842Box leaf1842Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi132ValidityFacts
    leaf1842LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1842CoverageChecked :
    coverageCheck (innerAD leaf1842Box) leaf1842InnerLog = true := by
  rfl'

private theorem leaf1842InnerLogValid :
    leaf1842InnerLog.Valid 8 (innerAD leaf1842Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1842CoverageChecked

private noncomputable def leaf1842InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1842InputLogOnePlusV_eq :
    leaf1842InputLogOnePlusV = outerEnclosure 24
      (leaf1842Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1842RoundedFacts : LeafRoundedFacts 8
    leaf1842Certificate.logOnePlusV leaf1842InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1842InputLogOnePlusV_eq }

private noncomputable def leaf1842Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi132InputQChi innerPair22Input
    leaf1842InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1842LowerChecked :
    lowerCheck 24 leaf1842Box leaf1842Inputs = true := by
  rfl'

private theorem leaf1842CoversExact : CoversExact 8
    leaf1842Box leaf1842Certificate leaf1842InnerLog leaf1842Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi132RoundedFacts
    innerPair22RoundedFacts leaf1842RoundedFacts (by rfl)

private theorem leaf1842FlatSound : Sound leaf1842Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1842CertificateValid
    leaf1842InnerLogValid leaf1842CoversExact leaf1842LowerChecked

private noncomputable def leaf1843Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1843Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776813) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (738348747/536870912) }, upper := { exponent := 0, mantissa := (1427/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554045/33553626) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1843InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1843LocalValidity :
    LeafFacts leaf1843Box leaf1843Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1843Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776813) }) = true
      norm_num [leaf1843Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1843CertificateValid :
    WideCertificateValid leaf1843Box leaf1843Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi132ValidityFacts
    leaf1843LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1843CoverageChecked :
    coverageCheck (innerAD leaf1843Box) leaf1843InnerLog = true := by
  rfl'

private theorem leaf1843InnerLogValid :
    leaf1843InnerLog.Valid 8 (innerAD leaf1843Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1843CoverageChecked

private noncomputable def leaf1843InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1843InputLogOnePlusV_eq :
    leaf1843InputLogOnePlusV = outerEnclosure 24
      (leaf1843Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1843RoundedFacts : LeafRoundedFacts 8
    leaf1843Certificate.logOnePlusV leaf1843InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1843InputLogOnePlusV_eq }

private noncomputable def leaf1843Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi132InputQChi innerPair26Input
    leaf1843InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1843LowerChecked :
    lowerCheck 24 leaf1843Box leaf1843Inputs = true := by
  rfl'

private theorem leaf1843CoversExact : CoversExact 8
    leaf1843Box leaf1843Certificate leaf1843InnerLog leaf1843Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi132RoundedFacts
    innerPair26RoundedFacts leaf1843RoundedFacts (by rfl)

private theorem leaf1843FlatSound : Sound leaf1843Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1843CertificateValid
    leaf1843InnerLogValid leaf1843CoversExact leaf1843LowerChecked

private noncomputable def leaf1844Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1844Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214461) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (741297691/536870912) }, upper := { exponent := 0, mantissa := (11459/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432317/268428922) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1844InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1844LocalValidity :
    LeafFacts leaf1844Box leaf1844Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1844Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214461) }) = true
      norm_num [leaf1844Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1844CertificateValid :
    WideCertificateValid leaf1844Box leaf1844Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi149ValidityFacts
    leaf1844LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1844CoverageChecked :
    coverageCheck (innerAD leaf1844Box) leaf1844InnerLog = true := by
  rfl'

private theorem leaf1844InnerLogValid :
    leaf1844InnerLog.Valid 8 (innerAD leaf1844Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1844CoverageChecked

private noncomputable def leaf1844InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1844InputLogOnePlusV_eq :
    leaf1844InputLogOnePlusV = outerEnclosure 24
      (leaf1844Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1844RoundedFacts : LeafRoundedFacts 8
    leaf1844Certificate.logOnePlusV leaf1844InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1844InputLogOnePlusV_eq }

private noncomputable def leaf1844Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi149InputQChi innerPair26Input
    leaf1844InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1844LowerChecked :
    lowerCheck 24 leaf1844Box leaf1844Inputs = true := by
  rfl'

private theorem leaf1844CoversExact : CoversExact 8
    leaf1844Box leaf1844Certificate leaf1844InnerLog leaf1844Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi149RoundedFacts
    innerPair26RoundedFacts leaf1844RoundedFacts (by rfl)

private theorem leaf1844FlatSound : Sound leaf1844Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1844CertificateValid
    leaf1844InnerLogValid leaf1844CoversExact leaf1844LowerChecked

private noncomputable def leaf1845Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1845Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107217) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (743001521/536870912) }, upper := { exponent := 0, mantissa := (5743/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216145/134214434) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1845InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1845LocalValidity :
    LeafFacts leaf1845Box leaf1845Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1845Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107217) }) = true
      norm_num [leaf1845Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1845CertificateValid :
    WideCertificateValid leaf1845Box leaf1845Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi149ValidityFacts
    leaf1845LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1845CoverageChecked :
    coverageCheck (innerAD leaf1845Box) leaf1845InnerLog = true := by
  rfl'

private theorem leaf1845InnerLogValid :
    leaf1845InnerLog.Valid 8 (innerAD leaf1845Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1845CoverageChecked

private noncomputable def leaf1845InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1845InputLogOnePlusV_eq :
    leaf1845InputLogOnePlusV = outerEnclosure 24
      (leaf1845Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1845RoundedFacts : LeafRoundedFacts 8
    leaf1845Certificate.logOnePlusV leaf1845InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1845InputLogOnePlusV_eq }

private noncomputable def leaf1845Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi149InputQChi innerPair26Input
    leaf1845InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1845LowerChecked :
    lowerCheck 24 leaf1845Box leaf1845Inputs = true := by
  rfl'

private theorem leaf1845CoversExact : CoversExact 8
    leaf1845Box leaf1845Certificate leaf1845InnerLog leaf1845Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi149RoundedFacts
    innerPair26RoundedFacts leaf1845RoundedFacts (by rfl)

private theorem leaf1845FlatSound : Sound leaf1845Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1845CertificateValid
    leaf1845InnerLogValid leaf1845CoversExact leaf1845LowerChecked

private noncomputable def leaf1846Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1846Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553585) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (749161529/536870912) }, upper := { exponent := 0, mantissa := (2895/2048) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108049/67107170) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1846InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1846LocalValidity :
    LeafFacts leaf1846Box leaf1846Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1846Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553585) }) = true
      norm_num [leaf1846Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1846CertificateValid :
    WideCertificateValid leaf1846Box leaf1846Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi150ValidityFacts
    leaf1846LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1846CoverageChecked :
    coverageCheck (innerAD leaf1846Box) leaf1846InnerLog = true := by
  rfl'

private theorem leaf1846InnerLogValid :
    leaf1846InnerLog.Valid 8 (innerAD leaf1846Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1846CoverageChecked

private noncomputable def leaf1846InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1846InputLogOnePlusV_eq :
    leaf1846InputLogOnePlusV = outerEnclosure 24
      (leaf1846Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1846RoundedFacts : LeafRoundedFacts 8
    leaf1846Certificate.logOnePlusV leaf1846InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1846InputLogOnePlusV_eq }

private noncomputable def leaf1846Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1846InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1846LowerChecked :
    lowerCheck 24 leaf1846Box leaf1846Inputs = true := by
  rfl'

private theorem leaf1846CoversExact : CoversExact 8
    leaf1846Box leaf1846Certificate leaf1846InnerLog leaf1846Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1846RoundedFacts (by rfl)

private theorem leaf1846FlatSound : Sound leaf1846Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1846CertificateValid
    leaf1846InnerLogValid leaf1846CoversExact leaf1846LowerChecked

private noncomputable def leaf1847Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1847Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776789) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (750930891/536870912) }, upper := { exponent := 0, mantissa := (1451/1024) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554021/33553578) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1847InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1847LocalValidity :
    LeafFacts leaf1847Box leaf1847Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1847Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776789) }) = true
      norm_num [leaf1847Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1847CertificateValid :
    WideCertificateValid leaf1847Box leaf1847Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi150ValidityFacts
    leaf1847LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1847CoverageChecked :
    coverageCheck (innerAD leaf1847Box) leaf1847InnerLog = true := by
  rfl'

private theorem leaf1847InnerLogValid :
    leaf1847InnerLog.Valid 8 (innerAD leaf1847Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1847CoverageChecked

private noncomputable def leaf1847InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1847InputLogOnePlusV_eq :
    leaf1847InputLogOnePlusV = outerEnclosure 24
      (leaf1847Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1847RoundedFacts : LeafRoundedFacts 8
    leaf1847Certificate.logOnePlusV leaf1847InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1847InputLogOnePlusV_eq }

private noncomputable def leaf1847Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1847InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1847LowerChecked :
    lowerCheck 24 leaf1847Box leaf1847Inputs = true := by
  rfl'

private theorem leaf1847CoversExact : CoversExact 8
    leaf1847Box leaf1847Certificate leaf1847InnerLog leaf1847Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1847RoundedFacts (by rfl)

private theorem leaf1847FlatSound : Sound leaf1847Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1847CertificateValid
    leaf1847InnerLogValid leaf1847CoversExact leaf1847LowerChecked

private noncomputable def leaf1848Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1848Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214407) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (744705351/536870912) }, upper := { exponent := 0, mantissa := (11513/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432263/268428814) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1848InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1848LocalValidity :
    LeafFacts leaf1848Box leaf1848Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1848Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214407) }) = true
      norm_num [leaf1848Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1848CertificateValid :
    WideCertificateValid leaf1848Box leaf1848Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi149ValidityFacts
    leaf1848LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1848CoverageChecked :
    coverageCheck (innerAD leaf1848Box) leaf1848InnerLog = true := by
  rfl'

private theorem leaf1848InnerLogValid :
    leaf1848InnerLog.Valid 8 (innerAD leaf1848Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1848CoverageChecked

private noncomputable def leaf1848InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1848InputLogOnePlusV_eq :
    leaf1848InputLogOnePlusV = outerEnclosure 24
      (leaf1848Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1848RoundedFacts : LeafRoundedFacts 8
    leaf1848Certificate.logOnePlusV leaf1848InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1848InputLogOnePlusV_eq }

private noncomputable def leaf1848Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi149InputQChi innerPair26Input
    leaf1848InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1848LowerChecked :
    lowerCheck 24 leaf1848Box leaf1848Inputs = true := by
  rfl'

private theorem leaf1848CoversExact : CoversExact 8
    leaf1848Box leaf1848Certificate leaf1848InnerLog leaf1848Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi149RoundedFacts
    innerPair26RoundedFacts leaf1848RoundedFacts (by rfl)

private theorem leaf1848FlatSound : Sound leaf1848Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1848CertificateValid
    leaf1848InnerLogValid leaf1848CoversExact leaf1848LowerChecked

private noncomputable def leaf1849Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1849Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553595) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (746409181/536870912) }, upper := { exponent := 0, mantissa := (2885/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108059/67107190) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1849InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1849LocalValidity :
    LeafFacts leaf1849Box leaf1849Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1849Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553595) }) = true
      norm_num [leaf1849Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1849CertificateValid :
    WideCertificateValid leaf1849Box leaf1849Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi149ValidityFacts
    leaf1849LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1849CoverageChecked :
    coverageCheck (innerAD leaf1849Box) leaf1849InnerLog = true := by
  rfl'

private theorem leaf1849InnerLogValid :
    leaf1849InnerLog.Valid 8 (innerAD leaf1849Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1849CoverageChecked

private noncomputable def leaf1849InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1849InputLogOnePlusV_eq :
    leaf1849InputLogOnePlusV = outerEnclosure 24
      (leaf1849Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1849RoundedFacts : LeafRoundedFacts 8
    leaf1849Certificate.logOnePlusV leaf1849InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1849InputLogOnePlusV_eq }

private noncomputable def leaf1849Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi149InputQChi innerPair26Input
    leaf1849InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1849LowerChecked :
    lowerCheck 24 leaf1849Box leaf1849Inputs = true := by
  rfl'

private theorem leaf1849CoversExact : CoversExact 8
    leaf1849Box leaf1849Certificate leaf1849InnerLog leaf1849Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi149RoundedFacts
    innerPair26RoundedFacts leaf1849RoundedFacts (by rfl)

private theorem leaf1849FlatSound : Sound leaf1849Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1849CertificateValid
    leaf1849InnerLogValid leaf1849CoversExact leaf1849LowerChecked

private noncomputable def leaf1850Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1850Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (752700253/536870912) }, upper := { exponent := 0, mantissa := (2909/2048) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108035/67107142) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1850InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1850LocalValidity :
    LeafFacts leaf1850Box leaf1850Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1850Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553571) }) = true
      norm_num [leaf1850Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1850CertificateValid :
    WideCertificateValid leaf1850Box leaf1850Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi150ValidityFacts
    leaf1850LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1850CoverageChecked :
    coverageCheck (innerAD leaf1850Box) leaf1850InnerLog = true := by
  rfl'

private theorem leaf1850InnerLogValid :
    leaf1850InnerLog.Valid 8 (innerAD leaf1850Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1850CoverageChecked

private noncomputable def leaf1850InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1850InputLogOnePlusV_eq :
    leaf1850InputLogOnePlusV = outerEnclosure 24
      (leaf1850Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1850RoundedFacts : LeafRoundedFacts 8
    leaf1850Certificate.logOnePlusV leaf1850InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1850InputLogOnePlusV_eq }

private noncomputable def leaf1850Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1850InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1850LowerChecked :
    lowerCheck 24 leaf1850Box leaf1850Inputs = true := by
  rfl'

private theorem leaf1850CoversExact : CoversExact 8
    leaf1850Box leaf1850Certificate leaf1850InnerLog leaf1850Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1850RoundedFacts (by rfl)

private theorem leaf1850FlatSound : Sound leaf1850Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1850CertificateValid
    leaf1850InnerLogValid leaf1850CoversExact leaf1850LowerChecked

private noncomputable def leaf1851Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1851Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388391) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (754469615/536870912) }, upper := { exponent := 0, mantissa := (729/512) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777007/16776782) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1851InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1851LocalValidity :
    LeafFacts leaf1851Box leaf1851Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1851Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388391) }) = true
      norm_num [leaf1851Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1851CertificateValid :
    WideCertificateValid leaf1851Box leaf1851Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi150ValidityFacts
    leaf1851LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1851CoverageChecked :
    coverageCheck (innerAD leaf1851Box) leaf1851InnerLog = true := by
  rfl'

private theorem leaf1851InnerLogValid :
    leaf1851InnerLog.Valid 8 (innerAD leaf1851Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1851CoverageChecked

private noncomputable def leaf1851InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1851InputLogOnePlusV_eq :
    leaf1851InputLogOnePlusV = outerEnclosure 24
      (leaf1851Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1851RoundedFacts : LeafRoundedFacts 8
    leaf1851Certificate.logOnePlusV leaf1851InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1851InputLogOnePlusV_eq }

private noncomputable def leaf1851Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi150InputQChi innerPair26Input
    leaf1851InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1851LowerChecked :
    lowerCheck 24 leaf1851Box leaf1851Inputs = true := by
  rfl'

private theorem leaf1851CoversExact : CoversExact 8
    leaf1851Box leaf1851Certificate leaf1851InnerLog leaf1851Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi150RoundedFacts
    innerPair26RoundedFacts leaf1851RoundedFacts (by rfl)

private theorem leaf1851FlatSound : Sound leaf1851Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1851CertificateValid
    leaf1851InnerLogValid leaf1851CoversExact leaf1851LowerChecked

private noncomputable def leaf1852Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1852Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214603) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (731861079/536870912) }, upper := { exponent := 0, mantissa := (11317/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432459/268429206) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1852InnerLog : WideLogData :=
  innerPair132Data

set_option maxRecDepth 1000000 in
private theorem leaf1852LocalValidity :
    LeafFacts leaf1852Box leaf1852Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1852Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214603) }) = true
      norm_num [leaf1852Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1852CertificateValid :
    WideCertificateValid leaf1852Box leaf1852Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi131ValidityFacts
    leaf1852LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1852CoverageChecked :
    coverageCheck (innerAD leaf1852Box) leaf1852InnerLog = true := by
  rfl'

private theorem leaf1852InnerLogValid :
    leaf1852InnerLog.Valid 8 (innerAD leaf1852Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint34PositiveFacts.valid leaf1852CoverageChecked

private noncomputable def leaf1852InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1852InputLogOnePlusV_eq :
    leaf1852InputLogOnePlusV = outerEnclosure 24
      (leaf1852Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1852RoundedFacts : LeafRoundedFacts 8
    leaf1852Certificate.logOnePlusV leaf1852InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1852InputLogOnePlusV_eq }

private noncomputable def leaf1852Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi131InputQChi innerPair132Input
    leaf1852InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1852LowerChecked :
    lowerCheck 24 leaf1852Box leaf1852Inputs = true := by
  rfl'

private theorem leaf1852CoversExact : CoversExact 8
    leaf1852Box leaf1852Certificate leaf1852InnerLog leaf1852Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi131RoundedFacts
    innerPair132RoundedFacts leaf1852RoundedFacts (by rfl)

private theorem leaf1852FlatSound : Sound leaf1852Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1852CertificateValid
    leaf1852InnerLogValid leaf1852CoversExact leaf1852LowerChecked

private noncomputable def leaf1853Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1853Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107289) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (733433845/536870912) }, upper := { exponent := 0, mantissa := (5671/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216217/134214578) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1853InnerLog : WideLogData :=
  innerPair132Data

set_option maxRecDepth 1000000 in
private theorem leaf1853LocalValidity :
    LeafFacts leaf1853Box leaf1853Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1853Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107289) }) = true
      norm_num [leaf1853Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1853CertificateValid :
    WideCertificateValid leaf1853Box leaf1853Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi131ValidityFacts
    leaf1853LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1853CoverageChecked :
    coverageCheck (innerAD leaf1853Box) leaf1853InnerLog = true := by
  rfl'

private theorem leaf1853InnerLogValid :
    leaf1853InnerLog.Valid 8 (innerAD leaf1853Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint34PositiveFacts.valid leaf1853CoverageChecked

private noncomputable def leaf1853InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1853InputLogOnePlusV_eq :
    leaf1853InputLogOnePlusV = outerEnclosure 24
      (leaf1853Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1853RoundedFacts : LeafRoundedFacts 8
    leaf1853Certificate.logOnePlusV leaf1853InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1853InputLogOnePlusV_eq }

private noncomputable def leaf1853Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi131InputQChi innerPair132Input
    leaf1853InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1853LowerChecked :
    lowerCheck 24 leaf1853Box leaf1853Inputs = true := by
  rfl'

private theorem leaf1853CoversExact : CoversExact 8
    leaf1853Box leaf1853Certificate leaf1853InnerLog leaf1853Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi131RoundedFacts
    innerPair132RoundedFacts leaf1853RoundedFacts (by rfl)

private theorem leaf1853FlatSound : Sound leaf1853Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1853CertificateValid
    leaf1853InnerLogValid leaf1853CoversExact leaf1853LowerChecked

private noncomputable def leaf1854Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1854Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107239) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (739987045/536870912) }, upper := { exponent := 0, mantissa := (5721/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216167/134214478) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1854InnerLog : WideLogData :=
  innerPair29Data

set_option maxRecDepth 1000000 in
private theorem leaf1854LocalValidity :
    LeafFacts leaf1854Box leaf1854Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1854Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107239) }) = true
      norm_num [leaf1854Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1854CertificateValid :
    WideCertificateValid leaf1854Box leaf1854Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi132ValidityFacts
    leaf1854LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1854CoverageChecked :
    coverageCheck (innerAD leaf1854Box) leaf1854InnerLog = true := by
  rfl'

private theorem leaf1854InnerLogValid :
    leaf1854InnerLog.Valid 8 (innerAD leaf1854Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint38PositiveFacts.valid leaf1854CoverageChecked

private noncomputable def leaf1854InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1854InputLogOnePlusV_eq :
    leaf1854InputLogOnePlusV = outerEnclosure 24
      (leaf1854Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1854RoundedFacts : LeafRoundedFacts 8
    leaf1854Certificate.logOnePlusV leaf1854InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1854InputLogOnePlusV_eq }

private noncomputable def leaf1854Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi132InputQChi innerPair29Input
    leaf1854InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1854LowerChecked :
    lowerCheck 24 leaf1854Box leaf1854Inputs = true := by
  rfl'

private theorem leaf1854CoversExact : CoversExact 8
    leaf1854Box leaf1854Certificate leaf1854InnerLog leaf1854Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi132RoundedFacts
    innerPair29RoundedFacts leaf1854RoundedFacts (by rfl)

private theorem leaf1854FlatSound : Sound leaf1854Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1854CertificateValid
    leaf1854InnerLogValid leaf1854CoversExact leaf1854LowerChecked

private noncomputable def leaf1855Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1855Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553613) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (741625343/536870912) }, upper := { exponent := 0, mantissa := (2867/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108077/67107226) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1855InnerLog : WideLogData :=
  innerPair29Data

set_option maxRecDepth 1000000 in
private theorem leaf1855LocalValidity :
    LeafFacts leaf1855Box leaf1855Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1855Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553613) }) = true
      norm_num [leaf1855Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1855CertificateValid :
    WideCertificateValid leaf1855Box leaf1855Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi132ValidityFacts
    leaf1855LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1855CoverageChecked :
    coverageCheck (innerAD leaf1855Box) leaf1855InnerLog = true := by
  rfl'

private theorem leaf1855InnerLogValid :
    leaf1855InnerLog.Valid 8 (innerAD leaf1855Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint38PositiveFacts.valid leaf1855CoverageChecked

private noncomputable def leaf1855InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1855InputLogOnePlusV_eq :
    leaf1855InputLogOnePlusV = outerEnclosure 24
      (leaf1855Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1855RoundedFacts : LeafRoundedFacts 8
    leaf1855Certificate.logOnePlusV leaf1855InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1855InputLogOnePlusV_eq }

private noncomputable def leaf1855Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi132InputQChi innerPair29Input
    leaf1855InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1855LowerChecked :
    lowerCheck 24 leaf1855Box leaf1855Inputs = true := by
  rfl'

private theorem leaf1855CoversExact : CoversExact 8
    leaf1855Box leaf1855Certificate leaf1855InnerLog leaf1855Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi132RoundedFacts
    innerPair29RoundedFacts leaf1855RoundedFacts (by rfl)

private theorem leaf1855FlatSound : Sound leaf1855Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1855CertificateValid
    leaf1855InnerLogValid leaf1855CoversExact leaf1855LowerChecked

private noncomputable def leaf1856Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1856Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (735006611/536870912) }, upper := { exponent := 0, mantissa := (11367/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432409/268429106) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1856InnerLog : WideLogData :=
  innerPair132Data

set_option maxRecDepth 1000000 in
private theorem leaf1856LocalValidity :
    LeafFacts leaf1856Box leaf1856Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1856Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214553) }) = true
      norm_num [leaf1856Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1856CertificateValid :
    WideCertificateValid leaf1856Box leaf1856Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi131ValidityFacts
    leaf1856LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1856CoverageChecked :
    coverageCheck (innerAD leaf1856Box) leaf1856InnerLog = true := by
  rfl'

private theorem leaf1856InnerLogValid :
    leaf1856InnerLog.Valid 8 (innerAD leaf1856Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint34PositiveFacts.valid leaf1856CoverageChecked

private noncomputable def leaf1856InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1856InputLogOnePlusV_eq :
    leaf1856InputLogOnePlusV = outerEnclosure 24
      (leaf1856Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1856RoundedFacts : LeafRoundedFacts 8
    leaf1856Certificate.logOnePlusV leaf1856InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1856InputLogOnePlusV_eq }

private noncomputable def leaf1856Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi131InputQChi innerPair132Input
    leaf1856InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1856LowerChecked :
    lowerCheck 24 leaf1856Box leaf1856Inputs = true := by
  rfl'

private theorem leaf1856CoversExact : CoversExact 8
    leaf1856Box leaf1856Certificate leaf1856InnerLog leaf1856Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi131RoundedFacts
    innerPair132RoundedFacts leaf1856RoundedFacts (by rfl)

private theorem leaf1856FlatSound : Sound leaf1856Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1856CertificateValid
    leaf1856InnerLogValid leaf1856CoversExact leaf1856LowerChecked

private noncomputable def leaf1857Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1857Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871217/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048551) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (736579377/536870912) }, upper := { exponent := 0, mantissa := (89/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048564/1048551) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1857InnerLog : WideLogData :=
  innerPair132Data

set_option maxRecDepth 1000000 in
private theorem leaf1857LocalValidity :
    LeafFacts leaf1857Box leaf1857Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1857Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048551) }) = true
      norm_num [leaf1857Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1857CertificateValid :
    WideCertificateValid leaf1857Box leaf1857Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi131ValidityFacts
    leaf1857LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1857CoverageChecked :
    coverageCheck (innerAD leaf1857Box) leaf1857InnerLog = true := by
  rfl'

private theorem leaf1857InnerLogValid :
    leaf1857InnerLog.Valid 8 (innerAD leaf1857Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint34PositiveFacts.valid leaf1857CoverageChecked

private noncomputable def leaf1857InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1857InputLogOnePlusV_eq :
    leaf1857InputLogOnePlusV = outerEnclosure 24
      (leaf1857Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1857RoundedFacts : LeafRoundedFacts 8
    leaf1857Certificate.logOnePlusV leaf1857InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1857InputLogOnePlusV_eq }

private noncomputable def leaf1857Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi131InputQChi innerPair132Input
    leaf1857InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1857LowerChecked :
    lowerCheck 24 leaf1857Box leaf1857Inputs = true := by
  rfl'

private theorem leaf1857CoversExact : CoversExact 8
    leaf1857Box leaf1857Certificate leaf1857InnerLog leaf1857Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi131RoundedFacts
    innerPair132RoundedFacts leaf1857RoundedFacts (by rfl)

private theorem leaf1857FlatSound : Sound leaf1857Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1857CertificateValid
    leaf1857InnerLogValid leaf1857CoversExact leaf1857LowerChecked

private noncomputable def leaf1858Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1858Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871217/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107213) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (743263641/536870912) }, upper := { exponent := 0, mantissa := (5747/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216141/134214426) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1858InnerLog : WideLogData :=
  innerPair29Data

set_option maxRecDepth 1000000 in
private theorem leaf1858LocalValidity :
    LeafFacts leaf1858Box leaf1858Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1858Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107213) }) = true
      norm_num [leaf1858Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1858CertificateValid :
    WideCertificateValid leaf1858Box leaf1858Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi132ValidityFacts
    leaf1858LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1858CoverageChecked :
    coverageCheck (innerAD leaf1858Box) leaf1858InnerLog = true := by
  rfl'

private theorem leaf1858InnerLogValid :
    leaf1858InnerLog.Valid 8 (innerAD leaf1858Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint38PositiveFacts.valid leaf1858CoverageChecked

private noncomputable def leaf1858InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1858InputLogOnePlusV_eq :
    leaf1858InputLogOnePlusV = outerEnclosure 24
      (leaf1858Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1858RoundedFacts : LeafRoundedFacts 8
    leaf1858Certificate.logOnePlusV leaf1858InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1858InputLogOnePlusV_eq }

private noncomputable def leaf1858Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi132InputQChi innerPair29Input
    leaf1858InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1858LowerChecked :
    lowerCheck 24 leaf1858Box leaf1858Inputs = true := by
  rfl'

private theorem leaf1858CoversExact : CoversExact 8
    leaf1858Box leaf1858Certificate leaf1858InnerLog leaf1858Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi132RoundedFacts
    innerPair29RoundedFacts leaf1858RoundedFacts (by rfl)

private theorem leaf1858FlatSound : Sound leaf1858Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1858CertificateValid
    leaf1858InnerLogValid leaf1858CoversExact leaf1858LowerChecked

private noncomputable def leaf1859Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1859Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871219/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048550) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (744901939/536870912) }, upper := { exponent := 0, mantissa := (45/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097127/2097100) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1859InnerLog : WideLogData :=
  innerPair29Data

set_option maxRecDepth 1000000 in
private theorem leaf1859LocalValidity :
    LeafFacts leaf1859Box leaf1859Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1859Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048550) }) = true
      norm_num [leaf1859Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1859CertificateValid :
    WideCertificateValid leaf1859Box leaf1859Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi132ValidityFacts
    leaf1859LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1859CoverageChecked :
    coverageCheck (innerAD leaf1859Box) leaf1859InnerLog = true := by
  rfl'

private theorem leaf1859InnerLogValid :
    leaf1859InnerLog.Valid 8 (innerAD leaf1859Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint38PositiveFacts.valid leaf1859CoverageChecked

private noncomputable def leaf1859InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1859InputLogOnePlusV_eq :
    leaf1859InputLogOnePlusV = outerEnclosure 24
      (leaf1859Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1859RoundedFacts : LeafRoundedFacts 8
    leaf1859Certificate.logOnePlusV leaf1859InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1859InputLogOnePlusV_eq }

private noncomputable def leaf1859Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi132InputQChi innerPair29Input
    leaf1859InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1859LowerChecked :
    lowerCheck 24 leaf1859Box leaf1859Inputs = true := by
  rfl'

private theorem leaf1859CoversExact : CoversExact 8
    leaf1859Box leaf1859Certificate leaf1859InnerLog leaf1859Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi132RoundedFacts
    innerPair29RoundedFacts leaf1859RoundedFacts (by rfl)

private theorem leaf1859FlatSound : Sound leaf1859Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1859CertificateValid
    leaf1859InnerLogValid leaf1859CoversExact leaf1859LowerChecked

private noncomputable def leaf1860Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1860Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214353) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (748113011/536870912) }, upper := { exponent := 0, mantissa := (11567/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432209/268428706) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1860InnerLog : WideLogData :=
  innerPair139Data

set_option maxRecDepth 1000000 in
private theorem leaf1860LocalValidity :
    LeafFacts leaf1860Box leaf1860Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1860Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214353) }) = true
      norm_num [leaf1860Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1860CertificateValid :
    WideCertificateValid leaf1860Box leaf1860Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi149ValidityFacts
    leaf1860LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1860CoverageChecked :
    coverageCheck (innerAD leaf1860Box) leaf1860InnerLog = true := by
  rfl'

private theorem leaf1860InnerLogValid :
    leaf1860InnerLog.Valid 8 (innerAD leaf1860Box) :=
  wideLogDataValid_of_cachedCheck endpoint34PositiveFacts
    endpoint119PositiveFacts.valid leaf1860CoverageChecked

private noncomputable def leaf1860InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1860InputLogOnePlusV_eq :
    leaf1860InputLogOnePlusV = outerEnclosure 24
      (leaf1860Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1860RoundedFacts : LeafRoundedFacts 8
    leaf1860Certificate.logOnePlusV leaf1860InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1860InputLogOnePlusV_eq }

private noncomputable def leaf1860Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi149InputQChi innerPair139Input
    leaf1860InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1860LowerChecked :
    lowerCheck 24 leaf1860Box leaf1860Inputs = true := by
  rfl'

private theorem leaf1860CoversExact : CoversExact 8
    leaf1860Box leaf1860Certificate leaf1860InnerLog leaf1860Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi149RoundedFacts
    innerPair139RoundedFacts leaf1860RoundedFacts (by rfl)

private theorem leaf1860FlatSound : Sound leaf1860Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1860CertificateValid
    leaf1860InnerLogValid leaf1860CoversExact leaf1860LowerChecked

private noncomputable def leaf1861Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1861Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871217/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107163) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (749816841/536870912) }, upper := { exponent := 0, mantissa := (5797/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216091/134214326) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1861InnerLog : WideLogData :=
  innerPair139Data

set_option maxRecDepth 1000000 in
private theorem leaf1861LocalValidity :
    LeafFacts leaf1861Box leaf1861Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1861Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107163) }) = true
      norm_num [leaf1861Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1861CertificateValid :
    WideCertificateValid leaf1861Box leaf1861Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi149ValidityFacts
    leaf1861LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1861CoverageChecked :
    coverageCheck (innerAD leaf1861Box) leaf1861InnerLog = true := by
  rfl'

private theorem leaf1861InnerLogValid :
    leaf1861InnerLog.Valid 8 (innerAD leaf1861Box) :=
  wideLogDataValid_of_cachedCheck endpoint34PositiveFacts
    endpoint119PositiveFacts.valid leaf1861CoverageChecked

private noncomputable def leaf1861InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1861InputLogOnePlusV_eq :
    leaf1861InputLogOnePlusV = outerEnclosure 24
      (leaf1861Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1861RoundedFacts : LeafRoundedFacts 8
    leaf1861Certificate.logOnePlusV leaf1861InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1861InputLogOnePlusV_eq }

private noncomputable def leaf1861Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi149InputQChi innerPair139Input
    leaf1861InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1861LowerChecked :
    lowerCheck 24 leaf1861Box leaf1861Inputs = true := by
  rfl'

private theorem leaf1861CoversExact : CoversExact 8
    leaf1861Box leaf1861Certificate leaf1861InnerLog leaf1861Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi149RoundedFacts
    innerPair139RoundedFacts leaf1861RoundedFacts (by rfl)

private theorem leaf1861FlatSound : Sound leaf1861Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1861CertificateValid
    leaf1861InnerLogValid leaf1861CoversExact leaf1861LowerChecked

private noncomputable def leaf1862Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1862Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871217/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553557) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (756238977/536870912) }, upper := { exponent := 0, mantissa := (2923/2048) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108021/67107114) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1862InnerLog : WideLogData :=
  innerPair146Data

set_option maxRecDepth 1000000 in
private theorem leaf1862LocalValidity :
    LeafFacts leaf1862Box leaf1862Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1862Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553557) }) = true
      norm_num [leaf1862Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1862CertificateValid :
    WideCertificateValid leaf1862Box leaf1862Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi150ValidityFacts
    leaf1862LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1862CoverageChecked :
    coverageCheck (innerAD leaf1862Box) leaf1862InnerLog = true := by
  rfl'

private theorem leaf1862InnerLogValid :
    leaf1862InnerLog.Valid 8 (innerAD leaf1862Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint156PositiveFacts.valid leaf1862CoverageChecked

private noncomputable def leaf1862InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1862InputLogOnePlusV_eq :
    leaf1862InputLogOnePlusV = outerEnclosure 24
      (leaf1862Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1862RoundedFacts : LeafRoundedFacts 8
    leaf1862Certificate.logOnePlusV leaf1862InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1862InputLogOnePlusV_eq }

private noncomputable def leaf1862Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi150InputQChi innerPair146Input
    leaf1862InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1862LowerChecked :
    lowerCheck 24 leaf1862Box leaf1862Inputs = true := by
  rfl'

private theorem leaf1862CoversExact : CoversExact 8
    leaf1862Box leaf1862Certificate leaf1862InnerLog leaf1862Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi150RoundedFacts
    innerPair146RoundedFacts leaf1862RoundedFacts (by rfl)

private theorem leaf1862FlatSound : Sound leaf1862Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1862CertificateValid
    leaf1862InnerLogValid leaf1862CoversExact leaf1862LowerChecked

private noncomputable def leaf1863Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1863Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871219/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776775) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (758008339/536870912) }, upper := { exponent := 0, mantissa := (1465/1024) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554007/33553550) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1863InnerLog : WideLogData :=
  innerPair396Data

set_option maxRecDepth 1000000 in
private theorem leaf1863LocalValidity :
    LeafFacts leaf1863Box leaf1863Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1863Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776775) }) = true
      norm_num [leaf1863Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1863CertificateValid :
    WideCertificateValid leaf1863Box leaf1863Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi150ValidityFacts
    leaf1863LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1863CoverageChecked :
    coverageCheck (innerAD leaf1863Box) leaf1863InnerLog = true := by
  rfl'

private theorem leaf1863InnerLogValid :
    leaf1863InnerLog.Valid 8 (innerAD leaf1863Box) :=
  wideLogDataValid_of_cachedCheck endpoint107PositiveFacts
    endpoint155PositiveFacts.valid leaf1863CoverageChecked

private noncomputable def leaf1863InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1863InputLogOnePlusV_eq :
    leaf1863InputLogOnePlusV = outerEnclosure 24
      (leaf1863Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1863RoundedFacts : LeafRoundedFacts 8
    leaf1863Certificate.logOnePlusV leaf1863InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1863InputLogOnePlusV_eq }

private noncomputable def leaf1863Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi150InputQChi innerPair396Input
    leaf1863InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1863LowerChecked :
    lowerCheck 24 leaf1863Box leaf1863Inputs = true := by
  rfl'

private theorem leaf1863CoversExact : CoversExact 8
    leaf1863Box leaf1863Certificate leaf1863InnerLog leaf1863Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi150RoundedFacts
    innerPair396RoundedFacts leaf1863RoundedFacts (by rfl)

private theorem leaf1863FlatSound : Sound leaf1863Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1863CertificateValid
    leaf1863InnerLogValid leaf1863CoversExact leaf1863LowerChecked

private noncomputable def leaf1864Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1864Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871219/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214299) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (751520671/536870912) }, upper := { exponent := 0, mantissa := (11621/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432155/268428598) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1864InnerLog : WideLogData :=
  innerPair139Data

set_option maxRecDepth 1000000 in
private theorem leaf1864LocalValidity :
    LeafFacts leaf1864Box leaf1864Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1864Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214299) }) = true
      norm_num [leaf1864Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1864CertificateValid :
    WideCertificateValid leaf1864Box leaf1864Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi149ValidityFacts
    leaf1864LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1864CoverageChecked :
    coverageCheck (innerAD leaf1864Box) leaf1864InnerLog = true := by
  rfl'

private theorem leaf1864InnerLogValid :
    leaf1864InnerLog.Valid 8 (innerAD leaf1864Box) :=
  wideLogDataValid_of_cachedCheck endpoint34PositiveFacts
    endpoint119PositiveFacts.valid leaf1864CoverageChecked

private noncomputable def leaf1864InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1864InputLogOnePlusV_eq :
    leaf1864InputLogOnePlusV = outerEnclosure 24
      (leaf1864Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1864RoundedFacts : LeafRoundedFacts 8
    leaf1864Certificate.logOnePlusV leaf1864InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1864InputLogOnePlusV_eq }

private noncomputable def leaf1864Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi149InputQChi innerPair139Input
    leaf1864InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1864LowerChecked :
    lowerCheck 24 leaf1864Box leaf1864Inputs = true := by
  rfl'

private theorem leaf1864CoversExact : CoversExact 8
    leaf1864Box leaf1864Certificate leaf1864InnerLog leaf1864Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi149RoundedFacts
    innerPair139RoundedFacts leaf1864RoundedFacts (by rfl)

private theorem leaf1864FlatSound : Sound leaf1864Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1864CertificateValid
    leaf1864InnerLogValid leaf1864CoversExact leaf1864LowerChecked

private noncomputable def leaf1865Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1865Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871221/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (753224501/536870912) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048563/1048549) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1865InnerLog : WideLogData :=
  innerPair139Data

set_option maxRecDepth 1000000 in
private theorem leaf1865LocalValidity :
    LeafFacts leaf1865Box leaf1865Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1865Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048549) }) = true
      norm_num [leaf1865Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1865CertificateValid :
    WideCertificateValid leaf1865Box leaf1865Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi149ValidityFacts
    leaf1865LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1865CoverageChecked :
    coverageCheck (innerAD leaf1865Box) leaf1865InnerLog = true := by
  rfl'

private theorem leaf1865InnerLogValid :
    leaf1865InnerLog.Valid 8 (innerAD leaf1865Box) :=
  wideLogDataValid_of_cachedCheck endpoint34PositiveFacts
    endpoint119PositiveFacts.valid leaf1865CoverageChecked

private noncomputable def leaf1865InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1865InputLogOnePlusV_eq :
    leaf1865InputLogOnePlusV = outerEnclosure 24
      (leaf1865Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1865RoundedFacts : LeafRoundedFacts 8
    leaf1865Certificate.logOnePlusV leaf1865InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1865InputLogOnePlusV_eq }

private noncomputable def leaf1865Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi149InputQChi innerPair139Input
    leaf1865InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1865LowerChecked :
    lowerCheck 24 leaf1865Box leaf1865Inputs = true := by
  rfl'

private theorem leaf1865CoversExact : CoversExact 8
    leaf1865Box leaf1865Certificate leaf1865InnerLog leaf1865Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi149RoundedFacts
    innerPair139RoundedFacts leaf1865RoundedFacts (by rfl)

private theorem leaf1865FlatSound : Sound leaf1865Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1865CertificateValid
    leaf1865InnerLogValid leaf1865CoversExact leaf1865LowerChecked

private noncomputable def leaf1866Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (27/256), chiHi := (55/512) }

private noncomputable def leaf1866Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742187/1073741824) }, vSqrt := { lower := (8191/8192), upper := (268435712/268428471) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1519588423/1073741824) }, upper := { exponent := 0, mantissa := (23369/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi165LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (536864183/536856942) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1866InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1866LocalValidity :
    LeafFacts leaf1866Box leaf1866Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1866Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (268435712/268428471) }) = true
      norm_num [leaf1866Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1866CertificateValid :
    WideCertificateValid leaf1866Box leaf1866Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi165ValidityFacts
    leaf1866LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1866CoverageChecked :
    coverageCheck (innerAD leaf1866Box) leaf1866InnerLog = true := by
  rfl'

private theorem leaf1866InnerLogValid :
    leaf1866InnerLog.Valid 8 (innerAD leaf1866Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1866CoverageChecked

private noncomputable def leaf1866InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1866InputLogOnePlusV_eq :
    leaf1866InputLogOnePlusV = outerEnclosure 24
      (leaf1866Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1866RoundedFacts : LeafRoundedFacts 8
    leaf1866Certificate.logOnePlusV leaf1866InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1866InputLogOnePlusV_eq }

private noncomputable def leaf1866Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi165InputQChi innerPair26Input
    leaf1866InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1866LowerChecked :
    lowerCheck 24 leaf1866Box leaf1866Inputs = true := by
  rfl'

private theorem leaf1866CoversExact : CoversExact 8
    leaf1866Box leaf1866Certificate leaf1866InnerLog leaf1866Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi165RoundedFacts
    innerPair26RoundedFacts leaf1866RoundedFacts (by rfl)

private theorem leaf1866FlatSound : Sound leaf1866Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1866CertificateValid
    leaf1866InnerLogValid leaf1866CoversExact leaf1866LowerChecked

private noncomputable def leaf1867Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (55/512), chiHi := (7/64) }

private noncomputable def leaf1867Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742189/1073741824) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553543) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1527845453/1073741824) }, upper := { exponent := 0, mantissa := (2937/2048) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi166LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108007/67107086) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1867InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1867LocalValidity :
    LeafFacts leaf1867Box leaf1867Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1867Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553543) }) = true
      norm_num [leaf1867Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1867CertificateValid :
    WideCertificateValid leaf1867Box leaf1867Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi166ValidityFacts
    leaf1867LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1867CoverageChecked :
    coverageCheck (innerAD leaf1867Box) leaf1867InnerLog = true := by
  rfl'

private theorem leaf1867InnerLogValid :
    leaf1867InnerLog.Valid 8 (innerAD leaf1867Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1867CoverageChecked

private noncomputable def leaf1867InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1867InputLogOnePlusV_eq :
    leaf1867InputLogOnePlusV = outerEnclosure 24
      (leaf1867Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1867RoundedFacts : LeafRoundedFacts 8
    leaf1867Certificate.logOnePlusV leaf1867InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1867InputLogOnePlusV_eq }

private noncomputable def leaf1867Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi166InputQChi innerPair26Input
    leaf1867InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1867LowerChecked :
    lowerCheck 24 leaf1867Box leaf1867Inputs = true := by
  rfl'

private theorem leaf1867CoversExact : CoversExact 8
    leaf1867Box leaf1867Certificate leaf1867InnerLog leaf1867Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi166RoundedFacts
    innerPair26RoundedFacts leaf1867RoundedFacts (by rfl)

private theorem leaf1867FlatSound : Sound leaf1867Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1867CertificateValid
    leaf1867InnerLogValid leaf1867CoversExact leaf1867LowerChecked

private noncomputable def leaf1868Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (27/256), chiHi := (55/512) }

private noncomputable def leaf1868Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742189/1073741824) }, vSqrt := { lower := (65527/65536), upper := (2097154/2097097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1523127149/1073741824) }, upper := { exponent := 0, mantissa := (183/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi165LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (4194251/4194194) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1868InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1868LocalValidity :
    LeafFacts leaf1868Box leaf1868Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1868Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (2097154/2097097) }) = true
      norm_num [leaf1868Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1868CertificateValid :
    WideCertificateValid leaf1868Box leaf1868Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi165ValidityFacts
    leaf1868LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1868CoverageChecked :
    coverageCheck (innerAD leaf1868Box) leaf1868InnerLog = true := by
  rfl'

private theorem leaf1868InnerLogValid :
    leaf1868InnerLog.Valid 8 (innerAD leaf1868Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1868CoverageChecked

private noncomputable def leaf1868InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1868InputLogOnePlusV_eq :
    leaf1868InputLogOnePlusV = outerEnclosure 24
      (leaf1868Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1868RoundedFacts : LeafRoundedFacts 8
    leaf1868Certificate.logOnePlusV leaf1868InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1868InputLogOnePlusV_eq }

private noncomputable def leaf1868Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi165InputQChi innerPair26Input
    leaf1868InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1868LowerChecked :
    lowerCheck 24 leaf1868Box leaf1868Inputs = true := by
  rfl'

private theorem leaf1868CoversExact : CoversExact 8
    leaf1868Box leaf1868Certificate leaf1868InnerLog leaf1868Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi165RoundedFacts
    innerPair26RoundedFacts leaf1868RoundedFacts (by rfl)

private theorem leaf1868FlatSound : Sound leaf1868Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1868CertificateValid
    leaf1868InnerLogValid leaf1868CoversExact leaf1868LowerChecked

private noncomputable def leaf1869Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (55/512), chiHi := (7/64) }

private noncomputable def leaf1869Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742191/1073741824) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048548) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1531449711/1073741824) }, upper := { exponent := 0, mantissa := (23/16) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi166LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097125/2097096) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1869InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1869LocalValidity :
    LeafFacts leaf1869Box leaf1869Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1869Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048548) }) = true
      norm_num [leaf1869Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1869CertificateValid :
    WideCertificateValid leaf1869Box leaf1869Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi166ValidityFacts
    leaf1869LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1869CoverageChecked :
    coverageCheck (innerAD leaf1869Box) leaf1869InnerLog = true := by
  rfl'

private theorem leaf1869InnerLogValid :
    leaf1869InnerLog.Valid 8 (innerAD leaf1869Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1869CoverageChecked

private noncomputable def leaf1869InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1869InputLogOnePlusV_eq :
    leaf1869InputLogOnePlusV = outerEnclosure 24
      (leaf1869Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1869RoundedFacts : LeafRoundedFacts 8
    leaf1869Certificate.logOnePlusV leaf1869InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1869InputLogOnePlusV_eq }

private noncomputable def leaf1869Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi166InputQChi innerPair26Input
    leaf1869InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1869LowerChecked :
    lowerCheck 24 leaf1869Box leaf1869Inputs = true := by
  rfl'

private theorem leaf1869CoversExact : CoversExact 8
    leaf1869Box leaf1869Certificate leaf1869InnerLog leaf1869Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi166RoundedFacts
    innerPair26RoundedFacts leaf1869RoundedFacts (by rfl)

private theorem leaf1869FlatSound : Sound leaf1869Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1869CertificateValid
    leaf1869InnerLogValid leaf1869CoversExact leaf1869LowerChecked

private noncomputable def component41Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node0_sound : Sound component41Node0Box :=
  sound_of_literal_split component41Node0Box leaf1836Box leaf1837Box
    .k (121/32) (by rfl) (by rfl)
    leaf1836FlatSound leaf1837FlatSound

private noncomputable def component41Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node1_sound : Sound component41Node1Box :=
  sound_of_literal_split component41Node1Box leaf1838Box leaf1839Box
    .k (121/32) (by rfl) (by rfl)
    leaf1838FlatSound leaf1839FlatSound

private noncomputable def component41Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node2_sound : Sound component41Node2Box :=
  sound_of_literal_split component41Node2Box component41Node0Box component41Node1Box
    .chi (25/256) (by rfl) (by rfl)
    component41Node0_sound component41Node1_sound

private noncomputable def component41Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node3_sound : Sound component41Node3Box :=
  sound_of_literal_split component41Node3Box leaf1840Box leaf1841Box
    .k (123/32) (by rfl) (by rfl)
    leaf1840FlatSound leaf1841FlatSound

private noncomputable def component41Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node4_sound : Sound component41Node4Box :=
  sound_of_literal_split component41Node4Box leaf1842Box leaf1843Box
    .k (123/32) (by rfl) (by rfl)
    leaf1842FlatSound leaf1843FlatSound

private noncomputable def component41Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node5_sound : Sound component41Node5Box :=
  sound_of_literal_split component41Node5Box component41Node3Box component41Node4Box
    .chi (25/256) (by rfl) (by rfl)
    component41Node3_sound component41Node4_sound

private noncomputable def component41Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node6_sound : Sound component41Node6Box :=
  sound_of_literal_split component41Node6Box component41Node2Box component41Node5Box
    .k (61/16) (by rfl) (by rfl)
    component41Node2_sound component41Node5_sound

private noncomputable def component41Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node7_sound : Sound component41Node7Box :=
  sound_of_literal_split component41Node7Box leaf1844Box leaf1845Box
    .k (121/32) (by rfl) (by rfl)
    leaf1844FlatSound leaf1845FlatSound

private noncomputable def component41Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node8_sound : Sound component41Node8Box :=
  sound_of_literal_split component41Node8Box leaf1846Box leaf1847Box
    .k (121/32) (by rfl) (by rfl)
    leaf1846FlatSound leaf1847FlatSound

private noncomputable def component41Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node9_sound : Sound component41Node9Box :=
  sound_of_literal_split component41Node9Box component41Node7Box component41Node8Box
    .chi (27/256) (by rfl) (by rfl)
    component41Node7_sound component41Node8_sound

private noncomputable def component41Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node10_sound : Sound component41Node10Box :=
  sound_of_literal_split component41Node10Box leaf1848Box leaf1849Box
    .k (123/32) (by rfl) (by rfl)
    leaf1848FlatSound leaf1849FlatSound

private noncomputable def component41Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node11_sound : Sound component41Node11Box :=
  sound_of_literal_split component41Node11Box leaf1850Box leaf1851Box
    .k (123/32) (by rfl) (by rfl)
    leaf1850FlatSound leaf1851FlatSound

private noncomputable def component41Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node12_sound : Sound component41Node12Box :=
  sound_of_literal_split component41Node12Box component41Node10Box component41Node11Box
    .chi (27/256) (by rfl) (by rfl)
    component41Node10_sound component41Node11_sound

private noncomputable def component41Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node13_sound : Sound component41Node13Box :=
  sound_of_literal_split component41Node13Box component41Node9Box component41Node12Box
    .k (61/16) (by rfl) (by rfl)
    component41Node9_sound component41Node12_sound

private noncomputable def component41Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node14_sound : Sound component41Node14Box :=
  sound_of_literal_split component41Node14Box component41Node6Box component41Node13Box
    .chi (13/128) (by rfl) (by rfl)
    component41Node6_sound component41Node13_sound

private noncomputable def component41Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node15_sound : Sound component41Node15Box :=
  sound_of_literal_split component41Node15Box leaf1852Box leaf1853Box
    .k (125/32) (by rfl) (by rfl)
    leaf1852FlatSound leaf1853FlatSound

private noncomputable def component41Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node16_sound : Sound component41Node16Box :=
  sound_of_literal_split component41Node16Box leaf1854Box leaf1855Box
    .k (125/32) (by rfl) (by rfl)
    leaf1854FlatSound leaf1855FlatSound

private noncomputable def component41Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node17_sound : Sound component41Node17Box :=
  sound_of_literal_split component41Node17Box component41Node15Box component41Node16Box
    .chi (25/256) (by rfl) (by rfl)
    component41Node15_sound component41Node16_sound

private noncomputable def component41Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node18_sound : Sound component41Node18Box :=
  sound_of_literal_split component41Node18Box leaf1856Box leaf1857Box
    .k (127/32) (by rfl) (by rfl)
    leaf1856FlatSound leaf1857FlatSound

private noncomputable def component41Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node19_sound : Sound component41Node19Box :=
  sound_of_literal_split component41Node19Box leaf1858Box leaf1859Box
    .k (127/32) (by rfl) (by rfl)
    leaf1858FlatSound leaf1859FlatSound

private noncomputable def component41Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node20_sound : Sound component41Node20Box :=
  sound_of_literal_split component41Node20Box component41Node18Box component41Node19Box
    .chi (25/256) (by rfl) (by rfl)
    component41Node18_sound component41Node19_sound

private noncomputable def component41Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component41Node21_sound : Sound component41Node21Box :=
  sound_of_literal_split component41Node21Box component41Node17Box component41Node20Box
    .k (63/16) (by rfl) (by rfl)
    component41Node17_sound component41Node20_sound

private noncomputable def component41Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node22_sound : Sound component41Node22Box :=
  sound_of_literal_split component41Node22Box leaf1860Box leaf1861Box
    .k (125/32) (by rfl) (by rfl)
    leaf1860FlatSound leaf1861FlatSound

private noncomputable def component41Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node23_sound : Sound component41Node23Box :=
  sound_of_literal_split component41Node23Box leaf1862Box leaf1863Box
    .k (125/32) (by rfl) (by rfl)
    leaf1862FlatSound leaf1863FlatSound

private noncomputable def component41Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node24_sound : Sound component41Node24Box :=
  sound_of_literal_split component41Node24Box component41Node22Box component41Node23Box
    .chi (27/256) (by rfl) (by rfl)
    component41Node22_sound component41Node23_sound

private noncomputable def component41Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component41Node25_sound : Sound component41Node25Box :=
  sound_of_literal_split component41Node25Box leaf1864Box leaf1865Box
    .k (127/32) (by rfl) (by rfl)
    leaf1864FlatSound leaf1865FlatSound

private noncomputable def component41Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node26_sound : Sound component41Node26Box :=
  sound_of_literal_split component41Node26Box leaf1866Box leaf1867Box
    .chi (55/512) (by rfl) (by rfl)
    leaf1866FlatSound leaf1867FlatSound

private noncomputable def component41Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node27_sound : Sound component41Node27Box :=
  sound_of_literal_split component41Node27Box leaf1868Box leaf1869Box
    .chi (55/512) (by rfl) (by rfl)
    leaf1868FlatSound leaf1869FlatSound

private noncomputable def component41Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node28_sound : Sound component41Node28Box :=
  sound_of_literal_split component41Node28Box component41Node26Box component41Node27Box
    .k (127/32) (by rfl) (by rfl)
    component41Node26_sound component41Node27_sound

private noncomputable def component41Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node29_sound : Sound component41Node29Box :=
  sound_of_literal_split component41Node29Box component41Node25Box component41Node28Box
    .chi (27/256) (by rfl) (by rfl)
    component41Node25_sound component41Node28_sound

private noncomputable def component41Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node30_sound : Sound component41Node30Box :=
  sound_of_literal_split component41Node30Box component41Node24Box component41Node29Box
    .k (63/16) (by rfl) (by rfl)
    component41Node24_sound component41Node29_sound

private noncomputable def component41Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component41Node31_sound : Sound component41Node31Box :=
  sound_of_literal_split component41Node31Box component41Node21Box component41Node30Box
    .chi (13/128) (by rfl) (by rfl)
    component41Node21_sound component41Node30_sound

noncomputable def component41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
theorem component41_sound : Sound component41Box :=
  sound_of_literal_split component41Box component41Node14Box component41Node31Box
    .k (31/8) (by rfl) (by rfl)
    component41Node14_sound component41Node31_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
