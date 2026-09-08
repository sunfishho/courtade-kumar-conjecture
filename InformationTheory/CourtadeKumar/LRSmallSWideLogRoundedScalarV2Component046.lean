import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
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

private noncomputable def leaf2101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871203/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717272576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (809450975/536870912) }, upper := { exponent := 0, mantissa := (12497/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435766271/137434545152) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2101InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2101LocalValidity :
    LeafFacts leaf2101Box leaf2101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717272576) }) = true
      norm_num [leaf2101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2101CertificateValid :
    WideCertificateValid leaf2101Box leaf2101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi183ValidityFacts
    leaf2101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2101CoverageChecked :
    coverageCheck (innerAD leaf2101Box) leaf2101InnerLog = true := by
  rfl'

private theorem leaf2101InnerLogValid :
    leaf2101InnerLog.Valid 8 (innerAD leaf2101Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2101CoverageChecked

private noncomputable def leaf2101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2101InputLogOnePlusV_eq :
    leaf2101InputLogOnePlusV = outerEnclosure 24
      (leaf2101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2101RoundedFacts : LeafRoundedFacts 8
    leaf2101Certificate.logOnePlusV leaf2101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2101InputLogOnePlusV_eq }

private noncomputable def leaf2101Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi183InputQChi innerPair40Input
    leaf2101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2101LowerChecked :
    lowerCheck 24 leaf2101Box leaf2101Inputs = true := by
  rfl'

private theorem leaf2101CoversExact : CoversExact 8
    leaf2101Box leaf2101Certificate leaf2101InnerLog leaf2101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi183RoundedFacts
    innerPair40RoundedFacts leaf2101RoundedFacts (by rfl)

private theorem leaf2101FlatSound : Sound leaf2101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2101CertificateValid
    leaf2101InnerLogValid leaf2101CoversExact leaf2101LowerChecked

private noncomputable def leaf2102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717218816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (816266301/536870912) }, upper := { exponent := 0, mantissa := (6301/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435712511/137434437632) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2102InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2102LocalValidity :
    LeafFacts leaf2102Box leaf2102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717218816) }) = true
      norm_num [leaf2102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2102CertificateValid :
    WideCertificateValid leaf2102Box leaf2102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi184ValidityFacts
    leaf2102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2102CoverageChecked :
    coverageCheck (innerAD leaf2102Box) leaf2102InnerLog = true := by
  rfl'

private theorem leaf2102InnerLogValid :
    leaf2102InnerLog.Valid 8 (innerAD leaf2102Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2102CoverageChecked

private noncomputable def leaf2102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2102InputLogOnePlusV_eq :
    leaf2102InputLogOnePlusV = outerEnclosure 24
      (leaf2102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2102RoundedFacts : LeafRoundedFacts 8
    leaf2102Certificate.logOnePlusV leaf2102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2102InputLogOnePlusV_eq }

private noncomputable def leaf2102Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2102LowerChecked :
    lowerCheck 24 leaf2102Box leaf2102Inputs = true := by
  rfl'

private theorem leaf2102CoversExact : CoversExact 8
    leaf2102Box leaf2102Certificate leaf2102InnerLog leaf2102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2102RoundedFacts (by rfl)

private theorem leaf2102FlatSound : Sound leaf2102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2102CertificateValid
    leaf2102InnerLogValid leaf2102CoversExact leaf2102LowerChecked

private noncomputable def leaf2103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871205/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905750528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (812072253/536870912) }, upper := { exponent := 0, mantissa := (6269/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811915093/45811501056) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2103InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2103LocalValidity :
    LeafFacts leaf2103Box leaf2103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905750528) }) = true
      norm_num [leaf2103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2103CertificateValid :
    WideCertificateValid leaf2103Box leaf2103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi183ValidityFacts
    leaf2103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2103CoverageChecked :
    coverageCheck (innerAD leaf2103Box) leaf2103InnerLog = true := by
  rfl'

private theorem leaf2103InnerLogValid :
    leaf2103InnerLog.Valid 8 (innerAD leaf2103Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2103CoverageChecked

private noncomputable def leaf2103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2103InputLogOnePlusV_eq :
    leaf2103InputLogOnePlusV = outerEnclosure 24
      (leaf2103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2103RoundedFacts : LeafRoundedFacts 8
    leaf2103Certificate.logOnePlusV leaf2103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2103InputLogOnePlusV_eq }

private noncomputable def leaf2103Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi183InputQChi innerPair40Input
    leaf2103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2103LowerChecked :
    lowerCheck 24 leaf2103Box leaf2103Inputs = true := by
  rfl'

private theorem leaf2103CoversExact : CoversExact 8
    leaf2103Box leaf2103Certificate leaf2103InnerLog leaf2103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi183RoundedFacts
    innerPair40RoundedFacts leaf2103RoundedFacts (by rfl)

private theorem leaf2103FlatSound : Sound leaf2103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2103CertificateValid
    leaf2103InnerLogValid leaf2103CoversExact leaf2103LowerChecked

private noncomputable def leaf2104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717197312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (818953111/536870912) }, upper := { exponent := 0, mantissa := (3161/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435691007/137434394624) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2104InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2104LocalValidity :
    LeafFacts leaf2104Box leaf2104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717197312) }) = true
      norm_num [leaf2104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2104CertificateValid :
    WideCertificateValid leaf2104Box leaf2104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi184ValidityFacts
    leaf2104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2104CoverageChecked :
    coverageCheck (innerAD leaf2104Box) leaf2104InnerLog = true := by
  rfl'

private theorem leaf2104InnerLogValid :
    leaf2104InnerLog.Valid 8 (innerAD leaf2104Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2104CoverageChecked

private noncomputable def leaf2104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2104InputLogOnePlusV_eq :
    leaf2104InputLogOnePlusV = outerEnclosure 24
      (leaf2104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2104RoundedFacts : LeafRoundedFacts 8
    leaf2104Certificate.logOnePlusV leaf2104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2104InputLogOnePlusV_eq }

private noncomputable def leaf2104Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2104LowerChecked :
    lowerCheck 24 leaf2104Box leaf2104Inputs = true := by
  rfl'

private theorem leaf2104CoversExact : CoversExact 8
    leaf2104Box leaf2104Certificate leaf2104InnerLog leaf2104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2104RoundedFacts (by rfl)

private theorem leaf2104FlatSound : Sound leaf2104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2104CertificateValid
    leaf2104InnerLogValid leaf2104CoversExact leaf2104LowerChecked

private noncomputable def leaf2105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717165056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (823081627/536870912) }, upper := { exponent := 0, mantissa := (12707/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435658751/137434330112) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2105InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2105LocalValidity :
    LeafFacts leaf2105Box leaf2105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717165056) }) = true
      norm_num [leaf2105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2105CertificateValid :
    WideCertificateValid leaf2105Box leaf2105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi185ValidityFacts
    leaf2105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2105CoverageChecked :
    coverageCheck (innerAD leaf2105Box) leaf2105InnerLog = true := by
  rfl'

private theorem leaf2105InnerLogValid :
    leaf2105InnerLog.Valid 8 (innerAD leaf2105Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2105CoverageChecked

private noncomputable def leaf2105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2105InputLogOnePlusV_eq :
    leaf2105InputLogOnePlusV = outerEnclosure 24
      (leaf2105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2105RoundedFacts : LeafRoundedFacts 8
    leaf2105Certificate.logOnePlusV leaf2105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2105InputLogOnePlusV_eq }

private noncomputable def leaf2105Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi185InputQChi innerPair40Input
    leaf2105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2105LowerChecked :
    lowerCheck 24 leaf2105Box leaf2105Inputs = true := by
  rfl'

private theorem leaf2105CoversExact : CoversExact 8
    leaf2105Box leaf2105Certificate leaf2105InnerLog leaf2105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf2105RoundedFacts (by rfl)

private theorem leaf2105FlatSound : Sound leaf2105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2105CertificateValid
    leaf2105InnerLogValid leaf2105CoversExact leaf2105LowerChecked

private noncomputable def leaf2106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717111296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (829896953/536870912) }, upper := { exponent := 0, mantissa := (3203/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435604991/137434222592) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2106InnerLog : WideLogData :=
  innerPair87Data

set_option maxRecDepth 1000000 in
private theorem leaf2106LocalValidity :
    LeafFacts leaf2106Box leaf2106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717111296) }) = true
      norm_num [leaf2106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2106CertificateValid :
    WideCertificateValid leaf2106Box leaf2106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi186ValidityFacts
    leaf2106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2106CoverageChecked :
    coverageCheck (innerAD leaf2106Box) leaf2106InnerLog = true := by
  rfl'

private theorem leaf2106InnerLogValid :
    leaf2106InnerLog.Valid 8 (innerAD leaf2106Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint47PositiveFacts.valid leaf2106CoverageChecked

private noncomputable def leaf2106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2106InputLogOnePlusV_eq :
    leaf2106InputLogOnePlusV = outerEnclosure 24
      (leaf2106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2106RoundedFacts : LeafRoundedFacts 8
    leaf2106Certificate.logOnePlusV leaf2106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2106InputLogOnePlusV_eq }

private noncomputable def leaf2106Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi186InputQChi innerPair87Input
    leaf2106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2106LowerChecked :
    lowerCheck 24 leaf2106Box leaf2106Inputs = true := by
  rfl'

private theorem leaf2106CoversExact : CoversExact 8
    leaf2106Box leaf2106Certificate leaf2106InnerLog leaf2106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi186RoundedFacts
    innerPair87RoundedFacts leaf2106RoundedFacts (by rfl)

private theorem leaf2106FlatSound : Sound leaf2106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2106CertificateValid
    leaf2106InnerLogValid leaf2106CoversExact leaf2106LowerChecked

private noncomputable def leaf2107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743428608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (825833969/536870912) }, upper := { exponent := 0, mantissa := (6375/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487127347/27486857216) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2107InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2107LocalValidity :
    LeafFacts leaf2107Box leaf2107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743428608) }) = true
      norm_num [leaf2107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2107CertificateValid :
    WideCertificateValid leaf2107Box leaf2107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi185ValidityFacts
    leaf2107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2107CoverageChecked :
    coverageCheck (innerAD leaf2107Box) leaf2107InnerLog = true := by
  rfl'

private theorem leaf2107InnerLogValid :
    leaf2107InnerLog.Valid 8 (innerAD leaf2107Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2107CoverageChecked

private noncomputable def leaf2107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2107InputLogOnePlusV_eq :
    leaf2107InputLogOnePlusV = outerEnclosure 24
      (leaf2107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2107RoundedFacts : LeafRoundedFacts 8
    leaf2107Certificate.logOnePlusV leaf2107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2107InputLogOnePlusV_eq }

private noncomputable def leaf2107Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi185InputQChi innerPair40Input
    leaf2107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2107LowerChecked :
    lowerCheck 24 leaf2107Box leaf2107Inputs = true := by
  rfl'

private theorem leaf2107CoversExact : CoversExact 8
    leaf2107Box leaf2107Certificate leaf2107InnerLog leaf2107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf2107RoundedFacts (by rfl)

private theorem leaf2107FlatSound : Sound leaf2107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2107CertificateValid
    leaf2107InnerLogValid leaf2107CoversExact leaf2107LowerChecked

private noncomputable def leaf2108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905696256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (832714827/536870912) }, upper := { exponent := 0, mantissa := (1607/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811860821/45811392512) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2108InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2108LocalValidity :
    LeafFacts leaf2108Box leaf2108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905696256) }) = true
      norm_num [leaf2108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2108CertificateValid :
    WideCertificateValid leaf2108Box leaf2108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi186ValidityFacts
    leaf2108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2108CoverageChecked :
    coverageCheck (innerAD leaf2108Box) leaf2108InnerLog = true := by
  rfl'

private theorem leaf2108InnerLogValid :
    leaf2108InnerLog.Valid 8 (innerAD leaf2108Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2108CoverageChecked

private noncomputable def leaf2108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2108InputLogOnePlusV_eq :
    leaf2108InputLogOnePlusV = outerEnclosure 24
      (leaf2108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2108RoundedFacts : LeafRoundedFacts 8
    leaf2108Certificate.logOnePlusV leaf2108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2108InputLogOnePlusV_eq }

private noncomputable def leaf2108Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi186InputQChi innerPair156Input
    leaf2108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2108LowerChecked :
    lowerCheck 24 leaf2108Box leaf2108Inputs = true := by
  rfl'

private theorem leaf2108CoversExact : CoversExact 8
    leaf2108Box leaf2108Certificate leaf2108InnerLog leaf2108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi186RoundedFacts
    innerPair156RoundedFacts leaf2108RoundedFacts (by rfl)

private theorem leaf2108FlatSound : Sound leaf2108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2108CertificateValid
    leaf2108InnerLogValid leaf2108CoversExact leaf2108LowerChecked

private noncomputable def leaf2109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871207/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717230592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (814693531/536870912) }, upper := { exponent := 0, mantissa := (12579/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435724287/137434461184) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2109InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2109LocalValidity :
    LeafFacts leaf2109Box leaf2109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717230592) }) = true
      norm_num [leaf2109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2109CertificateValid :
    WideCertificateValid leaf2109Box leaf2109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi183ValidityFacts
    leaf2109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2109CoverageChecked :
    coverageCheck (innerAD leaf2109Box) leaf2109InnerLog = true := by
  rfl'

private theorem leaf2109InnerLogValid :
    leaf2109InnerLog.Valid 8 (innerAD leaf2109Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2109CoverageChecked

private noncomputable def leaf2109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2109InputLogOnePlusV_eq :
    leaf2109InputLogOnePlusV = outerEnclosure 24
      (leaf2109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2109RoundedFacts : LeafRoundedFacts 8
    leaf2109Certificate.logOnePlusV leaf2109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2109InputLogOnePlusV_eq }

private noncomputable def leaf2109Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi183InputQChi innerPair40Input
    leaf2109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2109LowerChecked :
    lowerCheck 24 leaf2109Box leaf2109Inputs = true := by
  rfl'

private theorem leaf2109CoversExact : CoversExact 8
    leaf2109Box leaf2109Certificate leaf2109InnerLog leaf2109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi183RoundedFacts
    innerPair40RoundedFacts leaf2109RoundedFacts (by rfl)

private theorem leaf2109FlatSound : Sound leaf2109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2109CertificateValid
    leaf2109InnerLogValid leaf2109CoversExact leaf2109LowerChecked

private noncomputable def leaf2110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717175808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (821639921/536870912) }, upper := { exponent := 0, mantissa := (6343/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435669503/137434351616) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2110InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2110LocalValidity :
    LeafFacts leaf2110Box leaf2110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717175808) }) = true
      norm_num [leaf2110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2110CertificateValid :
    WideCertificateValid leaf2110Box leaf2110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi184ValidityFacts
    leaf2110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2110CoverageChecked :
    coverageCheck (innerAD leaf2110Box) leaf2110InnerLog = true := by
  rfl'

private theorem leaf2110InnerLogValid :
    leaf2110InnerLog.Valid 8 (innerAD leaf2110Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2110CoverageChecked

private noncomputable def leaf2110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2110InputLogOnePlusV_eq :
    leaf2110InputLogOnePlusV = outerEnclosure 24
      (leaf2110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2110RoundedFacts : LeafRoundedFacts 8
    leaf2110Certificate.logOnePlusV leaf2110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2110InputLogOnePlusV_eq }

private noncomputable def leaf2110Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2110LowerChecked :
    lowerCheck 24 leaf2110Box leaf2110Inputs = true := by
  rfl'

private theorem leaf2110CoversExact : CoversExact 8
    leaf2110Box leaf2110Certificate leaf2110InnerLog leaf2110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2110RoundedFacts (by rfl)

private theorem leaf2110FlatSound : Sound leaf2110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2110CertificateValid
    leaf2110InnerLogValid leaf2110CoversExact leaf2110LowerChecked

private noncomputable def leaf2111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (5/32), chiHi := (41/256) }

private noncomputable def leaf2111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871209/536870912) }, vSqrt := { lower := (65529/65536), upper := (808452867/808437760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (817314809/536870912) }, upper := { exponent := 0, mantissa := (3155/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi183LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1616890627/1616875520) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2111InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2111LocalValidity :
    LeafFacts leaf2111Box leaf2111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (808452867/808437760) }) = true
      norm_num [leaf2111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2111CertificateValid :
    WideCertificateValid leaf2111Box leaf2111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi183ValidityFacts
    leaf2111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2111CoverageChecked :
    coverageCheck (innerAD leaf2111Box) leaf2111InnerLog = true := by
  rfl'

private theorem leaf2111InnerLogValid :
    leaf2111InnerLog.Valid 8 (innerAD leaf2111Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2111CoverageChecked

private noncomputable def leaf2111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2111InputLogOnePlusV_eq :
    leaf2111InputLogOnePlusV = outerEnclosure 24
      (leaf2111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2111RoundedFacts : LeafRoundedFacts 8
    leaf2111Certificate.logOnePlusV leaf2111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2111InputLogOnePlusV_eq }

private noncomputable def leaf2111Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi183InputQChi innerPair40Input
    leaf2111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2111LowerChecked :
    lowerCheck 24 leaf2111Box leaf2111Inputs = true := by
  rfl'

private theorem leaf2111CoversExact : CoversExact 8
    leaf2111Box leaf2111Certificate leaf2111InnerLog leaf2111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi183RoundedFacts
    innerPair40RoundedFacts leaf2111RoundedFacts (by rfl)

private theorem leaf2111FlatSound : Sound leaf2111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2111CertificateValid
    leaf2111InnerLogValid leaf2111CoversExact leaf2111LowerChecked

private noncomputable def leaf2112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (41/256), chiHi := (21/128) }

private noncomputable def leaf2112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717154304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (824326731/536870912) }, upper := { exponent := 0, mantissa := (1591/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi184LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435647999/137434308608) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2112InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2112LocalValidity :
    LeafFacts leaf2112Box leaf2112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717154304) }) = true
      norm_num [leaf2112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2112CertificateValid :
    WideCertificateValid leaf2112Box leaf2112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi184ValidityFacts
    leaf2112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2112CoverageChecked :
    coverageCheck (innerAD leaf2112Box) leaf2112InnerLog = true := by
  rfl'

private theorem leaf2112InnerLogValid :
    leaf2112InnerLog.Valid 8 (innerAD leaf2112Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2112CoverageChecked

private noncomputable def leaf2112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2112InputLogOnePlusV_eq :
    leaf2112InputLogOnePlusV = outerEnclosure 24
      (leaf2112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2112RoundedFacts : LeafRoundedFacts 8
    leaf2112Certificate.logOnePlusV leaf2112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2112InputLogOnePlusV_eq }

private noncomputable def leaf2112Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi184InputQChi innerPair40Input
    leaf2112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2112LowerChecked :
    lowerCheck 24 leaf2112Box leaf2112Inputs = true := by
  rfl'

private theorem leaf2112CoversExact : CoversExact 8
    leaf2112Box leaf2112Certificate leaf2112InnerLog leaf2112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi184RoundedFacts
    innerPair40RoundedFacts leaf2112RoundedFacts (by rfl)

private theorem leaf2112FlatSound : Sound leaf2112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2112CertificateValid
    leaf2112InnerLogValid leaf2112CoversExact leaf2112LowerChecked

private noncomputable def leaf2113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905707008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (828586311/536870912) }, upper := { exponent := 0, mantissa := (12793/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811871573/45811414016) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2113InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2113LocalValidity :
    LeafFacts leaf2113Box leaf2113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905707008) }) = true
      norm_num [leaf2113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2113CertificateValid :
    WideCertificateValid leaf2113Box leaf2113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi185ValidityFacts
    leaf2113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2113CoverageChecked :
    coverageCheck (innerAD leaf2113Box) leaf2113InnerLog = true := by
  rfl'

private theorem leaf2113InnerLogValid :
    leaf2113InnerLog.Valid 8 (innerAD leaf2113Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2113CoverageChecked

private noncomputable def leaf2113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2113InputLogOnePlusV_eq :
    leaf2113InputLogOnePlusV = outerEnclosure 24
      (leaf2113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2113RoundedFacts : LeafRoundedFacts 8
    leaf2113Certificate.logOnePlusV leaf2113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2113InputLogOnePlusV_eq }

private noncomputable def leaf2113Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi185InputQChi innerPair40Input
    leaf2113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2113LowerChecked :
    lowerCheck 24 leaf2113Box leaf2113Inputs = true := by
  rfl'

private theorem leaf2113CoversExact : CoversExact 8
    leaf2113Box leaf2113Certificate leaf2113InnerLog leaf2113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi185RoundedFacts
    innerPair40RoundedFacts leaf2113RoundedFacts (by rfl)

private theorem leaf2113FlatSound : Sound leaf2113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2113CertificateValid
    leaf2113InnerLogValid leaf2113CoversExact leaf2113LowerChecked

private noncomputable def leaf2114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743413248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (835532701/536870912) }, upper := { exponent := 0, mantissa := (3225/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487111987/27486826496) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2114InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2114LocalValidity :
    LeafFacts leaf2114Box leaf2114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743413248) }) = true
      norm_num [leaf2114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2114CertificateValid :
    WideCertificateValid leaf2114Box leaf2114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi186ValidityFacts
    leaf2114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2114CoverageChecked :
    coverageCheck (innerAD leaf2114Box) leaf2114InnerLog = true := by
  rfl'

private theorem leaf2114InnerLogValid :
    leaf2114InnerLog.Valid 8 (innerAD leaf2114Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2114CoverageChecked

private noncomputable def leaf2114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2114InputLogOnePlusV_eq :
    leaf2114InputLogOnePlusV = outerEnclosure 24
      (leaf2114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2114RoundedFacts : LeafRoundedFacts 8
    leaf2114Certificate.logOnePlusV leaf2114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2114InputLogOnePlusV_eq }

private noncomputable def leaf2114Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi186InputQChi innerPair156Input
    leaf2114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2114LowerChecked :
    lowerCheck 24 leaf2114Box leaf2114Inputs = true := by
  rfl'

private theorem leaf2114CoversExact : CoversExact 8
    leaf2114Box leaf2114Certificate leaf2114InnerLog leaf2114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi186RoundedFacts
    innerPair156RoundedFacts leaf2114RoundedFacts (by rfl)

private theorem leaf2114FlatSound : Sound leaf2114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2114CertificateValid
    leaf2114InnerLogValid leaf2114CoversExact leaf2114LowerChecked

private noncomputable def leaf2115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (21/128), chiHi := (43/256) }

private noncomputable def leaf2115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717099008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (831338653/536870912) }, upper := { exponent := 0, mantissa := (3209/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi185LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435592703/137434198016) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2115InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2115LocalValidity :
    LeafFacts leaf2115Box leaf2115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717099008) }) = true
      norm_num [leaf2115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2115CertificateValid :
    WideCertificateValid leaf2115Box leaf2115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi185ValidityFacts
    leaf2115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2115CoverageChecked :
    coverageCheck (innerAD leaf2115Box) leaf2115InnerLog = true := by
  rfl'

private theorem leaf2115InnerLogValid :
    leaf2115InnerLog.Valid 8 (innerAD leaf2115Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2115CoverageChecked

private noncomputable def leaf2115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2115InputLogOnePlusV_eq :
    leaf2115InputLogOnePlusV = outerEnclosure 24
      (leaf2115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2115RoundedFacts : LeafRoundedFacts 8
    leaf2115Certificate.logOnePlusV leaf2115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2115InputLogOnePlusV_eq }

private noncomputable def leaf2115Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi185InputQChi innerPair156Input
    leaf2115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2115LowerChecked :
    lowerCheck 24 leaf2115Box leaf2115Inputs = true := by
  rfl'

private theorem leaf2115CoversExact : CoversExact 8
    leaf2115Box leaf2115Certificate leaf2115InnerLog leaf2115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi185RoundedFacts
    innerPair156RoundedFacts leaf2115RoundedFacts (by rfl)

private theorem leaf2115FlatSound : Sound leaf2115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2115CertificateValid
    leaf2115InnerLogValid leaf2115CoversExact leaf2115LowerChecked

private noncomputable def leaf2116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (43/256), chiHi := (11/64) }

private noncomputable def leaf2116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717043712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (838350575/536870912) }, upper := { exponent := 0, mantissa := (809/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi186LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435537407/137434087424) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2116InnerLog : WideLogData :=
  innerPair450Data

set_option maxRecDepth 1000000 in
private theorem leaf2116LocalValidity :
    LeafFacts leaf2116Box leaf2116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717043712) }) = true
      norm_num [leaf2116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2116CertificateValid :
    WideCertificateValid leaf2116Box leaf2116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi186ValidityFacts
    leaf2116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2116CoverageChecked :
    coverageCheck (innerAD leaf2116Box) leaf2116InnerLog = true := by
  rfl'

private theorem leaf2116InnerLogValid :
    leaf2116InnerLog.Valid 8 (innerAD leaf2116Box) :=
  wideLogDataValid_of_cachedCheck endpoint165PositiveFacts
    endpoint130PositiveFacts.valid leaf2116CoverageChecked

private noncomputable def leaf2116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2116InputLogOnePlusV_eq :
    leaf2116InputLogOnePlusV = outerEnclosure 24
      (leaf2116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2116RoundedFacts : LeafRoundedFacts 8
    leaf2116Certificate.logOnePlusV leaf2116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2116InputLogOnePlusV_eq }

private noncomputable def leaf2116Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi186InputQChi innerPair450Input
    leaf2116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2116LowerChecked :
    lowerCheck 24 leaf2116Box leaf2116Inputs = true := by
  rfl'

private theorem leaf2116CoversExact : CoversExact 8
    leaf2116Box leaf2116Certificate leaf2116InnerLog leaf2116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi186RoundedFacts
    innerPair450RoundedFacts leaf2116RoundedFacts (by rfl)

private theorem leaf2116FlatSound : Sound leaf2116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2116CertificateValid
    leaf2116InnerLogValid leaf2116CoversExact leaf2116LowerChecked

private noncomputable def leaf2117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871211/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717057536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (836712279/536870912) }, upper := { exponent := 0, mantissa := (12917/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435551231/137434115072) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2117InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2117LocalValidity :
    LeafFacts leaf2117Box leaf2117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717057536) }) = true
      norm_num [leaf2117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2117CertificateValid :
    WideCertificateValid leaf2117Box leaf2117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi133ValidityFacts
    leaf2117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2117CoverageChecked :
    coverageCheck (innerAD leaf2117Box) leaf2117InnerLog = true := by
  rfl'

private theorem leaf2117InnerLogValid :
    leaf2117InnerLog.Valid 8 (innerAD leaf2117Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2117CoverageChecked

private noncomputable def leaf2117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2117InputLogOnePlusV_eq :
    leaf2117InputLogOnePlusV = outerEnclosure 24
      (leaf2117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2117RoundedFacts : LeafRoundedFacts 8
    leaf2117Certificate.logOnePlusV leaf2117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2117InputLogOnePlusV_eq }

private noncomputable def leaf2117Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi133InputQChi innerPair156Input
    leaf2117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2117LowerChecked :
    lowerCheck 24 leaf2117Box leaf2117Inputs = true := by
  rfl'

private theorem leaf2117CoversExact : CoversExact 8
    leaf2117Box leaf2117Certificate leaf2117InnerLog leaf2117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi133RoundedFacts
    innerPair156RoundedFacts leaf2117RoundedFacts (by rfl)

private theorem leaf2117FlatSound : Sound leaf2117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2117CertificateValid
    leaf2117InnerLogValid leaf2117CoversExact leaf2117LowerChecked

private noncomputable def leaf2118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717003776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (843527605/536870912) }, upper := { exponent := 0, mantissa := (6511/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435497471/137434007552) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2118InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2118LocalValidity :
    LeafFacts leaf2118Box leaf2118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717003776) }) = true
      norm_num [leaf2118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2118CertificateValid :
    WideCertificateValid leaf2118Box leaf2118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi134ValidityFacts
    leaf2118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2118CoverageChecked :
    coverageCheck (innerAD leaf2118Box) leaf2118InnerLog = true := by
  rfl'

private theorem leaf2118InnerLogValid :
    leaf2118InnerLog.Valid 8 (innerAD leaf2118Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2118CoverageChecked

private noncomputable def leaf2118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2118InputLogOnePlusV_eq :
    leaf2118InputLogOnePlusV = outerEnclosure 24
      (leaf2118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2118RoundedFacts : LeafRoundedFacts 8
    leaf2118Certificate.logOnePlusV leaf2118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2118InputLogOnePlusV_eq }

private noncomputable def leaf2118Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi134InputQChi innerPair54Input
    leaf2118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2118LowerChecked :
    lowerCheck 24 leaf2118Box leaf2118Inputs = true := by
  rfl'

private theorem leaf2118CoversExact : CoversExact 8
    leaf2118Box leaf2118Certificate leaf2118InnerLog leaf2118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi134RoundedFacts
    innerPair54RoundedFacts leaf2118RoundedFacts (by rfl)

private theorem leaf2118FlatSound : Sound leaf2118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2118CertificateValid
    leaf2118InnerLogValid leaf2118CoversExact leaf2118LowerChecked

private noncomputable def leaf2119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871213/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717034496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (839595685/536870912) }, upper := { exponent := 0, mantissa := (6481/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435528191/137434068992) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2119InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2119LocalValidity :
    LeafFacts leaf2119Box leaf2119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717034496) }) = true
      norm_num [leaf2119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2119CertificateValid :
    WideCertificateValid leaf2119Box leaf2119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi133ValidityFacts
    leaf2119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2119CoverageChecked :
    coverageCheck (innerAD leaf2119Box) leaf2119InnerLog = true := by
  rfl'

private theorem leaf2119InnerLogValid :
    leaf2119InnerLog.Valid 8 (innerAD leaf2119Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2119CoverageChecked

private noncomputable def leaf2119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2119InputLogOnePlusV_eq :
    leaf2119InputLogOnePlusV = outerEnclosure 24
      (leaf2119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2119RoundedFacts : LeafRoundedFacts 8
    leaf2119Certificate.logOnePlusV leaf2119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2119InputLogOnePlusV_eq }

private noncomputable def leaf2119Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi133InputQChi innerPair54Input
    leaf2119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2119LowerChecked :
    lowerCheck 24 leaf2119Box leaf2119Inputs = true := by
  rfl'

private theorem leaf2119CoversExact : CoversExact 8
    leaf2119Box leaf2119Certificate leaf2119InnerLog leaf2119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi133RoundedFacts
    innerPair54RoundedFacts leaf2119RoundedFacts (by rfl)

private theorem leaf2119FlatSound : Sound leaf2119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2119CertificateValid
    leaf2119InnerLogValid leaf2119CoversExact leaf2119LowerChecked

private noncomputable def leaf2120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716980224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (846476543/536870912) }, upper := { exponent := 0, mantissa := (3267/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435473919/137433960448) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2120InnerLog : WideLogData :=
  innerPair55Data

set_option maxRecDepth 1000000 in
private theorem leaf2120LocalValidity :
    LeafFacts leaf2120Box leaf2120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716980224) }) = true
      norm_num [leaf2120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2120CertificateValid :
    WideCertificateValid leaf2120Box leaf2120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi134ValidityFacts
    leaf2120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2120CoverageChecked :
    coverageCheck (innerAD leaf2120Box) leaf2120InnerLog = true := by
  rfl'

private theorem leaf2120InnerLogValid :
    leaf2120InnerLog.Valid 8 (innerAD leaf2120Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint46PositiveFacts.valid leaf2120CoverageChecked

private noncomputable def leaf2120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2120InputLogOnePlusV_eq :
    leaf2120InputLogOnePlusV = outerEnclosure 24
      (leaf2120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2120RoundedFacts : LeafRoundedFacts 8
    leaf2120Certificate.logOnePlusV leaf2120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2120InputLogOnePlusV_eq }

private noncomputable def leaf2120Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi134InputQChi innerPair55Input
    leaf2120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2120LowerChecked :
    lowerCheck 24 leaf2120Box leaf2120Inputs = true := by
  rfl'

private theorem leaf2120CoversExact : CoversExact 8
    leaf2120Box leaf2120Certificate leaf2120InnerLog leaf2120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi134RoundedFacts
    innerPair55RoundedFacts leaf2120RoundedFacts (by rfl)

private theorem leaf2120FlatSound : Sound leaf2120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2120CertificateValid
    leaf2120InnerLogValid leaf2120CoversExact leaf2120LowerChecked

private noncomputable def leaf2121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716950016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (850342931/536870912) }, upper := { exponent := 0, mantissa := (13127/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435443711/137433900032) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2121InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2121LocalValidity :
    LeafFacts leaf2121Box leaf2121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716950016) }) = true
      norm_num [leaf2121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2121CertificateValid :
    WideCertificateValid leaf2121Box leaf2121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi135ValidityFacts
    leaf2121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2121CoverageChecked :
    coverageCheck (innerAD leaf2121Box) leaf2121InnerLog = true := by
  rfl'

private theorem leaf2121InnerLogValid :
    leaf2121InnerLog.Valid 8 (innerAD leaf2121Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2121CoverageChecked

private noncomputable def leaf2121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2121InputLogOnePlusV_eq :
    leaf2121InputLogOnePlusV = outerEnclosure 24
      (leaf2121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2121RoundedFacts : LeafRoundedFacts 8
    leaf2121Certificate.logOnePlusV leaf2121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2121InputLogOnePlusV_eq }

private noncomputable def leaf2121Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi135InputQChi innerPair171Input
    leaf2121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2121LowerChecked :
    lowerCheck 24 leaf2121Box leaf2121Inputs = true := by
  rfl'

private theorem leaf2121CoversExact : CoversExact 8
    leaf2121Box leaf2121Certificate leaf2121InnerLog leaf2121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi135RoundedFacts
    innerPair171RoundedFacts leaf2121RoundedFacts (by rfl)

private theorem leaf2121FlatSound : Sound leaf2121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2121CertificateValid
    leaf2121InnerLogValid leaf2121CoversExact leaf2121LowerChecked

private noncomputable def leaf2122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871217/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042170368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (857158257/536870912) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084434703/8084340736) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf2122InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2122LocalValidity :
    LeafFacts leaf2122Box leaf2122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042170368) }) = true
      norm_num [leaf2122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2122CertificateValid :
    WideCertificateValid leaf2122Box leaf2122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi136ValidityFacts
    leaf2122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2122CoverageChecked :
    coverageCheck (innerAD leaf2122Box) leaf2122InnerLog = true := by
  rfl'

private theorem leaf2122InnerLogValid :
    leaf2122InnerLog.Valid 8 (innerAD leaf2122Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2122CoverageChecked

private noncomputable def leaf2122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2122InputLogOnePlusV_eq :
    leaf2122InputLogOnePlusV = outerEnclosure 24
      (leaf2122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2122RoundedFacts : LeafRoundedFacts 8
    leaf2122Certificate.logOnePlusV leaf2122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2122InputLogOnePlusV_eq }

private noncomputable def leaf2122Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi136InputQChi innerPair50Input
    leaf2122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2122LowerChecked :
    lowerCheck 24 leaf2122Box leaf2122Inputs = true := by
  rfl'

private theorem leaf2122CoversExact : CoversExact 8
    leaf2122Box leaf2122Certificate leaf2122InnerLog leaf2122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi136RoundedFacts
    innerPair50RoundedFacts leaf2122RoundedFacts (by rfl)

private theorem leaf2122FlatSound : Sound leaf2122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2122CertificateValid
    leaf2122InnerLogValid leaf2122CoversExact leaf2122LowerChecked

private noncomputable def leaf2123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871217/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905641984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (853357401/536870912) }, upper := { exponent := 0, mantissa := (6587/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811806549/45811283968) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2123InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2123LocalValidity :
    LeafFacts leaf2123Box leaf2123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905641984) }) = true
      norm_num [leaf2123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2123CertificateValid :
    WideCertificateValid leaf2123Box leaf2123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi135ValidityFacts
    leaf2123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2123CoverageChecked :
    coverageCheck (innerAD leaf2123Box) leaf2123InnerLog = true := by
  rfl'

private theorem leaf2123InnerLogValid :
    leaf2123InnerLog.Valid 8 (innerAD leaf2123Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2123CoverageChecked

private noncomputable def leaf2123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2123InputLogOnePlusV_eq :
    leaf2123InputLogOnePlusV = outerEnclosure 24
      (leaf2123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2123RoundedFacts : LeafRoundedFacts 8
    leaf2123Certificate.logOnePlusV leaf2123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2123InputLogOnePlusV_eq }

private noncomputable def leaf2123Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi135InputQChi innerPair171Input
    leaf2123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2123LowerChecked :
    lowerCheck 24 leaf2123Box leaf2123Inputs = true := by
  rfl'

private theorem leaf2123CoversExact : CoversExact 8
    leaf2123Box leaf2123Certificate leaf2123InnerLog leaf2123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi135RoundedFacts
    innerPair171RoundedFacts leaf2123RoundedFacts (by rfl)

private theorem leaf2123FlatSound : Sound leaf2123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2123CertificateValid
    leaf2123InnerLogValid leaf2123CoversExact leaf2123LowerChecked

private noncomputable def leaf2124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871219/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743374336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (860238259/536870912) }, upper := { exponent := 0, mantissa := (415/256) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487073075/27486748672) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf2124InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2124LocalValidity :
    LeafFacts leaf2124Box leaf2124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743374336) }) = true
      norm_num [leaf2124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2124CertificateValid :
    WideCertificateValid leaf2124Box leaf2124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi136ValidityFacts
    leaf2124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2124CoverageChecked :
    coverageCheck (innerAD leaf2124Box) leaf2124InnerLog = true := by
  rfl'

private theorem leaf2124InnerLogValid :
    leaf2124InnerLog.Valid 8 (innerAD leaf2124Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2124CoverageChecked

private noncomputable def leaf2124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2124InputLogOnePlusV_eq :
    leaf2124InputLogOnePlusV = outerEnclosure 24
      (leaf2124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2124RoundedFacts : LeafRoundedFacts 8
    leaf2124Certificate.logOnePlusV leaf2124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2124InputLogOnePlusV_eq }

private noncomputable def leaf2124Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi136InputQChi innerPair50Input
    leaf2124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2124LowerChecked :
    lowerCheck 24 leaf2124Box leaf2124Inputs = true := by
  rfl'

private theorem leaf2124CoversExact : CoversExact 8
    leaf2124Box leaf2124Certificate leaf2124InnerLog leaf2124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi136RoundedFacts
    innerPair50RoundedFacts leaf2124RoundedFacts (by rfl)

private theorem leaf2124FlatSound : Sound leaf2124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2124CertificateValid
    leaf2124InnerLogValid leaf2124CoversExact leaf2124LowerChecked

private noncomputable def leaf2125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871215/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717011456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (842479091/536870912) }, upper := { exponent := 0, mantissa := (13007/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435505151/137434022912) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2125InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2125LocalValidity :
    LeafFacts leaf2125Box leaf2125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717011456) }) = true
      norm_num [leaf2125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2125CertificateValid :
    WideCertificateValid leaf2125Box leaf2125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi133ValidityFacts
    leaf2125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2125CoverageChecked :
    coverageCheck (innerAD leaf2125Box) leaf2125InnerLog = true := by
  rfl'

private theorem leaf2125InnerLogValid :
    leaf2125InnerLog.Valid 8 (innerAD leaf2125Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2125CoverageChecked

private noncomputable def leaf2125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2125InputLogOnePlusV_eq :
    leaf2125InputLogOnePlusV = outerEnclosure 24
      (leaf2125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2125RoundedFacts : LeafRoundedFacts 8
    leaf2125Certificate.logOnePlusV leaf2125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2125InputLogOnePlusV_eq }

private noncomputable def leaf2125Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi133InputQChi innerPair54Input
    leaf2125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2125LowerChecked :
    lowerCheck 24 leaf2125Box leaf2125Inputs = true := by
  rfl'

private theorem leaf2125CoversExact : CoversExact 8
    leaf2125Box leaf2125Certificate leaf2125InnerLog leaf2125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi133RoundedFacts
    innerPair54RoundedFacts leaf2125RoundedFacts (by rfl)

private theorem leaf2125FlatSound : Sound leaf2125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2125CertificateValid
    leaf2125InnerLogValid leaf2125CoversExact leaf2125LowerChecked

private noncomputable def leaf2126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871217/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905652224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (849425481/536870912) }, upper := { exponent := 0, mantissa := (6557/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811816789/45811304448) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2126InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2126LocalValidity :
    LeafFacts leaf2126Box leaf2126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905652224) }) = true
      norm_num [leaf2126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2126CertificateValid :
    WideCertificateValid leaf2126Box leaf2126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi134ValidityFacts
    leaf2126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2126CoverageChecked :
    coverageCheck (innerAD leaf2126Box) leaf2126InnerLog = true := by
  rfl'

private theorem leaf2126InnerLogValid :
    leaf2126InnerLog.Valid 8 (innerAD leaf2126Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2126CoverageChecked

private noncomputable def leaf2126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2126InputLogOnePlusV_eq :
    leaf2126InputLogOnePlusV = outerEnclosure 24
      (leaf2126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2126RoundedFacts : LeafRoundedFacts 8
    leaf2126Certificate.logOnePlusV leaf2126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2126InputLogOnePlusV_eq }

private noncomputable def leaf2126Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi134InputQChi innerPair171Input
    leaf2126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2126LowerChecked :
    lowerCheck 24 leaf2126Box leaf2126Inputs = true := by
  rfl'

private theorem leaf2126CoversExact : CoversExact 8
    leaf2126Box leaf2126Certificate leaf2126InnerLog leaf2126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi134RoundedFacts
    innerPair171RoundedFacts leaf2126RoundedFacts (by rfl)

private theorem leaf2126FlatSound : Sound leaf2126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2126CertificateValid
    leaf2126InnerLogValid leaf2126CoversExact leaf2126LowerChecked

private noncomputable def leaf2127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf2127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871217/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716988416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (845362497/536870912) }, upper := { exponent := 0, mantissa := (3263/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435482111/137433976832) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2127InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2127LocalValidity :
    LeafFacts leaf2127Box leaf2127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716988416) }) = true
      norm_num [leaf2127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2127CertificateValid :
    WideCertificateValid leaf2127Box leaf2127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi133ValidityFacts
    leaf2127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2127CoverageChecked :
    coverageCheck (innerAD leaf2127Box) leaf2127InnerLog = true := by
  rfl'

private theorem leaf2127InnerLogValid :
    leaf2127InnerLog.Valid 8 (innerAD leaf2127Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2127CoverageChecked

private noncomputable def leaf2127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2127InputLogOnePlusV_eq :
    leaf2127InputLogOnePlusV = outerEnclosure 24
      (leaf2127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2127RoundedFacts : LeafRoundedFacts 8
    leaf2127Certificate.logOnePlusV leaf2127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2127InputLogOnePlusV_eq }

private noncomputable def leaf2127Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi133InputQChi innerPair54Input
    leaf2127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2127LowerChecked :
    lowerCheck 24 leaf2127Box leaf2127Inputs = true := by
  rfl'

private theorem leaf2127CoversExact : CoversExact 8
    leaf2127Box leaf2127Certificate leaf2127InnerLog leaf2127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi133RoundedFacts
    innerPair54RoundedFacts leaf2127RoundedFacts (by rfl)

private theorem leaf2127FlatSound : Sound leaf2127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2127CertificateValid
    leaf2127InnerLogValid leaf2127CoversExact leaf2127LowerChecked

private noncomputable def leaf2128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf2128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871219/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743386624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (852374419/536870912) }, upper := { exponent := 0, mantissa := (1645/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487085363/27486773248) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2128InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2128LocalValidity :
    LeafFacts leaf2128Box leaf2128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743386624) }) = true
      norm_num [leaf2128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2128CertificateValid :
    WideCertificateValid leaf2128Box leaf2128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi134ValidityFacts
    leaf2128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2128CoverageChecked :
    coverageCheck (innerAD leaf2128Box) leaf2128InnerLog = true := by
  rfl'

private theorem leaf2128InnerLogValid :
    leaf2128InnerLog.Valid 8 (innerAD leaf2128Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2128CoverageChecked

private noncomputable def leaf2128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2128InputLogOnePlusV_eq :
    leaf2128InputLogOnePlusV = outerEnclosure 24
      (leaf2128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2128RoundedFacts : LeafRoundedFacts 8
    leaf2128Certificate.logOnePlusV leaf2128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2128InputLogOnePlusV_eq }

private noncomputable def leaf2128Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi134InputQChi innerPair171Input
    leaf2128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2128LowerChecked :
    lowerCheck 24 leaf2128Box leaf2128Inputs = true := by
  rfl'

private theorem leaf2128CoversExact : CoversExact 8
    leaf2128Box leaf2128Certificate leaf2128InnerLog leaf2128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi134RoundedFacts
    innerPair171RoundedFacts leaf2128RoundedFacts (by rfl)

private theorem leaf2128FlatSound : Sound leaf2128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2128CertificateValid
    leaf2128InnerLogValid leaf2128CoversExact leaf2128LowerChecked

private noncomputable def leaf2129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871219/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716901888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (856371871/536870912) }, upper := { exponent := 0, mantissa := (13221/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435395583/137433803776) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2129InnerLog : WideLogData :=
  innerPair159Data

set_option maxRecDepth 1000000 in
private theorem leaf2129LocalValidity :
    LeafFacts leaf2129Box leaf2129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716901888) }) = true
      norm_num [leaf2129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2129CertificateValid :
    WideCertificateValid leaf2129Box leaf2129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi135ValidityFacts
    leaf2129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2129CoverageChecked :
    coverageCheck (innerAD leaf2129Box) leaf2129InnerLog = true := by
  rfl'

private theorem leaf2129InnerLogValid :
    leaf2129InnerLog.Valid 8 (innerAD leaf2129Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint166PositiveFacts.valid leaf2129CoverageChecked

private noncomputable def leaf2129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2129InputLogOnePlusV_eq :
    leaf2129InputLogOnePlusV = outerEnclosure 24
      (leaf2129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2129RoundedFacts : LeafRoundedFacts 8
    leaf2129Certificate.logOnePlusV leaf2129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2129InputLogOnePlusV_eq }

private noncomputable def leaf2129Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi135InputQChi innerPair159Input
    leaf2129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2129LowerChecked :
    lowerCheck 24 leaf2129Box leaf2129Inputs = true := by
  rfl'

private theorem leaf2129CoversExact : CoversExact 8
    leaf2129Box leaf2129Certificate leaf2129InnerLog leaf2129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi135RoundedFacts
    innerPair159RoundedFacts leaf2129RoundedFacts (by rfl)

private theorem leaf2129FlatSound : Sound leaf2129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2129CertificateValid
    leaf2129InnerLogValid leaf2129CoversExact leaf2129LowerChecked

private noncomputable def leaf2130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871221/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716847104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (863318261/536870912) }, upper := { exponent := 0, mantissa := (833/512) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435340799/137433694208) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf2130InnerLog : WideLogData :=
  innerPair194Data

set_option maxRecDepth 1000000 in
private theorem leaf2130LocalValidity :
    LeafFacts leaf2130Box leaf2130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716847104) }) = true
      norm_num [leaf2130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2130CertificateValid :
    WideCertificateValid leaf2130Box leaf2130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi136ValidityFacts
    leaf2130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2130CoverageChecked :
    coverageCheck (innerAD leaf2130Box) leaf2130InnerLog = true := by
  rfl'

private theorem leaf2130InnerLogValid :
    leaf2130InnerLog.Valid 8 (innerAD leaf2130Box) :=
  wideLogDataValid_of_cachedCheck endpoint57PositiveFacts
    endpoint126PositiveFacts.valid leaf2130CoverageChecked

private noncomputable def leaf2130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2130InputLogOnePlusV_eq :
    leaf2130InputLogOnePlusV = outerEnclosure 24
      (leaf2130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2130RoundedFacts : LeafRoundedFacts 8
    leaf2130Certificate.logOnePlusV leaf2130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2130InputLogOnePlusV_eq }

private noncomputable def leaf2130Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi136InputQChi innerPair194Input
    leaf2130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2130LowerChecked :
    lowerCheck 24 leaf2130Box leaf2130Inputs = true := by
  rfl'

private theorem leaf2130CoversExact : CoversExact 8
    leaf2130Box leaf2130Certificate leaf2130InnerLog leaf2130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi136RoundedFacts
    innerPair194RoundedFacts leaf2130RoundedFacts (by rfl)

private theorem leaf2130FlatSound : Sound leaf2130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2130CertificateValid
    leaf2130InnerLogValid leaf2130CoversExact leaf2130LowerChecked

private noncomputable def leaf2131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf2131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871221/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716877824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (859386341/536870912) }, upper := { exponent := 0, mantissa := (3317/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435371519/137433755648) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2131InnerLog : WideLogData :=
  innerPair185Data

set_option maxRecDepth 1000000 in
private theorem leaf2131LocalValidity :
    LeafFacts leaf2131Box leaf2131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716877824) }) = true
      norm_num [leaf2131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2131CertificateValid :
    WideCertificateValid leaf2131Box leaf2131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi135ValidityFacts
    leaf2131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2131CoverageChecked :
    coverageCheck (innerAD leaf2131Box) leaf2131InnerLog = true := by
  rfl'

private theorem leaf2131InnerLogValid :
    leaf2131InnerLog.Valid 8 (innerAD leaf2131Box) :=
  wideLogDataValid_of_cachedCheck endpoint54PositiveFacts
    endpoint55PositiveFacts.valid leaf2131CoverageChecked

private noncomputable def leaf2131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2131InputLogOnePlusV_eq :
    leaf2131InputLogOnePlusV = outerEnclosure 24
      (leaf2131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2131RoundedFacts : LeafRoundedFacts 8
    leaf2131Certificate.logOnePlusV leaf2131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2131InputLogOnePlusV_eq }

private noncomputable def leaf2131Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi135InputQChi innerPair185Input
    leaf2131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2131LowerChecked :
    lowerCheck 24 leaf2131Box leaf2131Inputs = true := by
  rfl'

private theorem leaf2131CoversExact : CoversExact 8
    leaf2131Box leaf2131Certificate leaf2131InnerLog leaf2131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi135RoundedFacts
    innerPair185RoundedFacts leaf2131RoundedFacts (by rfl)

private theorem leaf2131FlatSound : Sound leaf2131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2131CertificateValid
    leaf2131InnerLogValid leaf2131CoversExact leaf2131LowerChecked

private noncomputable def leaf2132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf2132Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871223/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68716822528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (866398263/536870912) }, upper := { exponent := 0, mantissa := (209/128) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435316223/137433645056) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf2132InnerLog : WideLogData :=
  innerPair419Data

set_option maxRecDepth 1000000 in
private theorem leaf2132LocalValidity :
    LeafFacts leaf2132Box leaf2132Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2132Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68716822528) }) = true
      norm_num [leaf2132Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2132CertificateValid :
    WideCertificateValid leaf2132Box leaf2132Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi136ValidityFacts
    leaf2132LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2132CoverageChecked :
    coverageCheck (innerAD leaf2132Box) leaf2132InnerLog = true := by
  rfl'

private theorem leaf2132InnerLogValid :
    leaf2132InnerLog.Valid 8 (innerAD leaf2132Box) :=
  wideLogDataValid_of_cachedCheck endpoint131PositiveFacts
    endpoint167PositiveFacts.valid leaf2132CoverageChecked

private noncomputable def leaf2132InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2132InputLogOnePlusV_eq :
    leaf2132InputLogOnePlusV = outerEnclosure 24
      (leaf2132Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2132RoundedFacts : LeafRoundedFacts 8
    leaf2132Certificate.logOnePlusV leaf2132InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2132InputLogOnePlusV_eq }

private noncomputable def leaf2132Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi136InputQChi innerPair419Input
    leaf2132InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2132LowerChecked :
    lowerCheck 24 leaf2132Box leaf2132Inputs = true := by
  rfl'

private theorem leaf2132CoversExact : CoversExact 8
    leaf2132Box leaf2132Certificate leaf2132InnerLog leaf2132Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi136RoundedFacts
    innerPair419RoundedFacts leaf2132RoundedFacts (by rfl)

private theorem leaf2132FlatSound : Sound leaf2132Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2132CertificateValid
    leaf2132InnerLogValid leaf2132CoversExact leaf2132LowerChecked

private noncomputable def component46Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node0_sound : Sound component46Node0Box :=
  sound_of_literal_split component46Node0Box leaf2101Box leaf2102Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2101FlatSound leaf2102FlatSound

private noncomputable def component46Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node1_sound : Sound component46Node1Box :=
  sound_of_literal_split component46Node1Box leaf2103Box leaf2104Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2103FlatSound leaf2104FlatSound

private noncomputable def component46Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node2_sound : Sound component46Node2Box :=
  sound_of_literal_split component46Node2Box component46Node0Box component46Node1Box
    .k (105/32) (by rfl) (by rfl)
    component46Node0_sound component46Node1_sound

private noncomputable def component46Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node3_sound : Sound component46Node3Box :=
  sound_of_literal_split component46Node3Box leaf2105Box leaf2106Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2105FlatSound leaf2106FlatSound

private noncomputable def component46Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node4_sound : Sound component46Node4Box :=
  sound_of_literal_split component46Node4Box leaf2107Box leaf2108Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2107FlatSound leaf2108FlatSound

private noncomputable def component46Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node5_sound : Sound component46Node5Box :=
  sound_of_literal_split component46Node5Box component46Node3Box component46Node4Box
    .k (105/32) (by rfl) (by rfl)
    component46Node3_sound component46Node4_sound

private noncomputable def component46Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node6_sound : Sound component46Node6Box :=
  sound_of_literal_split component46Node6Box component46Node2Box component46Node5Box
    .chi (21/128) (by rfl) (by rfl)
    component46Node2_sound component46Node5_sound

private noncomputable def component46Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node7_sound : Sound component46Node7Box :=
  sound_of_literal_split component46Node7Box leaf2109Box leaf2110Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2109FlatSound leaf2110FlatSound

private noncomputable def component46Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node8_sound : Sound component46Node8Box :=
  sound_of_literal_split component46Node8Box leaf2111Box leaf2112Box
    .chi (41/256) (by rfl) (by rfl)
    leaf2111FlatSound leaf2112FlatSound

private noncomputable def component46Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node9_sound : Sound component46Node9Box :=
  sound_of_literal_split component46Node9Box component46Node7Box component46Node8Box
    .k (107/32) (by rfl) (by rfl)
    component46Node7_sound component46Node8_sound

private noncomputable def component46Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node10_sound : Sound component46Node10Box :=
  sound_of_literal_split component46Node10Box leaf2113Box leaf2114Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2113FlatSound leaf2114FlatSound

private noncomputable def component46Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node11_sound : Sound component46Node11Box :=
  sound_of_literal_split component46Node11Box leaf2115Box leaf2116Box
    .chi (43/256) (by rfl) (by rfl)
    leaf2115FlatSound leaf2116FlatSound

private noncomputable def component46Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node12_sound : Sound component46Node12Box :=
  sound_of_literal_split component46Node12Box component46Node10Box component46Node11Box
    .k (107/32) (by rfl) (by rfl)
    component46Node10_sound component46Node11_sound

private noncomputable def component46Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node13_sound : Sound component46Node13Box :=
  sound_of_literal_split component46Node13Box component46Node9Box component46Node12Box
    .chi (21/128) (by rfl) (by rfl)
    component46Node9_sound component46Node12_sound

private noncomputable def component46Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component46Node14_sound : Sound component46Node14Box :=
  sound_of_literal_split component46Node14Box component46Node6Box component46Node13Box
    .k (53/16) (by rfl) (by rfl)
    component46Node6_sound component46Node13_sound

private noncomputable def component46Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node15_sound : Sound component46Node15Box :=
  sound_of_literal_split component46Node15Box leaf2117Box leaf2118Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2117FlatSound leaf2118FlatSound

private noncomputable def component46Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node16_sound : Sound component46Node16Box :=
  sound_of_literal_split component46Node16Box leaf2119Box leaf2120Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2119FlatSound leaf2120FlatSound

private noncomputable def component46Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node17_sound : Sound component46Node17Box :=
  sound_of_literal_split component46Node17Box component46Node15Box component46Node16Box
    .k (105/32) (by rfl) (by rfl)
    component46Node15_sound component46Node16_sound

private noncomputable def component46Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node18_sound : Sound component46Node18Box :=
  sound_of_literal_split component46Node18Box leaf2121Box leaf2122Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2121FlatSound leaf2122FlatSound

private noncomputable def component46Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node19_sound : Sound component46Node19Box :=
  sound_of_literal_split component46Node19Box leaf2123Box leaf2124Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2123FlatSound leaf2124FlatSound

private noncomputable def component46Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node20_sound : Sound component46Node20Box :=
  sound_of_literal_split component46Node20Box component46Node18Box component46Node19Box
    .k (105/32) (by rfl) (by rfl)
    component46Node18_sound component46Node19_sound

private noncomputable def component46Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node21_sound : Sound component46Node21Box :=
  sound_of_literal_split component46Node21Box component46Node17Box component46Node20Box
    .chi (23/128) (by rfl) (by rfl)
    component46Node17_sound component46Node20_sound

private noncomputable def component46Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node22_sound : Sound component46Node22Box :=
  sound_of_literal_split component46Node22Box leaf2125Box leaf2126Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2125FlatSound leaf2126FlatSound

private noncomputable def component46Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node23_sound : Sound component46Node23Box :=
  sound_of_literal_split component46Node23Box leaf2127Box leaf2128Box
    .chi (45/256) (by rfl) (by rfl)
    leaf2127FlatSound leaf2128FlatSound

private noncomputable def component46Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component46Node24_sound : Sound component46Node24Box :=
  sound_of_literal_split component46Node24Box component46Node22Box component46Node23Box
    .k (107/32) (by rfl) (by rfl)
    component46Node22_sound component46Node23_sound

private noncomputable def component46Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node25_sound : Sound component46Node25Box :=
  sound_of_literal_split component46Node25Box leaf2129Box leaf2130Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2129FlatSound leaf2130FlatSound

private noncomputable def component46Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node26_sound : Sound component46Node26Box :=
  sound_of_literal_split component46Node26Box leaf2131Box leaf2132Box
    .chi (47/256) (by rfl) (by rfl)
    leaf2131FlatSound leaf2132FlatSound

private noncomputable def component46Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node27_sound : Sound component46Node27Box :=
  sound_of_literal_split component46Node27Box component46Node25Box component46Node26Box
    .k (107/32) (by rfl) (by rfl)
    component46Node25_sound component46Node26_sound

private noncomputable def component46Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node28_sound : Sound component46Node28Box :=
  sound_of_literal_split component46Node28Box component46Node24Box component46Node27Box
    .chi (23/128) (by rfl) (by rfl)
    component46Node24_sound component46Node27_sound

private noncomputable def component46Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component46Node29_sound : Sound component46Node29Box :=
  sound_of_literal_split component46Node29Box component46Node21Box component46Node28Box
    .k (53/16) (by rfl) (by rfl)
    component46Node21_sound component46Node28_sound

noncomputable def component46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component46_sound : Sound component46Box :=
  sound_of_literal_split component46Box component46Node14Box component46Node29Box
    .chi (11/64) (by rfl) (by rfl)
    component46Node14_sound component46Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
