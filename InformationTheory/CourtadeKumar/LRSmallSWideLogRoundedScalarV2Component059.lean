import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch3

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

private noncomputable def leaf2815Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2815Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742203/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1347421445/1347399936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1593770631/1073741824) }, upper := { exponent := 0, mantissa := (24509/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2694821381/2694799872) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf2815InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2815LocalValidity :
    LeafFacts leaf2815Box leaf2815Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2815Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1347421445/1347399936) }) = true
      norm_num [leaf2815Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2815CertificateValid :
    WideCertificateValid leaf2815Box leaf2815Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi205ValidityFacts
    leaf2815LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2815CoverageChecked :
    coverageCheck (innerAD leaf2815Box) leaf2815InnerLog = true := by
  rfl'

private theorem leaf2815InnerLogValid :
    leaf2815InnerLog.Valid 8 (innerAD leaf2815Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2815CoverageChecked

private noncomputable def leaf2815InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629215/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2815InputLogOnePlusV_eq :
    leaf2815InputLogOnePlusV = outerEnclosure 24
      (leaf2815Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2815RoundedFacts : LeafRoundedFacts 8
    leaf2815Certificate.logOnePlusV leaf2815InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2815InputLogOnePlusV_eq }

private noncomputable def leaf2815Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2815InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2815LowerChecked :
    lowerCheck 24 leaf2815Box leaf2815Inputs = true := by
  rfl'

private theorem leaf2815CoversExact : CoversExact 8
    leaf2815Box leaf2815Certificate leaf2815InnerLog leaf2815Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2815RoundedFacts (by rfl)

private theorem leaf2815FlatSound : Sound leaf2815Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2815CertificateValid
    leaf2815InnerLogValid leaf2815CoversExact leaf2815LowerChecked

private noncomputable def leaf2816Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2816Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742205/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717364736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1601896597/1073741824) }, upper := { exponent := 0, mantissa := (12317/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435858431/137434729472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf2816InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2816LocalValidity :
    LeafFacts leaf2816Box leaf2816Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2816Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717364736) }) = true
      norm_num [leaf2816Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2816CertificateValid :
    WideCertificateValid leaf2816Box leaf2816Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi206ValidityFacts
    leaf2816LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2816CoverageChecked :
    coverageCheck (innerAD leaf2816Box) leaf2816InnerLog = true := by
  rfl'

private theorem leaf2816InnerLogValid :
    leaf2816InnerLog.Valid 8 (innerAD leaf2816Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2816CoverageChecked

private noncomputable def leaf2816InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2816InputLogOnePlusV_eq :
    leaf2816InputLogOnePlusV = outerEnclosure 24
      (leaf2816Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2816RoundedFacts : LeafRoundedFacts 8
    leaf2816Certificate.logOnePlusV leaf2816InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2816InputLogOnePlusV_eq }

private noncomputable def leaf2816Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi206InputQChi innerPair409Input
    leaf2816InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2816LowerChecked :
    lowerCheck 24 leaf2816Box leaf2816Inputs = true := by
  rfl'

private theorem leaf2816CoversExact : CoversExact 8
    leaf2816Box leaf2816Certificate leaf2816InnerLog leaf2816Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi206RoundedFacts
    innerPair409RoundedFacts leaf2816RoundedFacts (by rfl)

private theorem leaf2816FlatSound : Sound leaf2816Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2816CertificateValid
    leaf2816InnerLogValid leaf2816CoversExact leaf2816LowerChecked

private noncomputable def leaf2817Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2817Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (1073742205/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717380096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1597964677/1073741824) }, upper := { exponent := 0, mantissa := (12287/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435873791/137434760192) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf2817InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf2817LocalValidity :
    LeafFacts leaf2817Box leaf2817Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2817Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717380096) }) = true
      norm_num [leaf2817Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2817CertificateValid :
    WideCertificateValid leaf2817Box leaf2817Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi205ValidityFacts
    leaf2817LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2817CoverageChecked :
    coverageCheck (innerAD leaf2817Box) leaf2817InnerLog = true := by
  rfl'

private theorem leaf2817InnerLogValid :
    leaf2817InnerLog.Valid 8 (innerAD leaf2817Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf2817CoverageChecked

private noncomputable def leaf2817InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2817InputLogOnePlusV_eq :
    leaf2817InputLogOnePlusV = outerEnclosure 24
      (leaf2817Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2817RoundedFacts : LeafRoundedFacts 8
    leaf2817Certificate.logOnePlusV leaf2817InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2817InputLogOnePlusV_eq }

private noncomputable def leaf2817Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi205InputQChi innerPair34Input
    leaf2817InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2817LowerChecked :
    lowerCheck 24 leaf2817Box leaf2817Inputs = true := by
  rfl'

private theorem leaf2817CoversExact : CoversExact 8
    leaf2817Box leaf2817Certificate leaf2817InnerLog leaf2817Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi205RoundedFacts
    innerPair34RoundedFacts leaf2817RoundedFacts (by rfl)

private theorem leaf2817FlatSound : Sound leaf2817Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2817CertificateValid
    leaf2817InnerLogValid leaf2817CoversExact leaf2817LowerChecked

private noncomputable def leaf2818Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2818Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742207/1073741824) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743469568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1606156175/1073741824) }, upper := { exponent := 0, mantissa := (6175/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487168307/27486939136) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf2818InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2818LocalValidity :
    LeafFacts leaf2818Box leaf2818Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2818Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743469568) }) = true
      norm_num [leaf2818Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2818CertificateValid :
    WideCertificateValid leaf2818Box leaf2818Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi206ValidityFacts
    leaf2818LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2818CoverageChecked :
    coverageCheck (innerAD leaf2818Box) leaf2818InnerLog = true := by
  rfl'

private theorem leaf2818InnerLogValid :
    leaf2818InnerLog.Valid 8 (innerAD leaf2818Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2818CoverageChecked

private noncomputable def leaf2818InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2818InputLogOnePlusV_eq :
    leaf2818InputLogOnePlusV = outerEnclosure 24
      (leaf2818Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2818RoundedFacts : LeafRoundedFacts 8
    leaf2818Certificate.logOnePlusV leaf2818InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2818InputLogOnePlusV_eq }

private noncomputable def leaf2818Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi206InputQChi innerPair409Input
    leaf2818InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2818LowerChecked :
    lowerCheck 24 leaf2818Box leaf2818Inputs = true := by
  rfl'

private theorem leaf2818CoversExact : CoversExact 8
    leaf2818Box leaf2818Certificate leaf2818InnerLog leaf2818Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi206RoundedFacts
    innerPair409RoundedFacts leaf2818RoundedFacts (by rfl)

private theorem leaf2818FlatSound : Sound leaf2818Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2818CertificateValid
    leaf2818InnerLogValid leaf2818CoversExact leaf2818LowerChecked

private noncomputable def leaf2819Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2819Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742207/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717332736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1610022563/1073741824) }, upper := { exponent := 0, mantissa := (24759/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435826431/137434665472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf2819InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2819LocalValidity :
    LeafFacts leaf2819Box leaf2819Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2819Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717332736) }) = true
      norm_num [leaf2819Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2819CertificateValid :
    WideCertificateValid leaf2819Box leaf2819Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi203ValidityFacts
    leaf2819LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2819CoverageChecked :
    coverageCheck (innerAD leaf2819Box) leaf2819InnerLog = true := by
  rfl'

private theorem leaf2819InnerLogValid :
    leaf2819InnerLog.Valid 8 (innerAD leaf2819Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2819CoverageChecked

private noncomputable def leaf2819InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2819InputLogOnePlusV_eq :
    leaf2819InputLogOnePlusV = outerEnclosure 24
      (leaf2819Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2819RoundedFacts : LeafRoundedFacts 8
    leaf2819Certificate.logOnePlusV leaf2819InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2819InputLogOnePlusV_eq }

private noncomputable def leaf2819Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi203InputQChi innerPair409Input
    leaf2819InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2819LowerChecked :
    lowerCheck 24 leaf2819Box leaf2819Inputs = true := by
  rfl'

private theorem leaf2819CoversExact : CoversExact 8
    leaf2819Box leaf2819Certificate leaf2819InnerLog leaf2819Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi203RoundedFacts
    innerPair409RoundedFacts leaf2819RoundedFacts (by rfl)

private theorem leaf2819FlatSound : Sound leaf2819Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2819CertificateValid
    leaf2819InnerLogValid leaf2819CoversExact leaf2819LowerChecked

private noncomputable def leaf2820Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2820Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742209/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905766912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1618148529/1073741824) }, upper := { exponent := 0, mantissa := (6221/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811931477/45811533824) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf2820InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2820LocalValidity :
    LeafFacts leaf2820Box leaf2820Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2820Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905766912) }) = true
      norm_num [leaf2820Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2820CertificateValid :
    WideCertificateValid leaf2820Box leaf2820Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi204ValidityFacts
    leaf2820LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2820CoverageChecked :
    coverageCheck (innerAD leaf2820Box) leaf2820InnerLog = true := by
  rfl'

private theorem leaf2820InnerLogValid :
    leaf2820InnerLog.Valid 8 (innerAD leaf2820Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2820CoverageChecked

private noncomputable def leaf2820InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2820InputLogOnePlusV_eq :
    leaf2820InputLogOnePlusV = outerEnclosure 24
      (leaf2820Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2820RoundedFacts : LeafRoundedFacts 8
    leaf2820Certificate.logOnePlusV leaf2820InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2820InputLogOnePlusV_eq }

private noncomputable def leaf2820Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi204InputQChi innerPair44Input
    leaf2820InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2820LowerChecked :
    lowerCheck 24 leaf2820Box leaf2820Inputs = true := by
  rfl'

private theorem leaf2820CoversExact : CoversExact 8
    leaf2820Box leaf2820Certificate leaf2820InnerLog leaf2820Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi204RoundedFacts
    innerPair44RoundedFacts leaf2820RoundedFacts (by rfl)

private theorem leaf2820FlatSound : Sound leaf2820Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2820CertificateValid
    leaf2820InnerLogValid leaf2820CoversExact leaf2820LowerChecked

private noncomputable def leaf2821Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2821Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742209/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717315584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1614347673/1073741824) }, upper := { exponent := 0, mantissa := (12413/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435809279/137434631168) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf2821InnerLog : WideLogData :=
  innerPair47Data

set_option maxRecDepth 1000000 in
private theorem leaf2821LocalValidity :
    LeafFacts leaf2821Box leaf2821Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2821Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717315584) }) = true
      norm_num [leaf2821Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2821CertificateValid :
    WideCertificateValid leaf2821Box leaf2821Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi203ValidityFacts
    leaf2821LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2821CoverageChecked :
    coverageCheck (innerAD leaf2821Box) leaf2821InnerLog = true := by
  rfl'

private theorem leaf2821InnerLogValid :
    leaf2821InnerLog.Valid 8 (innerAD leaf2821Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint49PositiveFacts.valid leaf2821CoverageChecked

private noncomputable def leaf2821InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2821InputLogOnePlusV_eq :
    leaf2821InputLogOnePlusV = outerEnclosure 24
      (leaf2821Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2821RoundedFacts : LeafRoundedFacts 8
    leaf2821Certificate.logOnePlusV leaf2821InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2821InputLogOnePlusV_eq }

private noncomputable def leaf2821Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi203InputQChi innerPair47Input
    leaf2821InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2821LowerChecked :
    lowerCheck 24 leaf2821Box leaf2821Inputs = true := by
  rfl'

private theorem leaf2821CoversExact : CoversExact 8
    leaf2821Box leaf2821Certificate leaf2821InnerLog leaf2821Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi203RoundedFacts
    innerPair47RoundedFacts leaf2821RoundedFacts (by rfl)

private theorem leaf2821FlatSound : Sound leaf2821Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2821CertificateValid
    leaf2821InnerLogValid leaf2821CoversExact leaf2821LowerChecked

private noncomputable def leaf2822Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2822Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742211/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717283328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1622539171/1073741824) }, upper := { exponent := 0, mantissa := (3119/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435777023/137434566656) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf2822InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2822LocalValidity :
    LeafFacts leaf2822Box leaf2822Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2822Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717283328) }) = true
      norm_num [leaf2822Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2822CertificateValid :
    WideCertificateValid leaf2822Box leaf2822Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi204ValidityFacts
    leaf2822LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2822CoverageChecked :
    coverageCheck (innerAD leaf2822Box) leaf2822InnerLog = true := by
  rfl'

private theorem leaf2822InnerLogValid :
    leaf2822InnerLog.Valid 8 (innerAD leaf2822Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2822CoverageChecked

private noncomputable def leaf2822InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2822InputLogOnePlusV_eq :
    leaf2822InputLogOnePlusV = outerEnclosure 24
      (leaf2822Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2822RoundedFacts : LeafRoundedFacts 8
    leaf2822Certificate.logOnePlusV leaf2822InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2822InputLogOnePlusV_eq }

private noncomputable def leaf2822Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi204InputQChi innerPair44Input
    leaf2822InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2822LowerChecked :
    lowerCheck 24 leaf2822Box leaf2822Inputs = true := by
  rfl'

private theorem leaf2822CoversExact : CoversExact 8
    leaf2822Box leaf2822Certificate leaf2822InnerLog leaf2822Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi204RoundedFacts
    innerPair44RoundedFacts leaf2822RoundedFacts (by rfl)

private theorem leaf2822FlatSound : Sound leaf2822Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2822CertificateValid
    leaf2822InnerLogValid leaf2822CoversExact leaf2822LowerChecked

private noncomputable def leaf2823Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (17/128), chiHi := (69/512) }

private noncomputable def leaf2823Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742211/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717268736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1626274495/1073741824) }, upper := { exponent := 0, mantissa := (25009/16384) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi207LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435762431/137434537472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf2823InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2823LocalValidity :
    LeafFacts leaf2823Box leaf2823Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2823Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717268736) }) = true
      norm_num [leaf2823Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2823CertificateValid :
    WideCertificateValid leaf2823Box leaf2823Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi207ValidityFacts
    leaf2823LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2823CoverageChecked :
    coverageCheck (innerAD leaf2823Box) leaf2823InnerLog = true := by
  rfl'

private theorem leaf2823InnerLogValid :
    leaf2823InnerLog.Valid 8 (innerAD leaf2823Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2823CoverageChecked

private noncomputable def leaf2823InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2823InputLogOnePlusV_eq :
    leaf2823InputLogOnePlusV = outerEnclosure 24
      (leaf2823Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2823RoundedFacts : LeafRoundedFacts 8
    leaf2823Certificate.logOnePlusV leaf2823InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2823InputLogOnePlusV_eq }

private noncomputable def leaf2823Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi207InputQChi innerPair44Input
    leaf2823InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2823LowerChecked :
    lowerCheck 24 leaf2823Box leaf2823Inputs = true := by
  rfl'

private theorem leaf2823CoversExact : CoversExact 8
    leaf2823Box leaf2823Certificate leaf2823InnerLog leaf2823Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi207RoundedFacts
    innerPair44RoundedFacts leaf2823RoundedFacts (by rfl)

private theorem leaf2823FlatSound : Sound leaf2823Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2823CertificateValid
    leaf2823InnerLogValid leaf2823CoversExact leaf2823LowerChecked

private noncomputable def leaf2824Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (69/512), chiHi := (35/256) }

private noncomputable def leaf2824Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742213/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717236736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1634400461/1073741824) }, upper := { exponent := 0, mantissa := (12567/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi208LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435730431/137434473472) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf2824InnerLog : WideLogData :=
  innerPair411Data

set_option maxRecDepth 1000000 in
private theorem leaf2824LocalValidity :
    LeafFacts leaf2824Box leaf2824Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2824Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717236736) }) = true
      norm_num [leaf2824Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2824CertificateValid :
    WideCertificateValid leaf2824Box leaf2824Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi208ValidityFacts
    leaf2824LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2824CoverageChecked :
    coverageCheck (innerAD leaf2824Box) leaf2824InnerLog = true := by
  rfl'

private theorem leaf2824InnerLogValid :
    leaf2824InnerLog.Valid 8 (innerAD leaf2824Box) :=
  wideLogDataValid_of_cachedCheck endpoint121PositiveFacts
    endpoint124PositiveFacts.valid leaf2824CoverageChecked

private noncomputable def leaf2824InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2824InputLogOnePlusV_eq :
    leaf2824InputLogOnePlusV = outerEnclosure 24
      (leaf2824Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2824RoundedFacts : LeafRoundedFacts 8
    leaf2824Certificate.logOnePlusV leaf2824InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2824InputLogOnePlusV_eq }

private noncomputable def leaf2824Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi208InputQChi innerPair411Input
    leaf2824InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2824LowerChecked :
    lowerCheck 24 leaf2824Box leaf2824Inputs = true := by
  rfl'

private theorem leaf2824CoversExact : CoversExact 8
    leaf2824Box leaf2824Certificate leaf2824InnerLog leaf2824Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi208RoundedFacts
    innerPair411RoundedFacts leaf2824RoundedFacts (by rfl)

private theorem leaf2824FlatSound : Sound leaf2824Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2824CertificateValid
    leaf2824InnerLogValid leaf2824CoversExact leaf2824LowerChecked

private noncomputable def leaf2825Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2825Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434363904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1642526249/1073741824) }, upper := { exponent := 0, mantissa := (6337/4096) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871285759/274868727808) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2825InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2825LocalValidity :
    LeafFacts leaf2825Box leaf2825Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2825Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434363904) }) = true
      norm_num [leaf2825Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2825CertificateValid :
    WideCertificateValid leaf2825Box leaf2825Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi180ValidityFacts
    leaf2825LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2825CoverageChecked :
    coverageCheck (innerAD leaf2825Box) leaf2825InnerLog = true := by
  rfl'

private theorem leaf2825InnerLogValid :
    leaf2825InnerLog.Valid 8 (innerAD leaf2825Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2825CoverageChecked

private noncomputable def leaf2825InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2825InputLogOnePlusV_eq :
    leaf2825InputLogOnePlusV = outerEnclosure 24
      (leaf2825Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2825RoundedFacts : LeafRoundedFacts 8
    leaf2825Certificate.logOnePlusV leaf2825InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2825InputLogOnePlusV_eq }

private noncomputable def leaf2825Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2825InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2825LowerChecked :
    lowerCheck 24 leaf2825Box leaf2825Inputs = true := by
  rfl'

private theorem leaf2825CoversExact : CoversExact 8
    leaf2825Box leaf2825Certificate leaf2825InnerLog leaf2825Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2825RoundedFacts (by rfl)

private theorem leaf2825FlatSound : Sound leaf2825Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2825CertificateValid
    leaf2825InnerLogValid leaf2825CoversExact leaf2825LowerChecked

private noncomputable def leaf2826Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2826Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434345472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1644819867/1073741824) }, upper := { exponent := 0, mantissa := (3173/2048) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871267327/274868690944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2826InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2826LocalValidity :
    LeafFacts leaf2826Box leaf2826Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2826Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434345472) }) = true
      norm_num [leaf2826Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2826CertificateValid :
    WideCertificateValid leaf2826Box leaf2826Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi180ValidityFacts
    leaf2826LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2826CoverageChecked :
    coverageCheck (innerAD leaf2826Box) leaf2826InnerLog = true := by
  rfl'

private theorem leaf2826InnerLogValid :
    leaf2826InnerLog.Valid 8 (innerAD leaf2826Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2826CoverageChecked

private noncomputable def leaf2826InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2826InputLogOnePlusV_eq :
    leaf2826InputLogOnePlusV = outerEnclosure 24
      (leaf2826Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2826RoundedFacts : LeafRoundedFacts 8
    leaf2826Certificate.logOnePlusV leaf2826InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2826InputLogOnePlusV_eq }

private noncomputable def leaf2826Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2826InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2826LowerChecked :
    lowerCheck 24 leaf2826Box leaf2826Inputs = true := by
  rfl'

private theorem leaf2826CoversExact : CoversExact 8
    leaf2826Box leaf2826Certificate leaf2826InnerLog leaf2826Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2826RoundedFacts (by rfl)

private theorem leaf2826FlatSound : Sound leaf2826Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2826CertificateValid
    leaf2826InnerLogValid leaf2826CoversExact leaf2826LowerChecked

private noncomputable def leaf2827Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (17/128), chiHi := (69/512) }

private noncomputable def leaf2827Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742213/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717251072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1630730669/1073741824) }, upper := { exponent := 0, mantissa := (12539/8192) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi207LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435744767/137434502144) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf2827InnerLog : WideLogData :=
  innerPair176Data

set_option maxRecDepth 1000000 in
private theorem leaf2827LocalValidity :
    LeafFacts leaf2827Box leaf2827Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2827Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717251072) }) = true
      norm_num [leaf2827Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2827CertificateValid :
    WideCertificateValid leaf2827Box leaf2827Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi207ValidityFacts
    leaf2827LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2827CoverageChecked :
    coverageCheck (innerAD leaf2827Box) leaf2827InnerLog = true := by
  rfl'

private theorem leaf2827InnerLogValid :
    leaf2827InnerLog.Valid 8 (innerAD leaf2827Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint19PositiveFacts.valid leaf2827CoverageChecked

private noncomputable def leaf2827InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2827InputLogOnePlusV_eq :
    leaf2827InputLogOnePlusV = outerEnclosure 24
      (leaf2827Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2827RoundedFacts : LeafRoundedFacts 8
    leaf2827Certificate.logOnePlusV leaf2827InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2827InputLogOnePlusV_eq }

private noncomputable def leaf2827Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi207InputQChi innerPair176Input
    leaf2827InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2827LowerChecked :
    lowerCheck 24 leaf2827Box leaf2827Inputs = true := by
  rfl'

private theorem leaf2827CoversExact : CoversExact 8
    leaf2827Box leaf2827Certificate leaf2827InnerLog leaf2827Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi207RoundedFacts
    innerPair176RoundedFacts leaf2827RoundedFacts (by rfl)

private theorem leaf2827FlatSound : Sound leaf2827Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2827CertificateValid
    leaf2827InnerLogValid leaf2827CoversExact leaf2827LowerChecked

private noncomputable def leaf2828Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (69/512), chiHi := (35/256) }

private noncomputable def leaf2828Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742215/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717218816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1638922167/1073741824) }, upper := { exponent := 0, mantissa := (6301/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi208LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435712511/137434437632) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf2828InnerLog : WideLogData :=
  innerPair475Data

set_option maxRecDepth 1000000 in
private theorem leaf2828LocalValidity :
    LeafFacts leaf2828Box leaf2828Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2828Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717218816) }) = true
      norm_num [leaf2828Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2828CertificateValid :
    WideCertificateValid leaf2828Box leaf2828Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi208ValidityFacts
    leaf2828LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2828CoverageChecked :
    coverageCheck (innerAD leaf2828Box) leaf2828InnerLog = true := by
  rfl'

private theorem leaf2828InnerLogValid :
    leaf2828InnerLog.Valid 8 (innerAD leaf2828Box) :=
  wideLogDataValid_of_cachedCheck endpoint197PositiveFacts
    endpoint198PositiveFacts.valid leaf2828CoverageChecked

private noncomputable def leaf2828InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2828InputLogOnePlusV_eq :
    leaf2828InputLogOnePlusV = outerEnclosure 24
      (leaf2828Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2828RoundedFacts : LeafRoundedFacts 8
    leaf2828Certificate.logOnePlusV leaf2828InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2828InputLogOnePlusV_eq }

private noncomputable def leaf2828Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi208InputQChi innerPair475Input
    leaf2828InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2828LowerChecked :
    lowerCheck 24 leaf2828Box leaf2828Inputs = true := by
  rfl'

private theorem leaf2828CoversExact : CoversExact 8
    leaf2828Box leaf2828Certificate leaf2828InnerLog leaf2828Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi208RoundedFacts
    innerPair475RoundedFacts leaf2828RoundedFacts (by rfl)

private theorem leaf2828FlatSound : Sound leaf2828Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2828CertificateValid
    leaf2828InnerLogValid leaf2828CoversExact leaf2828LowerChecked

private noncomputable def leaf2829Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2829Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486865408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1647113485/1073741824) }, upper := { exponent := 0, mantissa := (6355/4096) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974249779/54973730816) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2829InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2829LocalValidity :
    LeafFacts leaf2829Box leaf2829Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2829Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486865408) }) = true
      norm_num [leaf2829Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2829CertificateValid :
    WideCertificateValid leaf2829Box leaf2829Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi180ValidityFacts
    leaf2829LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2829CoverageChecked :
    coverageCheck (innerAD leaf2829Box) leaf2829InnerLog = true := by
  rfl'

private theorem leaf2829InnerLogValid :
    leaf2829InnerLog.Valid 8 (innerAD leaf2829Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2829CoverageChecked

private noncomputable def leaf2829InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2829InputLogOnePlusV_eq :
    leaf2829InputLogOnePlusV = outerEnclosure 24
      (leaf2829Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2829RoundedFacts : LeafRoundedFacts 8
    leaf2829Certificate.logOnePlusV leaf2829InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2829InputLogOnePlusV_eq }

private noncomputable def leaf2829Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2829InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2829LowerChecked :
    lowerCheck 24 leaf2829Box leaf2829Inputs = true := by
  rfl'

private theorem leaf2829CoversExact : CoversExact 8
    leaf2829Box leaf2829Certificate leaf2829InnerLog leaf2829Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2829RoundedFacts (by rfl)

private theorem leaf2829FlatSound : Sound leaf2829Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2829CertificateValid
    leaf2829InnerLogValid leaf2829CoversExact leaf2829LowerChecked

private noncomputable def leaf2830Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2830Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434308608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1649407103/1073741824) }, upper := { exponent := 0, mantissa := (1591/1024) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871230463/274868617216) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2830InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2830LocalValidity :
    LeafFacts leaf2830Box leaf2830Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2830Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434308608) }) = true
      norm_num [leaf2830Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2830CertificateValid :
    WideCertificateValid leaf2830Box leaf2830Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi180ValidityFacts
    leaf2830LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2830CoverageChecked :
    coverageCheck (innerAD leaf2830Box) leaf2830InnerLog = true := by
  rfl'

private theorem leaf2830InnerLogValid :
    leaf2830InnerLog.Valid 8 (innerAD leaf2830Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2830CoverageChecked

private noncomputable def leaf2830InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2830InputLogOnePlusV_eq :
    leaf2830InputLogOnePlusV = outerEnclosure 24
      (leaf2830Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2830RoundedFacts : LeafRoundedFacts 8
    leaf2830Certificate.logOnePlusV leaf2830InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2830InputLogOnePlusV_eq }

private noncomputable def leaf2830Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2830InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2830LowerChecked :
    lowerCheck 24 leaf2830Box leaf2830Inputs = true := by
  rfl'

private theorem leaf2830CoversExact : CoversExact 8
    leaf2830Box leaf2830Certificate leaf2830InnerLog leaf2830Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2830RoundedFacts (by rfl)

private theorem leaf2830FlatSound : Sound leaf2830Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2830CertificateValid
    leaf2830InnerLogValid leaf2830CoversExact leaf2830LowerChecked

private noncomputable def leaf2831Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2831Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742207/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717363456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1602158723/1073741824) }, upper := { exponent := 0, mantissa := (24639/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435857151/137434726912) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf2831InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2831LocalValidity :
    LeafFacts leaf2831Box leaf2831Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2831Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717363456) }) = true
      norm_num [leaf2831Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2831CertificateValid :
    WideCertificateValid leaf2831Box leaf2831Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi205ValidityFacts
    leaf2831LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2831CoverageChecked :
    coverageCheck (innerAD leaf2831Box) leaf2831InnerLog = true := by
  rfl'

private theorem leaf2831InnerLogValid :
    leaf2831InnerLog.Valid 8 (innerAD leaf2831Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2831CoverageChecked

private noncomputable def leaf2831InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2831InputLogOnePlusV_eq :
    leaf2831InputLogOnePlusV = outerEnclosure 24
      (leaf2831Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2831RoundedFacts : LeafRoundedFacts 8
    leaf2831Certificate.logOnePlusV leaf2831InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2831InputLogOnePlusV_eq }

private noncomputable def leaf2831Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi205InputQChi innerPair409Input
    leaf2831InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2831LowerChecked :
    lowerCheck 24 leaf2831Box leaf2831Inputs = true := by
  rfl'

private theorem leaf2831CoversExact : CoversExact 8
    leaf2831Box leaf2831Certificate leaf2831InnerLog leaf2831Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi205RoundedFacts
    innerPair409RoundedFacts leaf2831RoundedFacts (by rfl)

private theorem leaf2831FlatSound : Sound leaf2831Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2831CertificateValid
    leaf2831InnerLogValid leaf2831CoversExact leaf2831LowerChecked

private noncomputable def leaf2832Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2832Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742209/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717330944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1610415753/1073741824) }, upper := { exponent := 0, mantissa := (12383/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435824639/137434661888) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf2832InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2832LocalValidity :
    LeafFacts leaf2832Box leaf2832Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2832Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717330944) }) = true
      norm_num [leaf2832Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2832CertificateValid :
    WideCertificateValid leaf2832Box leaf2832Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi206ValidityFacts
    leaf2832LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2832CoverageChecked :
    coverageCheck (innerAD leaf2832Box) leaf2832InnerLog = true := by
  rfl'

private theorem leaf2832InnerLogValid :
    leaf2832InnerLog.Valid 8 (innerAD leaf2832Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2832CoverageChecked

private noncomputable def leaf2832InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2832InputLogOnePlusV_eq :
    leaf2832InputLogOnePlusV = outerEnclosure 24
      (leaf2832Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2832RoundedFacts : LeafRoundedFacts 8
    leaf2832Certificate.logOnePlusV leaf2832InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2832InputLogOnePlusV_eq }

private noncomputable def leaf2832Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi206InputQChi innerPair409Input
    leaf2832InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2832LowerChecked :
    lowerCheck 24 leaf2832Box leaf2832Inputs = true := by
  rfl'

private theorem leaf2832CoversExact : CoversExact 8
    leaf2832Box leaf2832Certificate leaf2832InnerLog leaf2832Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi206RoundedFacts
    innerPair409RoundedFacts leaf2832RoundedFacts (by rfl)

private theorem leaf2832FlatSound : Sound leaf2832Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2832CertificateValid
    leaf2832InnerLogValid leaf2832CoversExact leaf2832LowerChecked

private noncomputable def leaf2833Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (1/8), chiHi := (65/512) }

private noncomputable def leaf2833Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742209/1073741824) }, vSqrt := { lower := (65527/65536), upper := (22906164565/22905782272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1606352769/1073741824) }, upper := { exponent := 0, mantissa := (193/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi205LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (45811946837/45811564544) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf2833InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf2833LocalValidity :
    LeafFacts leaf2833Box leaf2833Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2833Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (22906164565/22905782272) }) = true
      norm_num [leaf2833Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2833CertificateValid :
    WideCertificateValid leaf2833Box leaf2833Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi205ValidityFacts
    leaf2833LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2833CoverageChecked :
    coverageCheck (innerAD leaf2833Box) leaf2833InnerLog = true := by
  rfl'

private theorem leaf2833InnerLogValid :
    leaf2833InnerLog.Valid 8 (innerAD leaf2833Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf2833CoverageChecked

private noncomputable def leaf2833InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2833InputLogOnePlusV_eq :
    leaf2833InputLogOnePlusV = outerEnclosure 24
      (leaf2833Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2833RoundedFacts : LeafRoundedFacts 8
    leaf2833Certificate.logOnePlusV leaf2833InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2833InputLogOnePlusV_eq }

private noncomputable def leaf2833Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi205InputQChi innerPair409Input
    leaf2833InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2833LowerChecked :
    lowerCheck 24 leaf2833Box leaf2833Inputs = true := by
  rfl'

private theorem leaf2833CoversExact : CoversExact 8
    leaf2833Box leaf2833Certificate leaf2833InnerLog leaf2833Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi205RoundedFacts
    innerPair409RoundedFacts leaf2833RoundedFacts (by rfl)

private theorem leaf2833FlatSound : Sound leaf2833Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2833CertificateValid
    leaf2833InnerLogValid leaf2833CoversExact leaf2833LowerChecked

private noncomputable def leaf2834Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (65/512), chiHi := (33/256) }

private noncomputable def leaf2834Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742211/1073741824) }, vSqrt := { lower := (65527/65536), upper := (4042264335/4042194944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1614675331/1073741824) }, upper := { exponent := 0, mantissa := (97/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi206LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (8084459279/8084389888) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf2834InnerLog : WideLogData :=
  innerPair47Data

set_option maxRecDepth 1000000 in
private theorem leaf2834LocalValidity :
    LeafFacts leaf2834Box leaf2834Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2834Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (4042264335/4042194944) }) = true
      norm_num [leaf2834Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2834CertificateValid :
    WideCertificateValid leaf2834Box leaf2834Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi206ValidityFacts
    leaf2834LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2834CoverageChecked :
    coverageCheck (innerAD leaf2834Box) leaf2834InnerLog = true := by
  rfl'

private theorem leaf2834InnerLogValid :
    leaf2834InnerLog.Valid 8 (innerAD leaf2834Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint49PositiveFacts.valid leaf2834CoverageChecked

private noncomputable def leaf2834InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2834InputLogOnePlusV_eq :
    leaf2834InputLogOnePlusV = outerEnclosure 24
      (leaf2834Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2834RoundedFacts : LeafRoundedFacts 8
    leaf2834Certificate.logOnePlusV leaf2834InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2834InputLogOnePlusV_eq }

private noncomputable def leaf2834Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi206InputQChi innerPair47Input
    leaf2834InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2834LowerChecked :
    lowerCheck 24 leaf2834Box leaf2834Inputs = true := by
  rfl'

private theorem leaf2834CoversExact : CoversExact 8
    leaf2834Box leaf2834Certificate leaf2834InnerLog leaf2834Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi206RoundedFacts
    innerPair47RoundedFacts leaf2834RoundedFacts (by rfl)

private theorem leaf2834FlatSound : Sound leaf2834Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2834CertificateValid
    leaf2834InnerLogValid leaf2834CoversExact leaf2834LowerChecked

private noncomputable def leaf2835Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2835Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742211/1073741824) }, vSqrt := { lower := (8191/8192), upper := (22906164565/22905766144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1618672783/1073741824) }, upper := { exponent := 0, mantissa := (24893/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (45811930709/45811532288) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf2835InnerLog : WideLogData :=
  innerPair413Data

set_option maxRecDepth 1000000 in
private theorem leaf2835LocalValidity :
    LeafFacts leaf2835Box leaf2835Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2835Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22906164565/22905766144) }) = true
      norm_num [leaf2835Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2835CertificateValid :
    WideCertificateValid leaf2835Box leaf2835Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi203ValidityFacts
    leaf2835LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2835CoverageChecked :
    coverageCheck (innerAD leaf2835Box) leaf2835InnerLog = true := by
  rfl'

private theorem leaf2835InnerLogValid :
    leaf2835InnerLog.Valid 8 (innerAD leaf2835Box) :=
  wideLogDataValid_of_cachedCheck endpoint123PositiveFacts
    endpoint121PositiveFacts.valid leaf2835CoverageChecked

private noncomputable def leaf2835InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2835InputLogOnePlusV_eq :
    leaf2835InputLogOnePlusV = outerEnclosure 24
      (leaf2835Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2835RoundedFacts : LeafRoundedFacts 8
    leaf2835Certificate.logOnePlusV leaf2835InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2835InputLogOnePlusV_eq }

private noncomputable def leaf2835Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi203InputQChi innerPair413Input
    leaf2835InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2835LowerChecked :
    lowerCheck 24 leaf2835Box leaf2835Inputs = true := by
  rfl'

private theorem leaf2835CoversExact : CoversExact 8
    leaf2835Box leaf2835Certificate leaf2835InnerLog leaf2835Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi203RoundedFacts
    innerPair413RoundedFacts leaf2835RoundedFacts (by rfl)

private theorem leaf2835FlatSound : Sound leaf2835Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2835CertificateValid
    leaf2835InnerLogValid leaf2835CoversExact leaf2835LowerChecked

private noncomputable def leaf2836Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2836Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742213/1073741824) }, vSqrt := { lower := (8191/8192), upper := (13743698739/13743453184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1626929813/1073741824) }, upper := { exponent := 0, mantissa := (6255/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (27487151923/27486906368) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf2836InnerLog : WideLogData :=
  innerPair44Data

set_option maxRecDepth 1000000 in
private theorem leaf2836LocalValidity :
    LeafFacts leaf2836Box leaf2836Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2836Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (13743698739/13743453184) }) = true
      norm_num [leaf2836Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2836CertificateValid :
    WideCertificateValid leaf2836Box leaf2836Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi204ValidityFacts
    leaf2836LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2836CoverageChecked :
    coverageCheck (innerAD leaf2836Box) leaf2836InnerLog = true := by
  rfl'

private theorem leaf2836InnerLogValid :
    leaf2836InnerLog.Valid 8 (innerAD leaf2836Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint19PositiveFacts.valid leaf2836CoverageChecked

private noncomputable def leaf2836InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2836InputLogOnePlusV_eq :
    leaf2836InputLogOnePlusV = outerEnclosure 24
      (leaf2836Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2836RoundedFacts : LeafRoundedFacts 8
    leaf2836Certificate.logOnePlusV leaf2836InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2836InputLogOnePlusV_eq }

private noncomputable def leaf2836Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi204InputQChi innerPair44Input
    leaf2836InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2836LowerChecked :
    lowerCheck 24 leaf2836Box leaf2836Inputs = true := by
  rfl'

private theorem leaf2836CoversExact : CoversExact 8
    leaf2836Box leaf2836Certificate leaf2836InnerLog leaf2836Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi204RoundedFacts
    innerPair44RoundedFacts leaf2836RoundedFacts (by rfl)

private theorem leaf2836FlatSound : Sound leaf2836Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2836CertificateValid
    leaf2836InnerLogValid leaf2836CoversExact leaf2836LowerChecked

private noncomputable def leaf2837Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (33/256), chiHi := (67/512) }

private noncomputable def leaf2837Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742213/1073741824) }, vSqrt := { lower := (65527/65536), upper := (13743698739/13743456256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1622997893/1073741824) }, upper := { exponent := 0, mantissa := (195/128) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi203LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (27487154995/27486912512) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf2837InnerLog : WideLogData :=
  innerPair83Data

set_option maxRecDepth 1000000 in
private theorem leaf2837LocalValidity :
    LeafFacts leaf2837Box leaf2837Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2837Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (13743698739/13743456256) }) = true
      norm_num [leaf2837Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2837CertificateValid :
    WideCertificateValid leaf2837Box leaf2837Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi203ValidityFacts
    leaf2837LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2837CoverageChecked :
    coverageCheck (innerAD leaf2837Box) leaf2837InnerLog = true := by
  rfl'

private theorem leaf2837InnerLogValid :
    leaf2837InnerLog.Valid 8 (innerAD leaf2837Box) :=
  wideLogDataValid_of_cachedCheck endpoint18PositiveFacts
    endpoint197PositiveFacts.valid leaf2837CoverageChecked

private noncomputable def leaf2837InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2837InputLogOnePlusV_eq :
    leaf2837InputLogOnePlusV = outerEnclosure 24
      (leaf2837Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2837RoundedFacts : LeafRoundedFacts 8
    leaf2837Certificate.logOnePlusV leaf2837InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2837InputLogOnePlusV_eq }

private noncomputable def leaf2837Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi203InputQChi innerPair83Input
    leaf2837InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2837LowerChecked :
    lowerCheck 24 leaf2837Box leaf2837Inputs = true := by
  rfl'

private theorem leaf2837CoversExact : CoversExact 8
    leaf2837Box leaf2837Certificate leaf2837InnerLog leaf2837Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi203RoundedFacts
    innerPair83RoundedFacts leaf2837RoundedFacts (by rfl)

private theorem leaf2837FlatSound : Sound leaf2837Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2837CertificateValid
    leaf2837InnerLogValid leaf2837CoversExact leaf2837LowerChecked

private noncomputable def leaf2838Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (67/512), chiHi := (17/128) }

private noncomputable def leaf2838Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742215/1073741824) }, vSqrt := { lower := (65527/65536), upper := (22906164565/22905749504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1631320455/1073741824) }, upper := { exponent := 0, mantissa := (49/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi204LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (45811914069/45811499008) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf2838InnerLog : WideLogData :=
  innerPair176Data

set_option maxRecDepth 1000000 in
private theorem leaf2838LocalValidity :
    LeafFacts leaf2838Box leaf2838Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2838Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (22906164565/22905749504) }) = true
      norm_num [leaf2838Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2838CertificateValid :
    WideCertificateValid leaf2838Box leaf2838Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi204ValidityFacts
    leaf2838LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2838CoverageChecked :
    coverageCheck (innerAD leaf2838Box) leaf2838InnerLog = true := by
  rfl'

private theorem leaf2838InnerLogValid :
    leaf2838InnerLog.Valid 8 (innerAD leaf2838Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint19PositiveFacts.valid leaf2838CoverageChecked

private noncomputable def leaf2838InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2838InputLogOnePlusV_eq :
    leaf2838InputLogOnePlusV = outerEnclosure 24
      (leaf2838Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2838RoundedFacts : LeafRoundedFacts 8
    leaf2838Certificate.logOnePlusV leaf2838InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2838InputLogOnePlusV_eq }

private noncomputable def leaf2838Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi204InputQChi innerPair176Input
    leaf2838InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2838LowerChecked :
    lowerCheck 24 leaf2838Box leaf2838Inputs = true := by
  rfl'

private theorem leaf2838CoversExact : CoversExact 8
    leaf2838Box leaf2838Certificate leaf2838InnerLog leaf2838Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi204RoundedFacts
    innerPair176RoundedFacts leaf2838RoundedFacts (by rfl)

private theorem leaf2838FlatSound : Sound leaf2838Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2838CertificateValid
    leaf2838InnerLogValid leaf2838CoversExact leaf2838LowerChecked

private noncomputable def leaf2839Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (17/128), chiHi := (69/512) }

private noncomputable def leaf2839Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742215/1073741824) }, vSqrt := { lower := (8191/8192), upper := (68718493695/68717233408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1635186843/1073741824) }, upper := { exponent := 0, mantissa := (25147/16384) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi207LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (137435727103/137434466816) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf2839InnerLog : WideLogData :=
  innerPair411Data

set_option maxRecDepth 1000000 in
private theorem leaf2839LocalValidity :
    LeafFacts leaf2839Box leaf2839Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2839Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (68718493695/68717233408) }) = true
      norm_num [leaf2839Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2839CertificateValid :
    WideCertificateValid leaf2839Box leaf2839Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi207ValidityFacts
    leaf2839LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2839CoverageChecked :
    coverageCheck (innerAD leaf2839Box) leaf2839InnerLog = true := by
  rfl'

private theorem leaf2839InnerLogValid :
    leaf2839InnerLog.Valid 8 (innerAD leaf2839Box) :=
  wideLogDataValid_of_cachedCheck endpoint121PositiveFacts
    endpoint124PositiveFacts.valid leaf2839CoverageChecked

private noncomputable def leaf2839InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2839InputLogOnePlusV_eq :
    leaf2839InputLogOnePlusV = outerEnclosure 24
      (leaf2839Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2839RoundedFacts : LeafRoundedFacts 8
    leaf2839Certificate.logOnePlusV leaf2839InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2839InputLogOnePlusV_eq }

private noncomputable def leaf2839Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi207InputQChi innerPair411Input
    leaf2839InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2839LowerChecked :
    lowerCheck 24 leaf2839Box leaf2839Inputs = true := by
  rfl'

private theorem leaf2839CoversExact : CoversExact 8
    leaf2839Box leaf2839Certificate leaf2839InnerLog leaf2839Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi207RoundedFacts
    innerPair411RoundedFacts leaf2839RoundedFacts (by rfl)

private theorem leaf2839FlatSound : Sound leaf2839Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2839CertificateValid
    leaf2839InnerLogValid leaf2839CoversExact leaf2839LowerChecked

private noncomputable def leaf2840Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (69/512), chiHi := (35/256) }

private noncomputable def leaf2840Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484293/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434419712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3286920653/2147483648) }, upper := { exponent := 0, mantissa := (25239/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi208LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871341567/274868839424) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2840InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2840LocalValidity :
    LeafFacts leaf2840Box leaf2840Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2840Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434419712) }) = true
      norm_num [leaf2840Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2840CertificateValid :
    WideCertificateValid leaf2840Box leaf2840Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi208ValidityFacts
    leaf2840LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2840CoverageChecked :
    coverageCheck (innerAD leaf2840Box) leaf2840InnerLog = true := by
  rfl'

private theorem leaf2840InnerLogValid :
    leaf2840InnerLog.Valid 8 (innerAD leaf2840Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2840CoverageChecked

private noncomputable def leaf2840InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2840InputLogOnePlusV_eq :
    leaf2840InputLogOnePlusV = outerEnclosure 24
      (leaf2840Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2840RoundedFacts : LeafRoundedFacts 8
    leaf2840Certificate.logOnePlusV leaf2840InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2840InputLogOnePlusV_eq }

private noncomputable def leaf2840Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi208InputQChi innerPair40Input
    leaf2840InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2840LowerChecked :
    lowerCheck 24 leaf2840Box leaf2840Inputs = true := by
  rfl'

private theorem leaf2840CoversExact : CoversExact 8
    leaf2840Box leaf2840Certificate leaf2840InnerLog leaf2840Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi208RoundedFacts
    innerPair40RoundedFacts leaf2840RoundedFacts (by rfl)

private theorem leaf2840FlatSound : Sound leaf2840Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2840CertificateValid
    leaf2840InnerLogValid leaf2840CoversExact leaf2840LowerChecked

private noncomputable def leaf2841Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (69/512), chiHi := (35/256) }

private noncomputable def leaf2841Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484295/2147483648) }, vSqrt := { lower := (8191/8192), upper := (898280535/898264064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3291442359/2147483648) }, upper := { exponent := 0, mantissa := (12637/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi208LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1796544599/1796528128) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2841InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2841LocalValidity :
    LeafFacts leaf2841Box leaf2841Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2841Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (898280535/898264064) }) = true
      norm_num [leaf2841Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2841CertificateValid :
    WideCertificateValid leaf2841Box leaf2841Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi208ValidityFacts
    leaf2841LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2841CoverageChecked :
    coverageCheck (innerAD leaf2841Box) leaf2841InnerLog = true := by
  rfl'

private theorem leaf2841InnerLogValid :
    leaf2841InnerLog.Valid 8 (innerAD leaf2841Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2841CoverageChecked

private noncomputable def leaf2841InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2841InputLogOnePlusV_eq :
    leaf2841InputLogOnePlusV = outerEnclosure 24
      (leaf2841Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2841RoundedFacts : LeafRoundedFacts 8
    leaf2841Certificate.logOnePlusV leaf2841InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2841InputLogOnePlusV_eq }

private noncomputable def leaf2841Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi208InputQChi innerPair40Input
    leaf2841InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2841LowerChecked :
    lowerCheck 24 leaf2841Box leaf2841Inputs = true := by
  rfl'

private theorem leaf2841CoversExact : CoversExact 8
    leaf2841Box leaf2841Certificate leaf2841InnerLog leaf2841Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi208RoundedFacts
    innerPair40RoundedFacts leaf2841RoundedFacts (by rfl)

private theorem leaf2841FlatSound : Sound leaf2841Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2841CertificateValid
    leaf2841InnerLogValid leaf2841CoversExact leaf2841LowerChecked

private noncomputable def leaf2842Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2842Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434290176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1651700721/1073741824) }, upper := { exponent := 0, mantissa := (6373/4096) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871212031/274868580352) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2842InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2842LocalValidity :
    LeafFacts leaf2842Box leaf2842Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2842Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434290176) }) = true
      norm_num [leaf2842Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2842CertificateValid :
    WideCertificateValid leaf2842Box leaf2842Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi180ValidityFacts
    leaf2842LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2842CoverageChecked :
    coverageCheck (innerAD leaf2842Box) leaf2842InnerLog = true := by
  rfl'

private theorem leaf2842InnerLogValid :
    leaf2842InnerLog.Valid 8 (innerAD leaf2842Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2842CoverageChecked

private noncomputable def leaf2842InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2842InputLogOnePlusV_eq :
    leaf2842InputLogOnePlusV = outerEnclosure 24
      (leaf2842Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2842RoundedFacts : LeafRoundedFacts 8
    leaf2842Certificate.logOnePlusV leaf2842InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2842InputLogOnePlusV_eq }

private noncomputable def leaf2842Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2842InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2842LowerChecked :
    lowerCheck 24 leaf2842Box leaf2842Inputs = true := by
  rfl'

private theorem leaf2842CoversExact : CoversExact 8
    leaf2842Box leaf2842Certificate leaf2842InnerLog leaf2842Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2842RoundedFacts (by rfl)

private theorem leaf2842FlatSound : Sound leaf2842Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2842CertificateValid
    leaf2842InnerLogValid leaf2842CoversExact leaf2842LowerChecked

private noncomputable def leaf2843Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2843Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434271744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1653994339/1073741824) }, upper := { exponent := 0, mantissa := (3191/2048) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871193599/274868543488) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2843InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2843LocalValidity :
    LeafFacts leaf2843Box leaf2843Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2843Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434271744) }) = true
      norm_num [leaf2843Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2843CertificateValid :
    WideCertificateValid leaf2843Box leaf2843Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi180ValidityFacts
    leaf2843LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2843CoverageChecked :
    coverageCheck (innerAD leaf2843Box) leaf2843InnerLog = true := by
  rfl'

private theorem leaf2843InnerLogValid :
    leaf2843InnerLog.Valid 8 (innerAD leaf2843Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2843CoverageChecked

private noncomputable def leaf2843InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2843InputLogOnePlusV_eq :
    leaf2843InputLogOnePlusV = outerEnclosure 24
      (leaf2843Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2843RoundedFacts : LeafRoundedFacts 8
    leaf2843Certificate.logOnePlusV leaf2843InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2843InputLogOnePlusV_eq }

private noncomputable def leaf2843Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2843InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2843LowerChecked :
    lowerCheck 24 leaf2843Box leaf2843Inputs = true := by
  rfl'

private theorem leaf2843CoversExact : CoversExact 8
    leaf2843Box leaf2843Certificate leaf2843InnerLog leaf2843Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2843RoundedFacts (by rfl)

private theorem leaf2843FlatSound : Sound leaf2843Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2843CertificateValid
    leaf2843InnerLogValid leaf2843CoversExact leaf2843LowerChecked

private noncomputable def leaf2844Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (17/128), chiHi := (69/512) }

private noncomputable def leaf2844Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484295/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434449152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3279318939/2147483648) }, upper := { exponent := 0, mantissa := (50363/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi207LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871371007/274868898304) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2844InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2844LocalValidity :
    LeafFacts leaf2844Box leaf2844Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2844Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434449152) }) = true
      norm_num [leaf2844Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2844CertificateValid :
    WideCertificateValid leaf2844Box leaf2844Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi207ValidityFacts
    leaf2844LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2844CoverageChecked :
    coverageCheck (innerAD leaf2844Box) leaf2844InnerLog = true := by
  rfl'

private theorem leaf2844InnerLogValid :
    leaf2844InnerLog.Valid 8 (innerAD leaf2844Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2844CoverageChecked

private noncomputable def leaf2844InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2844InputLogOnePlusV_eq :
    leaf2844InputLogOnePlusV = outerEnclosure 24
      (leaf2844Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2844RoundedFacts : LeafRoundedFacts 8
    leaf2844Certificate.logOnePlusV leaf2844InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2844InputLogOnePlusV_eq }

private noncomputable def leaf2844Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi207InputQChi innerPair40Input
    leaf2844InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2844LowerChecked :
    lowerCheck 24 leaf2844Box leaf2844Inputs = true := by
  rfl'

private theorem leaf2844CoversExact : CoversExact 8
    leaf2844Box leaf2844Certificate leaf2844InnerLog leaf2844Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi207RoundedFacts
    innerPair40RoundedFacts leaf2844RoundedFacts (by rfl)

private theorem leaf2844FlatSound : Sound leaf2844Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2844CertificateValid
    leaf2844InnerLogValid leaf2844CoversExact leaf2844LowerChecked

private noncomputable def leaf2845Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (17/128), chiHi := (69/512) }

private noncomputable def leaf2845Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484297/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137434431488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3283775113/2147483648) }, upper := { exponent := 0, mantissa := (197/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi207LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274871353343/274868862976) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2845InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2845LocalValidity :
    LeafFacts leaf2845Box leaf2845Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2845Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137434431488) }) = true
      norm_num [leaf2845Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2845CertificateValid :
    WideCertificateValid leaf2845Box leaf2845Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi207ValidityFacts
    leaf2845LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2845CoverageChecked :
    coverageCheck (innerAD leaf2845Box) leaf2845InnerLog = true := by
  rfl'

private theorem leaf2845InnerLogValid :
    leaf2845InnerLog.Valid 8 (innerAD leaf2845Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2845CoverageChecked

private noncomputable def leaf2845InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2845InputLogOnePlusV_eq :
    leaf2845InputLogOnePlusV = outerEnclosure 24
      (leaf2845Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2845RoundedFacts : LeafRoundedFacts 8
    leaf2845Certificate.logOnePlusV leaf2845InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2845InputLogOnePlusV_eq }

private noncomputable def leaf2845Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi207InputQChi innerPair40Input
    leaf2845InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2845LowerChecked :
    lowerCheck 24 leaf2845Box leaf2845Inputs = true := by
  rfl'

private theorem leaf2845CoversExact : CoversExact 8
    leaf2845Box leaf2845Certificate leaf2845InnerLog leaf2845Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi207RoundedFacts
    innerPair40RoundedFacts leaf2845RoundedFacts (by rfl)

private theorem leaf2845FlatSound : Sound leaf2845Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2845CertificateValid
    leaf2845InnerLogValid leaf2845CoversExact leaf2845LowerChecked

private noncomputable def leaf2846Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (69/512), chiHi := (35/256) }

private noncomputable def leaf2846Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484297/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434383872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3295964065/2147483648) }, upper := { exponent := 0, mantissa := (25309/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi208LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871305727/274868767744) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2846InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2846LocalValidity :
    LeafFacts leaf2846Box leaf2846Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2846Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434383872) }) = true
      norm_num [leaf2846Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2846CertificateValid :
    WideCertificateValid leaf2846Box leaf2846Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi208ValidityFacts
    leaf2846LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2846CoverageChecked :
    coverageCheck (innerAD leaf2846Box) leaf2846InnerLog = true := by
  rfl'

private theorem leaf2846InnerLogValid :
    leaf2846InnerLog.Valid 8 (innerAD leaf2846Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2846CoverageChecked

private noncomputable def leaf2846InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2846InputLogOnePlusV_eq :
    leaf2846InputLogOnePlusV = outerEnclosure 24
      (leaf2846Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2846RoundedFacts : LeafRoundedFacts 8
    leaf2846Certificate.logOnePlusV leaf2846InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2846InputLogOnePlusV_eq }

private noncomputable def leaf2846Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi208InputQChi innerPair40Input
    leaf2846InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2846LowerChecked :
    lowerCheck 24 leaf2846Box leaf2846Inputs = true := by
  rfl'

private theorem leaf2846CoversExact : CoversExact 8
    leaf2846Box leaf2846Certificate leaf2846InnerLog leaf2846Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi208RoundedFacts
    innerPair40RoundedFacts leaf2846RoundedFacts (by rfl)

private theorem leaf2846FlatSound : Sound leaf2846Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2846CertificateValid
    leaf2846InnerLogValid leaf2846CoversExact leaf2846LowerChecked

private noncomputable def leaf2847Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (69/512), chiHi := (35/256) }

private noncomputable def leaf2847Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484299/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137434365952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3300485771/2147483648) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi208LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274871287807/274868731904) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2847InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2847LocalValidity :
    LeafFacts leaf2847Box leaf2847Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2847Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137434365952) }) = true
      norm_num [leaf2847Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2847CertificateValid :
    WideCertificateValid leaf2847Box leaf2847Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi208ValidityFacts
    leaf2847LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2847CoverageChecked :
    coverageCheck (innerAD leaf2847Box) leaf2847InnerLog = true := by
  rfl'

private theorem leaf2847InnerLogValid :
    leaf2847InnerLog.Valid 8 (innerAD leaf2847Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2847CoverageChecked

private noncomputable def leaf2847InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2847InputLogOnePlusV_eq :
    leaf2847InputLogOnePlusV = outerEnclosure 24
      (leaf2847Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2847RoundedFacts : LeafRoundedFacts 8
    leaf2847Certificate.logOnePlusV leaf2847InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2847InputLogOnePlusV_eq }

private noncomputable def leaf2847Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi208InputQChi innerPair40Input
    leaf2847InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2847LowerChecked :
    lowerCheck 24 leaf2847Box leaf2847Inputs = true := by
  rfl'

private theorem leaf2847CoversExact : CoversExact 8
    leaf2847Box leaf2847Certificate leaf2847InnerLog leaf2847Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi208RoundedFacts
    innerPair40RoundedFacts leaf2847RoundedFacts (by rfl)

private theorem leaf2847FlatSound : Sound leaf2847Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2847CertificateValid
    leaf2847InnerLogValid leaf2847CoversExact leaf2847LowerChecked

private noncomputable def leaf2848Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2848Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434253312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1656287957/1073741824) }, upper := { exponent := 0, mantissa := (6391/4096) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871175167/274868506624) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2848InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2848LocalValidity :
    LeafFacts leaf2848Box leaf2848Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2848Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434253312) }) = true
      norm_num [leaf2848Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2848CertificateValid :
    WideCertificateValid leaf2848Box leaf2848Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi180ValidityFacts
    leaf2848LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2848CoverageChecked :
    coverageCheck (innerAD leaf2848Box) leaf2848InnerLog = true := by
  rfl'

private theorem leaf2848InnerLogValid :
    leaf2848InnerLog.Valid 8 (innerAD leaf2848Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2848CoverageChecked

private noncomputable def leaf2848InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2848InputLogOnePlusV_eq :
    leaf2848InputLogOnePlusV = outerEnclosure 24
      (leaf2848Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2848RoundedFacts : LeafRoundedFacts 8
    leaf2848Certificate.logOnePlusV leaf2848InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2848InputLogOnePlusV_eq }

private noncomputable def leaf2848Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2848InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2848LowerChecked :
    lowerCheck 24 leaf2848Box leaf2848Inputs = true := by
  rfl'

private theorem leaf2848CoversExact : CoversExact 8
    leaf2848Box leaf2848Certificate leaf2848InnerLog leaf2848Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2848RoundedFacts (by rfl)

private theorem leaf2848FlatSound : Sound leaf2848Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2848CertificateValid
    leaf2848InnerLogValid leaf2848CoversExact leaf2848LowerChecked

private noncomputable def leaf2849Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (35/256), chiHi := (9/64) }

private noncomputable def leaf2849Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (65527/65536), upper := (27487384371/27486846976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1658581575/1073741824) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi180LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (54974231347/54973693952) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2849InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2849LocalValidity :
    LeafFacts leaf2849Box leaf2849Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2849Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (27487384371/27486846976) }) = true
      norm_num [leaf2849Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2849CertificateValid :
    WideCertificateValid leaf2849Box leaf2849Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi180ValidityFacts
    leaf2849LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2849CoverageChecked :
    coverageCheck (innerAD leaf2849Box) leaf2849InnerLog = true := by
  rfl'

private theorem leaf2849InnerLogValid :
    leaf2849InnerLog.Valid 8 (innerAD leaf2849Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2849CoverageChecked

private noncomputable def leaf2849InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2849InputLogOnePlusV_eq :
    leaf2849InputLogOnePlusV = outerEnclosure 24
      (leaf2849Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2849RoundedFacts : LeafRoundedFacts 8
    leaf2849Certificate.logOnePlusV leaf2849InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2849InputLogOnePlusV_eq }

private noncomputable def leaf2849Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi180InputQChi innerPair40Input
    leaf2849InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2849LowerChecked :
    lowerCheck 24 leaf2849Box leaf2849Inputs = true := by
  rfl'

private theorem leaf2849CoversExact : CoversExact 8
    leaf2849Box leaf2849Certificate leaf2849InnerLog leaf2849Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi180RoundedFacts
    innerPair40RoundedFacts leaf2849RoundedFacts (by rfl)

private theorem leaf2849FlatSound : Sound leaf2849Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2849CertificateValid
    leaf2849InnerLogValid leaf2849CoversExact leaf2849LowerChecked

private noncomputable def component59Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node0_sound : Sound component59Node0Box :=
  sound_of_literal_split component59Node0Box leaf2815Box leaf2816Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2815FlatSound leaf2816FlatSound

private noncomputable def component59Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node1_sound : Sound component59Node1Box :=
  sound_of_literal_split component59Node1Box leaf2817Box leaf2818Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2817FlatSound leaf2818FlatSound

private noncomputable def component59Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node2_sound : Sound component59Node2Box :=
  sound_of_literal_split component59Node2Box component59Node0Box component59Node1Box
    .k (125/32) (by rfl) (by rfl)
    component59Node0_sound component59Node1_sound

private noncomputable def component59Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node3_sound : Sound component59Node3Box :=
  sound_of_literal_split component59Node3Box leaf2819Box leaf2820Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2819FlatSound leaf2820FlatSound

private noncomputable def component59Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node4_sound : Sound component59Node4Box :=
  sound_of_literal_split component59Node4Box leaf2821Box leaf2822Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2821FlatSound leaf2822FlatSound

private noncomputable def component59Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node5_sound : Sound component59Node5Box :=
  sound_of_literal_split component59Node5Box component59Node3Box component59Node4Box
    .k (125/32) (by rfl) (by rfl)
    component59Node3_sound component59Node4_sound

private noncomputable def component59Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node6_sound : Sound component59Node6Box :=
  sound_of_literal_split component59Node6Box component59Node2Box component59Node5Box
    .chi (33/256) (by rfl) (by rfl)
    component59Node2_sound component59Node5_sound

private noncomputable def component59Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node7_sound : Sound component59Node7Box :=
  sound_of_literal_split component59Node7Box leaf2823Box leaf2824Box
    .chi (69/512) (by rfl) (by rfl)
    leaf2823FlatSound leaf2824FlatSound

private noncomputable def component59Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node8_sound : Sound component59Node8Box :=
  sound_of_literal_split component59Node8Box leaf2825Box leaf2826Box
    .k (249/64) (by rfl) (by rfl)
    leaf2825FlatSound leaf2826FlatSound

private noncomputable def component59Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node9_sound : Sound component59Node9Box :=
  sound_of_literal_split component59Node9Box component59Node7Box component59Node8Box
    .chi (35/256) (by rfl) (by rfl)
    component59Node7_sound component59Node8_sound

private noncomputable def component59Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node10_sound : Sound component59Node10Box :=
  sound_of_literal_split component59Node10Box leaf2827Box leaf2828Box
    .chi (69/512) (by rfl) (by rfl)
    leaf2827FlatSound leaf2828FlatSound

private noncomputable def component59Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node11_sound : Sound component59Node11Box :=
  sound_of_literal_split component59Node11Box leaf2829Box leaf2830Box
    .k (251/64) (by rfl) (by rfl)
    leaf2829FlatSound leaf2830FlatSound

private noncomputable def component59Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node12_sound : Sound component59Node12Box :=
  sound_of_literal_split component59Node12Box component59Node10Box component59Node11Box
    .chi (35/256) (by rfl) (by rfl)
    component59Node10_sound component59Node11_sound

private noncomputable def component59Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node13_sound : Sound component59Node13Box :=
  sound_of_literal_split component59Node13Box component59Node9Box component59Node12Box
    .k (125/32) (by rfl) (by rfl)
    component59Node9_sound component59Node12_sound

private noncomputable def component59Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node14_sound : Sound component59Node14Box :=
  sound_of_literal_split component59Node14Box component59Node6Box component59Node13Box
    .chi (17/128) (by rfl) (by rfl)
    component59Node6_sound component59Node13_sound

private noncomputable def component59Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node15_sound : Sound component59Node15Box :=
  sound_of_literal_split component59Node15Box leaf2831Box leaf2832Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2831FlatSound leaf2832FlatSound

private noncomputable def component59Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node16_sound : Sound component59Node16Box :=
  sound_of_literal_split component59Node16Box leaf2833Box leaf2834Box
    .chi (65/512) (by rfl) (by rfl)
    leaf2833FlatSound leaf2834FlatSound

private noncomputable def component59Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/8), chiHi := (33/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node17_sound : Sound component59Node17Box :=
  sound_of_literal_split component59Node17Box component59Node15Box component59Node16Box
    .k (127/32) (by rfl) (by rfl)
    component59Node15_sound component59Node16_sound

private noncomputable def component59Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node18_sound : Sound component59Node18Box :=
  sound_of_literal_split component59Node18Box leaf2835Box leaf2836Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2835FlatSound leaf2836FlatSound

private noncomputable def component59Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node19_sound : Sound component59Node19Box :=
  sound_of_literal_split component59Node19Box leaf2837Box leaf2838Box
    .chi (67/512) (by rfl) (by rfl)
    leaf2837FlatSound leaf2838FlatSound

private noncomputable def component59Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (33/256), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node20_sound : Sound component59Node20Box :=
  sound_of_literal_split component59Node20Box component59Node18Box component59Node19Box
    .k (127/32) (by rfl) (by rfl)
    component59Node18_sound component59Node19_sound

private noncomputable def component59Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component59Node21_sound : Sound component59Node21Box :=
  sound_of_literal_split component59Node21Box component59Node17Box component59Node20Box
    .chi (33/256) (by rfl) (by rfl)
    component59Node17_sound component59Node20_sound

private noncomputable def component59Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (69/512), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node22_sound : Sound component59Node22Box :=
  sound_of_literal_split component59Node22Box leaf2840Box leaf2841Box
    .k (253/64) (by rfl) (by rfl)
    leaf2840FlatSound leaf2841FlatSound

private noncomputable def component59Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node23_sound : Sound component59Node23Box :=
  sound_of_literal_split component59Node23Box leaf2839Box component59Node22Box
    .chi (69/512) (by rfl) (by rfl)
    leaf2839FlatSound component59Node22_sound

private noncomputable def component59Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node24_sound : Sound component59Node24Box :=
  sound_of_literal_split component59Node24Box leaf2842Box leaf2843Box
    .k (253/64) (by rfl) (by rfl)
    leaf2842FlatSound leaf2843FlatSound

private noncomputable def component59Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node25_sound : Sound component59Node25Box :=
  sound_of_literal_split component59Node25Box component59Node23Box component59Node24Box
    .chi (35/256) (by rfl) (by rfl)
    component59Node23_sound component59Node24_sound

private noncomputable def component59Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (17/128), chiHi := (69/512) }

set_option maxRecDepth 1000000 in
private theorem component59Node26_sound : Sound component59Node26Box :=
  sound_of_literal_split component59Node26Box leaf2844Box leaf2845Box
    .k (255/64) (by rfl) (by rfl)
    leaf2844FlatSound leaf2845FlatSound

private noncomputable def component59Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (69/512), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node27_sound : Sound component59Node27Box :=
  sound_of_literal_split component59Node27Box leaf2846Box leaf2847Box
    .k (255/64) (by rfl) (by rfl)
    leaf2846FlatSound leaf2847FlatSound

private noncomputable def component59Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (17/128), chiHi := (35/256) }

set_option maxRecDepth 1000000 in
private theorem component59Node28_sound : Sound component59Node28Box :=
  sound_of_literal_split component59Node28Box component59Node26Box component59Node27Box
    .chi (69/512) (by rfl) (by rfl)
    component59Node26_sound component59Node27_sound

private noncomputable def component59Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (35/256), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node29_sound : Sound component59Node29Box :=
  sound_of_literal_split component59Node29Box leaf2848Box leaf2849Box
    .k (255/64) (by rfl) (by rfl)
    leaf2848FlatSound leaf2849FlatSound

private noncomputable def component59Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node30_sound : Sound component59Node30Box :=
  sound_of_literal_split component59Node30Box component59Node28Box component59Node29Box
    .chi (35/256) (by rfl) (by rfl)
    component59Node28_sound component59Node29_sound

private noncomputable def component59Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node31_sound : Sound component59Node31Box :=
  sound_of_literal_split component59Node31Box component59Node25Box component59Node30Box
    .k (127/32) (by rfl) (by rfl)
    component59Node25_sound component59Node30_sound

private noncomputable def component59Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component59Node32_sound : Sound component59Node32Box :=
  sound_of_literal_split component59Node32Box component59Node21Box component59Node31Box
    .chi (17/128) (by rfl) (by rfl)
    component59Node21_sound component59Node31_sound

noncomputable def component59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
theorem component59_sound : Sound component59Box :=
  sound_of_literal_split component59Box component59Node14Box component59Node32Box
    .k (63/16) (by rfl) (by rfl)
    component59Node14_sound component59Node32_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
