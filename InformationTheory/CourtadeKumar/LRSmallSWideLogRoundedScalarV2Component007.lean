import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf288Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf288Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554483/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388455) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (41909711/33554432) }, upper := { exponent := 0, mantissa := (665/512) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777079/16776910) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf288InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf288LocalValidity :
    LeafFacts leaf288Box leaf288Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf288Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388455) }) = true
      norm_num [leaf288Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf288CertificateValid :
    WideCertificateValid leaf288Box leaf288Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi46ValidityFacts
    leaf288LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf288CoverageChecked :
    coverageCheck (innerAD leaf288Box) leaf288InnerLog = true := by
  rfl'

private theorem leaf288InnerLogValid :
    leaf288InnerLog.Valid 8 (innerAD leaf288Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf288CoverageChecked

private noncomputable def leaf288InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf288InputLogOnePlusV_eq :
    leaf288InputLogOnePlusV = outerEnclosure 24
      (leaf288Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf288RoundedFacts : LeafRoundedFacts 8
    leaf288Certificate.logOnePlusV leaf288InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf288InputLogOnePlusV_eq }

private noncomputable def leaf288Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi46InputQChi innerPair13Input
    leaf288InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf288LowerChecked :
    lowerCheck 24 leaf288Box leaf288Inputs = true := by
  rfl'

private theorem leaf288CoversExact : CoversExact 8
    leaf288Box leaf288Certificate leaf288InnerLog leaf288Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi46RoundedFacts
    innerPair13RoundedFacts leaf288RoundedFacts (by rfl)

private theorem leaf288FlatSound : Sound leaf288Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf288CertificateValid
    leaf288InnerLogValid leaf288CoversExact leaf288LowerChecked

private noncomputable def leaf289Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf289Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554485/33554432) }, vSqrt := { lower := (65533/65536), upper := (1398104/1398073) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (42958221/33554432) }, upper := { exponent := 0, mantissa := (341/256) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2796177/2796146) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf289InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf289LocalValidity :
    LeafFacts leaf289Box leaf289Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf289Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1398104/1398073) }) = true
      norm_num [leaf289Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf289CertificateValid :
    WideCertificateValid leaf289Box leaf289Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi47ValidityFacts
    leaf289LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf289CoverageChecked :
    coverageCheck (innerAD leaf289Box) leaf289InnerLog = true := by
  rfl'

private theorem leaf289InnerLogValid :
    leaf289InnerLog.Valid 8 (innerAD leaf289Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf289CoverageChecked

private noncomputable def leaf289InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf289InputLogOnePlusV_eq :
    leaf289InputLogOnePlusV = outerEnclosure 24
      (leaf289Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf289RoundedFacts : LeafRoundedFacts 8
    leaf289Certificate.logOnePlusV leaf289InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf289InputLogOnePlusV_eq }

private noncomputable def leaf289Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi47InputQChi innerPair17Input
    leaf289InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf289LowerChecked :
    lowerCheck 24 leaf289Box leaf289Inputs = true := by
  rfl'

private theorem leaf289CoversExact : CoversExact 8
    leaf289Box leaf289Certificate leaf289InnerLog leaf289Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi47RoundedFacts
    innerPair17RoundedFacts leaf289RoundedFacts (by rfl)

private theorem leaf289FlatSound : Sound leaf289Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf289CertificateValid
    leaf289InnerLogValid leaf289CoversExact leaf289LowerChecked

private noncomputable def leaf290Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf290Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554485/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194223) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (42433965/33554432) }, upper := { exponent := 0, mantissa := (337/256) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388535/8388446) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf290InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf290LocalValidity :
    LeafFacts leaf290Box leaf290Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf290Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194223) }) = true
      norm_num [leaf290Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf290CertificateValid :
    WideCertificateValid leaf290Box leaf290Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi46ValidityFacts
    leaf290LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf290CoverageChecked :
    coverageCheck (innerAD leaf290Box) leaf290InnerLog = true := by
  rfl'

private theorem leaf290InnerLogValid :
    leaf290InnerLog.Valid 8 (innerAD leaf290Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf290CoverageChecked

private noncomputable def leaf290InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf290InputLogOnePlusV_eq :
    leaf290InputLogOnePlusV = outerEnclosure 24
      (leaf290Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf290RoundedFacts : LeafRoundedFacts 8
    leaf290Certificate.logOnePlusV leaf290InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf290InputLogOnePlusV_eq }

private noncomputable def leaf290Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi46InputQChi innerPair17Input
    leaf290InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf290LowerChecked :
    lowerCheck 24 leaf290Box leaf290Inputs = true := by
  rfl'

private theorem leaf290CoversExact : CoversExact 8
    leaf290Box leaf290Certificate leaf290InnerLog leaf290Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi46RoundedFacts
    innerPair17RoundedFacts leaf290RoundedFacts (by rfl)

private theorem leaf290FlatSound : Sound leaf290Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf290CertificateValid
    leaf290InnerLogValid leaf290CoversExact leaf290LowerChecked

private noncomputable def leaf291Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf291Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (43548007/33554432) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194263/4194214) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf291InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf291LocalValidity :
    LeafFacts leaf291Box leaf291Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf291Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097107) }) = true
      norm_num [leaf291Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf291CertificateValid :
    WideCertificateValid leaf291Box leaf291Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi47ValidityFacts
    leaf291LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf291CoverageChecked :
    coverageCheck (innerAD leaf291Box) leaf291InnerLog = true := by
  rfl'

private theorem leaf291InnerLogValid :
    leaf291InnerLog.Valid 8 (innerAD leaf291Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf291CoverageChecked

private noncomputable def leaf291InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf291InputLogOnePlusV_eq :
    leaf291InputLogOnePlusV = outerEnclosure 24
      (leaf291Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf291RoundedFacts : LeafRoundedFacts 8
    leaf291Certificate.logOnePlusV leaf291InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf291InputLogOnePlusV_eq }

private noncomputable def leaf291Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi47InputQChi innerPair17Input
    leaf291InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf291LowerChecked :
    lowerCheck 24 leaf291Box leaf291Inputs = true := by
  rfl'

private theorem leaf291CoversExact : CoversExact 8
    leaf291Box leaf291Certificate leaf291InnerLog leaf291Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi47RoundedFacts
    innerPair17RoundedFacts leaf291RoundedFacts (by rfl)

private theorem leaf291FlatSound : Sound leaf291Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf291CertificateValid
    leaf291InnerLogValid leaf291CoversExact leaf291LowerChecked

private noncomputable def leaf292Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf292Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388421) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (44006731/33554432) }, upper := { exponent := 0, mantissa := (699/512) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777045/16776842) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf292InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf292LocalValidity :
    LeafFacts leaf292Box leaf292Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf292Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388421) }) = true
      norm_num [leaf292Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf292CertificateValid :
    WideCertificateValid leaf292Box leaf292Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi48ValidityFacts
    leaf292LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf292CoverageChecked :
    coverageCheck (innerAD leaf292Box) leaf292InnerLog = true := by
  rfl'

private theorem leaf292InnerLogValid :
    leaf292InnerLog.Valid 8 (innerAD leaf292Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf292CoverageChecked

private noncomputable def leaf292InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf292InputLogOnePlusV_eq :
    leaf292InputLogOnePlusV = outerEnclosure 24
      (leaf292Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf292RoundedFacts : LeafRoundedFacts 8
    leaf292Certificate.logOnePlusV leaf292InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf292InputLogOnePlusV_eq }

private noncomputable def leaf292Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi48InputQChi innerPair17Input
    leaf292InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf292LowerChecked :
    lowerCheck 24 leaf292Box leaf292Inputs = true := by
  rfl'

private theorem leaf292CoversExact : CoversExact 8
    leaf292Box leaf292Certificate leaf292InnerLog leaf292Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi48RoundedFacts
    innerPair17RoundedFacts leaf292RoundedFacts (by rfl)

private theorem leaf292FlatSound : Sound leaf292Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf292CertificateValid
    leaf292InnerLogValid leaf292CoversExact leaf292LowerChecked

private noncomputable def leaf293Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf293Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097101) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (45055241/33554432) }, upper := { exponent := 0, mantissa := (179/128) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194257/4194202) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf293InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf293LocalValidity :
    LeafFacts leaf293Box leaf293Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf293Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097101) }) = true
      norm_num [leaf293Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf293CertificateValid :
    WideCertificateValid leaf293Box leaf293Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi49ValidityFacts
    leaf293LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf293CoverageChecked :
    coverageCheck (innerAD leaf293Box) leaf293InnerLog = true := by
  rfl'

private theorem leaf293InnerLogValid :
    leaf293InnerLog.Valid 8 (innerAD leaf293Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf293CoverageChecked

private noncomputable def leaf293InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf293InputLogOnePlusV_eq :
    leaf293InputLogOnePlusV = outerEnclosure 24
      (leaf293Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf293RoundedFacts : LeafRoundedFacts 8
    leaf293Certificate.logOnePlusV leaf293InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf293InputLogOnePlusV_eq }

private noncomputable def leaf293Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi49InputQChi innerPair22Input
    leaf293InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf293LowerChecked :
    lowerCheck 24 leaf293Box leaf293Inputs = true := by
  rfl'

private theorem leaf293CoversExact : CoversExact 8
    leaf293Box leaf293Certificate leaf293InnerLog leaf293Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi49RoundedFacts
    innerPair22RoundedFacts leaf293RoundedFacts (by rfl)

private theorem leaf293FlatSound : Sound leaf293Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf293CertificateValid
    leaf293InnerLogValid leaf293CoversExact leaf293LowerChecked

private noncomputable def leaf294Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf294Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194205) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (44662049/33554432) }, upper := { exponent := 0, mantissa := (355/256) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388517/8388410) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf294InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf294LocalValidity :
    LeafFacts leaf294Box leaf294Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf294Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194205) }) = true
      norm_num [leaf294Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf294CertificateValid :
    WideCertificateValid leaf294Box leaf294Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi48ValidityFacts
    leaf294LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf294CoverageChecked :
    coverageCheck (innerAD leaf294Box) leaf294InnerLog = true := by
  rfl'

private theorem leaf294InnerLogValid :
    leaf294InnerLog.Valid 8 (innerAD leaf294Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf294CoverageChecked

private noncomputable def leaf294InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf294InputLogOnePlusV_eq :
    leaf294InputLogOnePlusV = outerEnclosure 24
      (leaf294Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf294RoundedFacts : LeafRoundedFacts 8
    leaf294Certificate.logOnePlusV leaf294InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf294InputLogOnePlusV_eq }

private noncomputable def leaf294Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi48InputQChi innerPair22Input
    leaf294InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf294LowerChecked :
    lowerCheck 24 leaf294Box leaf294Inputs = true := by
  rfl'

private theorem leaf294CoversExact : CoversExact 8
    leaf294Box leaf294Certificate leaf294InnerLog leaf294Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi48RoundedFacts
    innerPair22RoundedFacts leaf294RoundedFacts (by rfl)

private theorem leaf294FlatSound : Sound leaf294Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf294CertificateValid
    leaf294InnerLogValid leaf294CoversExact leaf294LowerChecked

private noncomputable def leaf295Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf295Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (65533/65536), upper := (1048578/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (45776091/33554432) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (2097127/2097098) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf295InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf295LocalValidity :
    LeafFacts leaf295Box leaf295Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf295Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (1048578/1048549) }) = true
      norm_num [leaf295Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf295CertificateValid :
    WideCertificateValid leaf295Box leaf295Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi49ValidityFacts
    leaf295LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf295CoverageChecked :
    coverageCheck (innerAD leaf295Box) leaf295InnerLog = true := by
  rfl'

private theorem leaf295InnerLogValid :
    leaf295InnerLog.Valid 8 (innerAD leaf295Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf295CoverageChecked

private noncomputable def leaf295InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf295InputLogOnePlusV_eq :
    leaf295InputLogOnePlusV = outerEnclosure 24
      (leaf295Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf295RoundedFacts : LeafRoundedFacts 8
    leaf295Certificate.logOnePlusV leaf295InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf295InputLogOnePlusV_eq }

private noncomputable def leaf295Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi49InputQChi innerPair22Input
    leaf295InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf295LowerChecked :
    lowerCheck 24 leaf295Box leaf295Inputs = true := by
  rfl'

private theorem leaf295CoversExact : CoversExact 8
    leaf295Box leaf295Certificate leaf295InnerLog leaf295Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi49RoundedFacts
    innerPair22RoundedFacts leaf295RoundedFacts (by rfl)

private theorem leaf295FlatSound : Sound leaf295Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf295CertificateValid
    leaf295InnerLogValid leaf295CoversExact leaf295LowerChecked

private noncomputable def leaf296Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf296Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554487/33554432) }, vSqrt := { lower := (65533/65536), upper := (8388624/8388437) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (42958219/33554432) }, upper := { exponent := 0, mantissa := (683/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (16777061/16776874) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf296InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf296LocalValidity :
    LeafFacts leaf296Box leaf296Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf296Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (8388624/8388437) }) = true
      norm_num [leaf296Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf296CertificateValid :
    WideCertificateValid leaf296Box leaf296Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi46ValidityFacts
    leaf296LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf296CoverageChecked :
    coverageCheck (innerAD leaf296Box) leaf296InnerLog = true := by
  rfl'

private theorem leaf296InnerLogValid :
    leaf296InnerLog.Valid 8 (innerAD leaf296Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf296CoverageChecked

private noncomputable def leaf296InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf296InputLogOnePlusV_eq :
    leaf296InputLogOnePlusV = outerEnclosure 24
      (leaf296Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf296RoundedFacts : LeafRoundedFacts 8
    leaf296Certificate.logOnePlusV leaf296InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf296InputLogOnePlusV_eq }

private noncomputable def leaf296Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi46InputQChi innerPair17Input
    leaf296InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf296LowerChecked :
    lowerCheck 24 leaf296Box leaf296Inputs = true := by
  rfl'

private theorem leaf296CoversExact : CoversExact 8
    leaf296Box leaf296Certificate leaf296InnerLog leaf296Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi46RoundedFacts
    innerPair17RoundedFacts leaf296RoundedFacts (by rfl)

private theorem leaf296FlatSound : Sound leaf296Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf296CertificateValid
    leaf296InnerLogValid leaf296CoversExact leaf296LowerChecked

private noncomputable def leaf297Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf297Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194209) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (44137793/33554432) }, upper := { exponent := 0, mantissa := (351/256) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388521/8388418) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf297InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf297LocalValidity :
    LeafFacts leaf297Box leaf297Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf297Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194209) }) = true
      norm_num [leaf297Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf297CertificateValid :
    WideCertificateValid leaf297Box leaf297Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi47ValidityFacts
    leaf297LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf297CoverageChecked :
    coverageCheck (innerAD leaf297Box) leaf297InnerLog = true := by
  rfl'

private theorem leaf297InnerLogValid :
    leaf297InnerLog.Valid 8 (innerAD leaf297Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf297CoverageChecked

private noncomputable def leaf297InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf297InputLogOnePlusV_eq :
    leaf297InputLogOnePlusV = outerEnclosure 24
      (leaf297Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf297RoundedFacts : LeafRoundedFacts 8
    leaf297Certificate.logOnePlusV leaf297InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf297InputLogOnePlusV_eq }

private noncomputable def leaf297Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi47InputQChi innerPair21Input
    leaf297InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf297LowerChecked :
    lowerCheck 24 leaf297Box leaf297Inputs = true := by
  rfl'

private theorem leaf297CoversExact : CoversExact 8
    leaf297Box leaf297Certificate leaf297InnerLog leaf297Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi47RoundedFacts
    innerPair21RoundedFacts leaf297RoundedFacts (by rfl)

private theorem leaf297FlatSound : Sound leaf297Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf297CertificateValid
    leaf297InnerLogValid leaf297CoversExact leaf297LowerChecked

private noncomputable def leaf298Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (1/4), chiHi := (9/32) }

private noncomputable def leaf298Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (43482473/33554432) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi46LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194263/4194214) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf298InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf298LocalValidity :
    LeafFacts leaf298Box leaf298Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf298Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097107) }) = true
      norm_num [leaf298Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf298CertificateValid :
    WideCertificateValid leaf298Box leaf298Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi46ValidityFacts
    leaf298LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf298CoverageChecked :
    coverageCheck (innerAD leaf298Box) leaf298InnerLog = true := by
  rfl'

private theorem leaf298InnerLogValid :
    leaf298InnerLog.Valid 8 (innerAD leaf298Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf298CoverageChecked

private noncomputable def leaf298InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf298InputLogOnePlusV_eq :
    leaf298InputLogOnePlusV = outerEnclosure 24
      (leaf298Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf298RoundedFacts : LeafRoundedFacts 8
    leaf298Certificate.logOnePlusV leaf298InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf298InputLogOnePlusV_eq }

private noncomputable def leaf298Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi46InputQChi innerPair17Input
    leaf298InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf298LowerChecked :
    lowerCheck 24 leaf298Box leaf298Inputs = true := by
  rfl'

private theorem leaf298CoversExact : CoversExact 8
    leaf298Box leaf298Certificate leaf298InnerLog leaf298Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi46RoundedFacts
    innerPair17RoundedFacts leaf298RoundedFacts (by rfl)

private theorem leaf298FlatSound : Sound leaf298Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf298CertificateValid
    leaf298InnerLogValid leaf298CoversExact leaf298LowerChecked

private noncomputable def leaf299Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (9/32), chiHi := (5/16) }

private noncomputable def leaf299Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (65533/65536), upper := (349526/349517) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (44727579/33554432) }, upper := { exponent := 0, mantissa := (89/64) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi47LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (699043/699034) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf299InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf299LocalValidity :
    LeafFacts leaf299Box leaf299Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf299Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (349526/349517) }) = true
      norm_num [leaf299Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf299CertificateValid :
    WideCertificateValid leaf299Box leaf299Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi47ValidityFacts
    leaf299LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf299CoverageChecked :
    coverageCheck (innerAD leaf299Box) leaf299InnerLog = true := by
  rfl'

private theorem leaf299InnerLogValid :
    leaf299InnerLog.Valid 8 (innerAD leaf299Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf299CoverageChecked

private noncomputable def leaf299InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf299InputLogOnePlusV_eq :
    leaf299InputLogOnePlusV = outerEnclosure 24
      (leaf299Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf299RoundedFacts : LeafRoundedFacts 8
    leaf299Certificate.logOnePlusV leaf299InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf299InputLogOnePlusV_eq }

private noncomputable def leaf299Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi47InputQChi innerPair22Input
    leaf299InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf299LowerChecked :
    lowerCheck 24 leaf299Box leaf299Inputs = true := by
  rfl'

private theorem leaf299CoversExact : CoversExact 8
    leaf299Box leaf299Certificate leaf299InnerLog leaf299Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi47RoundedFacts
    innerPair22RoundedFacts leaf299RoundedFacts (by rfl)

private theorem leaf299FlatSound : Sound leaf299Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf299CertificateValid
    leaf299InnerLogValid leaf299CoversExact leaf299LowerChecked

private noncomputable def leaf300Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf300Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (65533/65536), upper := (2796208/2796133) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (45317367/33554432) }, upper := { exponent := 0, mantissa := (721/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (5592341/5592266) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf300InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf300LocalValidity :
    LeafFacts leaf300Box leaf300Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf300Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2796208/2796133) }) = true
      norm_num [leaf300Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf300CertificateValid :
    WideCertificateValid leaf300Box leaf300Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi48ValidityFacts
    leaf300LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf300CoverageChecked :
    coverageCheck (innerAD leaf300Box) leaf300InnerLog = true := by
  rfl'

private theorem leaf300InnerLogValid :
    leaf300InnerLog.Valid 8 (innerAD leaf300Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf300CoverageChecked

private noncomputable def leaf300InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf300InputLogOnePlusV_eq :
    leaf300InputLogOnePlusV = outerEnclosure 24
      (leaf300Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf300RoundedFacts : LeafRoundedFacts 8
    leaf300Certificate.logOnePlusV leaf300InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf300InputLogOnePlusV_eq }

private noncomputable def leaf300Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi48InputQChi innerPair22Input
    leaf300InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf300LowerChecked :
    lowerCheck 24 leaf300Box leaf300Inputs = true := by
  rfl'

private theorem leaf300CoversExact : CoversExact 8
    leaf300Box leaf300Certificate leaf300InnerLog leaf300Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi48RoundedFacts
    innerPair22RoundedFacts leaf300RoundedFacts (by rfl)

private theorem leaf300FlatSound : Sound leaf300Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf300CertificateValid
    leaf300InnerLogValid leaf300CoversExact leaf300LowerChecked

private noncomputable def leaf301Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf301Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554493/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097095) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (46496941/33554432) }, upper := { exponent := 0, mantissa := (185/128) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194251/4194190) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf301InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf301LocalValidity :
    LeafFacts leaf301Box leaf301Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf301Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097095) }) = true
      norm_num [leaf301Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf301CertificateValid :
    WideCertificateValid leaf301Box leaf301Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi49ValidityFacts
    leaf301LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf301CoverageChecked :
    coverageCheck (innerAD leaf301Box) leaf301InnerLog = true := by
  rfl'

private theorem leaf301InnerLogValid :
    leaf301InnerLog.Valid 8 (innerAD leaf301Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf301CoverageChecked

private noncomputable def leaf301InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf301InputLogOnePlusV_eq :
    leaf301InputLogOnePlusV = outerEnclosure 24
      (leaf301Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf301RoundedFacts : LeafRoundedFacts 8
    leaf301Certificate.logOnePlusV leaf301InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf301InputLogOnePlusV_eq }

private noncomputable def leaf301Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi49InputQChi innerPair27Input
    leaf301InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf301LowerChecked :
    lowerCheck 24 leaf301Box leaf301Inputs = true := by
  rfl'

private theorem leaf301CoversExact : CoversExact 8
    leaf301Box leaf301Certificate leaf301InnerLog leaf301Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi49RoundedFacts
    innerPair27RoundedFacts leaf301RoundedFacts (by rfl)

private theorem leaf301FlatSound : Sound leaf301Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf301CertificateValid
    leaf301InnerLogValid leaf301CoversExact leaf301LowerChecked

private noncomputable def leaf302Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (5/16), chiHi := (11/32) }

private noncomputable def leaf302Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554493/33554432) }, vSqrt := { lower := (65533/65536), upper := (2097156/2097097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (45972685/33554432) }, upper := { exponent := 0, mantissa := (183/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi48LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4194253/4194194) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf302InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf302LocalValidity :
    LeafFacts leaf302Box leaf302Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf302Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2097156/2097097) }) = true
      norm_num [leaf302Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf302CertificateValid :
    WideCertificateValid leaf302Box leaf302Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi48ValidityFacts
    leaf302LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf302CoverageChecked :
    coverageCheck (innerAD leaf302Box) leaf302InnerLog = true := by
  rfl'

private theorem leaf302InnerLogValid :
    leaf302InnerLog.Valid 8 (innerAD leaf302Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf302CoverageChecked

private noncomputable def leaf302InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf302InputLogOnePlusV_eq :
    leaf302InputLogOnePlusV = outerEnclosure 24
      (leaf302Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf302RoundedFacts : LeafRoundedFacts 8
    leaf302Certificate.logOnePlusV leaf302InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf302InputLogOnePlusV_eq }

private noncomputable def leaf302Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi48InputQChi innerPair22Input
    leaf302InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf302LowerChecked :
    lowerCheck 24 leaf302Box leaf302Inputs = true := by
  rfl'

private theorem leaf302CoversExact : CoversExact 8
    leaf302Box leaf302Certificate leaf302InnerLog leaf302Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi48RoundedFacts
    innerPair22RoundedFacts leaf302RoundedFacts (by rfl)

private theorem leaf302FlatSound : Sound leaf302Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf302CertificateValid
    leaf302InnerLogValid leaf302CoversExact leaf302LowerChecked

private noncomputable def leaf303Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (11/32), chiHi := (3/8) }

private noncomputable def leaf303Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554495/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358755328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (47217791/33554432) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi49LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68718034943/68717510656) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf303InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf303LocalValidity :
    LeafFacts leaf303Box leaf303Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf303Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358755328) }) = true
      norm_num [leaf303Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf303CertificateValid :
    WideCertificateValid leaf303Box leaf303Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi49ValidityFacts
    leaf303LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf303CoverageChecked :
    coverageCheck (innerAD leaf303Box) leaf303InnerLog = true := by
  rfl'

private theorem leaf303InnerLogValid :
    leaf303InnerLog.Valid 8 (innerAD leaf303Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf303CoverageChecked

private noncomputable def leaf303InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf303InputLogOnePlusV_eq :
    leaf303InputLogOnePlusV = outerEnclosure 24
      (leaf303Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf303RoundedFacts : LeafRoundedFacts 8
    leaf303Certificate.logOnePlusV leaf303InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf303InputLogOnePlusV_eq }

private noncomputable def leaf303Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi49InputQChi innerPair27Input
    leaf303InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf303LowerChecked :
    lowerCheck 24 leaf303Box leaf303Inputs = true := by
  rfl'

private theorem leaf303CoversExact : CoversExact 8
    leaf303Box leaf303Certificate leaf303InnerLog leaf303Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi49RoundedFacts
    innerPair27RoundedFacts leaf303RoundedFacts (by rfl)

private theorem leaf303FlatSound : Sound leaf303Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf303CertificateValid
    leaf303InnerLogValid leaf303CoversExact leaf303LowerChecked

private noncomputable def leaf304Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (3/8), chiHi := (7/16) }

private noncomputable def leaf304Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777263/16777216) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194185) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (23035475/16777216) }, upper := { exponent := 0, mantissa := (375/256) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi17LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388497/8388370) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf304InnerLog : WideLogData :=
  innerPair134Data

set_option maxRecDepth 1000000 in
private theorem leaf304LocalValidity :
    LeafFacts leaf304Box leaf304Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf304Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194185) }) = true
      norm_num [leaf304Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf304CertificateValid :
    WideCertificateValid leaf304Box leaf304Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi17ValidityFacts
    leaf304LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf304CoverageChecked :
    coverageCheck (innerAD leaf304Box) leaf304InnerLog = true := by
  rfl'

private theorem leaf304InnerLogValid :
    leaf304InnerLog.Valid 8 (innerAD leaf304Box) :=
  wideLogDataValid_of_cachedCheck endpoint30PositiveFacts
    endpoint42PositiveFacts.valid leaf304CoverageChecked

private noncomputable def leaf304InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf304InputLogOnePlusV_eq :
    leaf304InputLogOnePlusV = outerEnclosure 24
      (leaf304Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf304RoundedFacts : LeafRoundedFacts 8
    leaf304Certificate.logOnePlusV leaf304InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf304InputLogOnePlusV_eq }

private noncomputable def leaf304Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi17InputQChi innerPair134Input
    leaf304InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf304LowerChecked :
    lowerCheck 24 leaf304Box leaf304Inputs = true := by
  rfl'

private theorem leaf304CoversExact : CoversExact 8
    leaf304Box leaf304Certificate leaf304InnerLog leaf304Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi17RoundedFacts
    innerPair134RoundedFacts leaf304RoundedFacts (by rfl)

private theorem leaf304FlatSound : Sound leaf304Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf304CertificateValid
    leaf304InnerLogValid leaf304CoversExact leaf304LowerChecked

private noncomputable def leaf305Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (3/8), chiHi := (13/32) }

private noncomputable def leaf305Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554493/33554432) }, vSqrt := { lower := (65533/65536), upper := (4194312/4194187) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (46890133/33554432) }, upper := { exponent := 0, mantissa := (373/256) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi50LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (8388499/8388374) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf305InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf305LocalValidity :
    LeafFacts leaf305Box leaf305Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf305Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (4194312/4194187) }) = true
      norm_num [leaf305Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf305CertificateValid :
    WideCertificateValid leaf305Box leaf305Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi50ValidityFacts
    leaf305LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf305CoverageChecked :
    coverageCheck (innerAD leaf305Box) leaf305InnerLog = true := by
  rfl'

private theorem leaf305InnerLogValid :
    leaf305InnerLog.Valid 8 (innerAD leaf305Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf305CoverageChecked

private noncomputable def leaf305InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629331/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf305InputLogOnePlusV_eq :
    leaf305InputLogOnePlusV = outerEnclosure 24
      (leaf305Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf305RoundedFacts : LeafRoundedFacts 8
    leaf305Certificate.logOnePlusV leaf305InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf305InputLogOnePlusV_eq }

private noncomputable def leaf305Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi50InputQChi innerPair27Input
    leaf305InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf305LowerChecked :
    lowerCheck 24 leaf305Box leaf305Inputs = true := by
  rfl'

private theorem leaf305CoversExact : CoversExact 8
    leaf305Box leaf305Certificate leaf305InnerLog leaf305Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi50RoundedFacts
    innerPair27RoundedFacts leaf305RoundedFacts (by rfl)

private theorem leaf305FlatSound : Sound leaf305Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf305CertificateValid
    leaf305InnerLogValid leaf305CoversExact leaf305LowerChecked

private noncomputable def leaf306Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf306Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554495/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358706176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (48004175/33554432) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717985791/68717412352) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf306InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf306LocalValidity :
    LeafFacts leaf306Box leaf306Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf306Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358706176) }) = true
      norm_num [leaf306Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf306CertificateValid :
    WideCertificateValid leaf306Box leaf306Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi51ValidityFacts
    leaf306LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf306CoverageChecked :
    coverageCheck (innerAD leaf306Box) leaf306InnerLog = true := by
  rfl'

private theorem leaf306InnerLogValid :
    leaf306InnerLog.Valid 8 (innerAD leaf306Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf306CoverageChecked

private noncomputable def leaf306InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf306InputLogOnePlusV_eq :
    leaf306InputLogOnePlusV = outerEnclosure 24
      (leaf306Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf306RoundedFacts : LeafRoundedFacts 8
    leaf306Certificate.logOnePlusV leaf306InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf306InputLogOnePlusV_eq }

private noncomputable def leaf306Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi51InputQChi innerPair27Input
    leaf306InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf306LowerChecked :
    lowerCheck 24 leaf306Box leaf306Inputs = true := by
  rfl'

private theorem leaf306CoversExact : CoversExact 8
    leaf306Box leaf306Certificate leaf306InnerLog leaf306Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi51RoundedFacts
    innerPair27RoundedFacts leaf306RoundedFacts (by rfl)

private theorem leaf306FlatSound : Sound leaf306Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf306CertificateValid
    leaf306InnerLogValid leaf306CoversExact leaf306LowerChecked

private noncomputable def leaf307Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (7/16), chiHi := (1/2) }

private noncomputable def leaf307Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777265/16777216) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452874752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (24083985/16777216) }, upper := { exponent := 0, mantissa := (49/32) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi18LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905967957/22905749504) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf307InnerLog : WideLogData :=
  innerPair28Data

set_option maxRecDepth 1000000 in
private theorem leaf307LocalValidity :
    LeafFacts leaf307Box leaf307Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf307Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452874752) }) = true
      norm_num [leaf307Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf307CertificateValid :
    WideCertificateValid leaf307Box leaf307Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi18ValidityFacts
    leaf307LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf307CoverageChecked :
    coverageCheck (innerAD leaf307Box) leaf307InnerLog = true := by
  rfl'

private theorem leaf307InnerLogValid :
    leaf307InnerLog.Valid 8 (innerAD leaf307Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint13PositiveFacts.valid leaf307CoverageChecked

private noncomputable def leaf307InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf307InputLogOnePlusV_eq :
    leaf307InputLogOnePlusV = outerEnclosure 24
      (leaf307Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf307RoundedFacts : LeafRoundedFacts 8
    leaf307Certificate.logOnePlusV leaf307InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf307InputLogOnePlusV_eq }

private noncomputable def leaf307Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi18InputQChi innerPair28Input
    leaf307InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf307LowerChecked :
    lowerCheck 24 leaf307Box leaf307Inputs = true := by
  rfl'

private theorem leaf307CoversExact : CoversExact 8
    leaf307Box leaf307Certificate leaf307InnerLog leaf307Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi18RoundedFacts
    innerPair28RoundedFacts leaf307RoundedFacts (by rfl)

private theorem leaf307FlatSound : Sound leaf307Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf307CertificateValid
    leaf307InnerLogValid leaf307CoversExact leaf307LowerChecked

private noncomputable def leaf308Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (7/16), chiHi := (1/2) }

private noncomputable def leaf308Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777267/16777216) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871711744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (24542707/16777216) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi18LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743567667/13743423488) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf308InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf308LocalValidity :
    LeafFacts leaf308Box leaf308Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf308Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871711744) }) = true
      norm_num [leaf308Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf308CertificateValid :
    WideCertificateValid leaf308Box leaf308Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi18ValidityFacts
    leaf308LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf308CoverageChecked :
    coverageCheck (innerAD leaf308Box) leaf308InnerLog = true := by
  rfl'

private theorem leaf308InnerLogValid :
    leaf308InnerLog.Valid 8 (innerAD leaf308Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf308CoverageChecked

private noncomputable def leaf308InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf308InputLogOnePlusV_eq :
    leaf308InputLogOnePlusV = outerEnclosure 24
      (leaf308Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf308RoundedFacts : LeafRoundedFacts 8
    leaf308Certificate.logOnePlusV leaf308InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf308InputLogOnePlusV_eq }

private noncomputable def leaf308Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi18InputQChi innerPair35Input
    leaf308InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf308LowerChecked :
    lowerCheck 24 leaf308Box leaf308Inputs = true := by
  rfl'

private theorem leaf308CoversExact : CoversExact 8
    leaf308Box leaf308Certificate leaf308InnerLog leaf308Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi18RoundedFacts
    innerPair35RoundedFacts leaf308RoundedFacts (by rfl)

private theorem leaf308FlatSound : Sound leaf308Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf308CertificateValid
    leaf308InnerLogValid leaf308CoversExact leaf308LowerChecked

private noncomputable def leaf309Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (3/8), chiHi := (13/32) }

private noncomputable def leaf309Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554495/33554432) }, vSqrt := { lower := (65533/65536), upper := (2021134095/2021101568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (47676515/33554432) }, upper := { exponent := 0, mantissa := (759/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi50LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4042235663/4042203136) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf309InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf309LocalValidity :
    LeafFacts leaf309Box leaf309Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf309Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2021134095/2021101568) }) = true
      norm_num [leaf309Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf309CertificateValid :
    WideCertificateValid leaf309Box leaf309Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi50ValidityFacts
    leaf309LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf309CoverageChecked :
    coverageCheck (innerAD leaf309Box) leaf309InnerLog = true := by
  rfl'

private theorem leaf309InnerLogValid :
    leaf309InnerLog.Valid 8 (innerAD leaf309Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf309CoverageChecked

private noncomputable def leaf309InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf309InputLogOnePlusV_eq :
    leaf309InputLogOnePlusV = outerEnclosure 24
      (leaf309Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf309RoundedFacts : LeafRoundedFacts 8
    leaf309Certificate.logOnePlusV leaf309InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf309InputLogOnePlusV_eq }

private noncomputable def leaf309Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi50InputQChi innerPair27Input
    leaf309InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf309LowerChecked :
    lowerCheck 24 leaf309Box leaf309Inputs = true := by
  rfl'

private theorem leaf309CoversExact : CoversExact 8
    leaf309Box leaf309Certificate leaf309InnerLog leaf309Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi50RoundedFacts
    innerPair27RoundedFacts leaf309RoundedFacts (by rfl)

private theorem leaf309FlatSound : Sound leaf309Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf309CertificateValid
    leaf309InnerLogValid leaf309CoversExact leaf309LowerChecked

private noncomputable def leaf310Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf310Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554497/33554432) }, vSqrt := { lower := (65533/65536), upper := (3817697735/3817627648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (48856089/33554432) }, upper := { exponent := 0, mantissa := (389/256) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (7635325383/7635255296) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf310InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf310LocalValidity :
    LeafFacts leaf310Box leaf310Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf310Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (3817697735/3817627648) }) = true
      norm_num [leaf310Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf310CertificateValid :
    WideCertificateValid leaf310Box leaf310Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi51ValidityFacts
    leaf310LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf310CoverageChecked :
    coverageCheck (innerAD leaf310Box) leaf310InnerLog = true := by
  rfl'

private theorem leaf310InnerLogValid :
    leaf310InnerLog.Valid 8 (innerAD leaf310Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf310CoverageChecked

private noncomputable def leaf310InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf310InputLogOnePlusV_eq :
    leaf310InputLogOnePlusV = outerEnclosure 24
      (leaf310Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf310RoundedFacts : LeafRoundedFacts 8
    leaf310Certificate.logOnePlusV leaf310InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf310InputLogOnePlusV_eq }

private noncomputable def leaf310Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi51InputQChi innerPair35Input
    leaf310InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf310LowerChecked :
    lowerCheck 24 leaf310Box leaf310Inputs = true := by
  rfl'

private theorem leaf310CoversExact : CoversExact 8
    leaf310Box leaf310Certificate leaf310InnerLog leaf310Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi51RoundedFacts
    innerPair35RoundedFacts leaf310RoundedFacts (by rfl)

private theorem leaf310FlatSound : Sound leaf310Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf310CertificateValid
    leaf310InnerLogValid leaf310CoversExact leaf310LowerChecked

private noncomputable def leaf311Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (3/8), chiHi := (13/32) }

private noncomputable def leaf311Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554497/33554432) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452891136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (48462897/33554432) }, upper := { exponent := 0, mantissa := (193/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi50LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905984341/22905782272) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf311InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf311LocalValidity :
    LeafFacts leaf311Box leaf311Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf311Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452891136) }) = true
      norm_num [leaf311Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf311CertificateValid :
    WideCertificateValid leaf311Box leaf311Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi50ValidityFacts
    leaf311LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf311CoverageChecked :
    coverageCheck (innerAD leaf311Box) leaf311InnerLog = true := by
  rfl'

private theorem leaf311InnerLogValid :
    leaf311InnerLog.Valid 8 (innerAD leaf311Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf311CoverageChecked

private noncomputable def leaf311InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf311InputLogOnePlusV_eq :
    leaf311InputLogOnePlusV = outerEnclosure 24
      (leaf311Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf311RoundedFacts : LeafRoundedFacts 8
    leaf311Certificate.logOnePlusV leaf311InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf311InputLogOnePlusV_eq }

private noncomputable def leaf311Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi50InputQChi innerPair35Input
    leaf311InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf311LowerChecked :
    lowerCheck 24 leaf311Box leaf311Inputs = true := by
  rfl'

private theorem leaf311CoversExact : CoversExact 8
    leaf311Box leaf311Certificate leaf311InnerLog leaf311Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi50RoundedFacts
    innerPair35RoundedFacts leaf311RoundedFacts (by rfl)

private theorem leaf311FlatSound : Sound leaf311Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf311CertificateValid
    leaf311InnerLogValid leaf311CoversExact leaf311LowerChecked

private noncomputable def leaf312Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (13/32), chiHi := (7/16) }

private noncomputable def leaf312Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554499/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358591488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (49708003/33554432) }, upper := { exponent := 0, mantissa := (99/64) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi51LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717871103/68717182976) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf312InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf312LocalValidity :
    LeafFacts leaf312Box leaf312Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf312Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358591488) }) = true
      norm_num [leaf312Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf312CertificateValid :
    WideCertificateValid leaf312Box leaf312Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi51ValidityFacts
    leaf312LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf312CoverageChecked :
    coverageCheck (innerAD leaf312Box) leaf312InnerLog = true := by
  rfl'

private theorem leaf312InnerLogValid :
    leaf312InnerLog.Valid 8 (innerAD leaf312Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf312CoverageChecked

private noncomputable def leaf312InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf312InputLogOnePlusV_eq :
    leaf312InputLogOnePlusV = outerEnclosure 24
      (leaf312Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf312RoundedFacts : LeafRoundedFacts 8
    leaf312Certificate.logOnePlusV leaf312InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf312InputLogOnePlusV_eq }

private noncomputable def leaf312Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi51InputQChi innerPair35Input
    leaf312InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf312LowerChecked :
    lowerCheck 24 leaf312Box leaf312Inputs = true := by
  rfl'

private theorem leaf312CoversExact : CoversExact 8
    leaf312Box leaf312Certificate leaf312InnerLog leaf312Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi51RoundedFacts
    innerPair35RoundedFacts leaf312RoundedFacts (by rfl)

private theorem leaf312FlatSound : Sound leaf312Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf312CertificateValid
    leaf312InnerLogValid leaf312CoversExact leaf312LowerChecked

private noncomputable def leaf313Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf313Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554499/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358571008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (50035663/33554432) }, upper := { exponent := 0, mantissa := (797/512) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717850623/68717142016) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf313InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf313LocalValidity :
    LeafFacts leaf313Box leaf313Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf313Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358571008) }) = true
      norm_num [leaf313Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf313CertificateValid :
    WideCertificateValid leaf313Box leaf313Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi52ValidityFacts
    leaf313LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf313CoverageChecked :
    coverageCheck (innerAD leaf313Box) leaf313InnerLog = true := by
  rfl'

private theorem leaf313InnerLogValid :
    leaf313InnerLog.Valid 8 (innerAD leaf313Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf313CoverageChecked

private noncomputable def leaf313InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf313InputLogOnePlusV_eq :
    leaf313InputLogOnePlusV = outerEnclosure 24
      (leaf313Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf313RoundedFacts : LeafRoundedFacts 8
    leaf313Certificate.logOnePlusV leaf313InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf313InputLogOnePlusV_eq }

private noncomputable def leaf313Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi52InputQChi innerPair35Input
    leaf313InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf313LowerChecked :
    lowerCheck 24 leaf313Box leaf313Inputs = true := by
  rfl'

private theorem leaf313CoversExact : CoversExact 8
    leaf313Box leaf313Certificate leaf313InnerLog leaf313Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi52RoundedFacts
    innerPair35RoundedFacts leaf313RoundedFacts (by rfl)

private theorem leaf313FlatSound : Sound leaf313Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf313CertificateValid
    leaf313InnerLogValid leaf313CoversExact leaf313LowerChecked

private noncomputable def leaf314Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf314Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554501/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358493184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (51215237/33554432) }, upper := { exponent := 0, mantissa := (51/32) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717772799/68716986368) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf314InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf314LocalValidity :
    LeafFacts leaf314Box leaf314Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf314Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358493184) }) = true
      norm_num [leaf314Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf314CertificateValid :
    WideCertificateValid leaf314Box leaf314Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi53ValidityFacts
    leaf314LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf314CoverageChecked :
    coverageCheck (innerAD leaf314Box) leaf314InnerLog = true := by
  rfl'

private theorem leaf314InnerLogValid :
    leaf314InnerLog.Valid 8 (innerAD leaf314Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf314CoverageChecked

private noncomputable def leaf314InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf314InputLogOnePlusV_eq :
    leaf314InputLogOnePlusV = outerEnclosure 24
      (leaf314Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf314RoundedFacts : LeafRoundedFacts 8
    leaf314Certificate.logOnePlusV leaf314InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf314InputLogOnePlusV_eq }

private noncomputable def leaf314Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi53InputQChi innerPair41Input
    leaf314InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf314LowerChecked :
    lowerCheck 24 leaf314Box leaf314Inputs = true := by
  rfl'

private theorem leaf314CoversExact : CoversExact 8
    leaf314Box leaf314Certificate leaf314InnerLog leaf314Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi53RoundedFacts
    innerPair41RoundedFacts leaf314RoundedFacts (by rfl)

private theorem leaf314FlatSound : Sound leaf314Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf314CertificateValid
    leaf314InnerLogValid leaf314CoversExact leaf314LowerChecked

private noncomputable def leaf315Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (7/16), chiHi := (15/32) }

private noncomputable def leaf315Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554501/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358509568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (50953109/33554432) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi52LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717789183/68717019136) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf315InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf315LocalValidity :
    LeafFacts leaf315Box leaf315Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf315Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358509568) }) = true
      norm_num [leaf315Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf315CertificateValid :
    WideCertificateValid leaf315Box leaf315Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi52ValidityFacts
    leaf315LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf315CoverageChecked :
    coverageCheck (innerAD leaf315Box) leaf315InnerLog = true := by
  rfl'

private theorem leaf315InnerLogValid :
    leaf315InnerLog.Valid 8 (innerAD leaf315Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf315CoverageChecked

private noncomputable def leaf315InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf315InputLogOnePlusV_eq :
    leaf315InputLogOnePlusV = outerEnclosure 24
      (leaf315Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf315RoundedFacts : LeafRoundedFacts 8
    leaf315Certificate.logOnePlusV leaf315InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf315InputLogOnePlusV_eq }

private noncomputable def leaf315Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi52InputQChi innerPair41Input
    leaf315InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf315LowerChecked :
    lowerCheck 24 leaf315Box leaf315Inputs = true := by
  rfl'

private theorem leaf315CoversExact : CoversExact 8
    leaf315Box leaf315Certificate leaf315InnerLog leaf315Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi52RoundedFacts
    innerPair41RoundedFacts leaf315RoundedFacts (by rfl)

private theorem leaf315FlatSound : Sound leaf315Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf315CertificateValid
    leaf315InnerLogValid leaf315CoversExact leaf315LowerChecked

private noncomputable def leaf316Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (15/32), chiHi := (1/2) }

private noncomputable def leaf316Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554503/33554432) }, vSqrt := { lower := (65533/65536), upper := (3817697735/3817603072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (52198215/33554432) }, upper := { exponent := 0, mantissa := (13/8) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi53LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (7635300807/7635206144) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf316InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf316LocalValidity :
    LeafFacts leaf316Box leaf316Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf316Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (3817697735/3817603072) }) = true
      norm_num [leaf316Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf316CertificateValid :
    WideCertificateValid leaf316Box leaf316Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi53ValidityFacts
    leaf316LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf316CoverageChecked :
    coverageCheck (innerAD leaf316Box) leaf316InnerLog = true := by
  rfl'

private theorem leaf316InnerLogValid :
    leaf316InnerLog.Valid 8 (innerAD leaf316Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf316CoverageChecked

private noncomputable def leaf316InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf316InputLogOnePlusV_eq :
    leaf316InputLogOnePlusV = outerEnclosure 24
      (leaf316Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf316RoundedFacts : LeafRoundedFacts 8
    leaf316Certificate.logOnePlusV leaf316InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf316InputLogOnePlusV_eq }

private noncomputable def leaf316Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi53InputQChi innerPair41Input
    leaf316InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf316LowerChecked :
    lowerCheck 24 leaf316Box leaf316Inputs = true := by
  rfl'

private theorem leaf316CoversExact : CoversExact 8
    leaf316Box leaf316Certificate leaf316InnerLog leaf316Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi53RoundedFacts
    innerPair41RoundedFacts leaf316RoundedFacts (by rfl)

private theorem leaf316FlatSound : Sound leaf316Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf316CertificateValid
    leaf316InnerLogValid leaf316CoversExact leaf316LowerChecked

private noncomputable def component7Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node0_sound : Sound component7Node0Box :=
  sound_of_literal_split component7Node0Box leaf288Box leaf289Box
    .chi (9/32) (by rfl) (by rfl)
    leaf288FlatSound leaf289FlatSound

private noncomputable def component7Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node1_sound : Sound component7Node1Box :=
  sound_of_literal_split component7Node1Box leaf290Box leaf291Box
    .chi (9/32) (by rfl) (by rfl)
    leaf290FlatSound leaf291FlatSound

private noncomputable def component7Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node2_sound : Sound component7Node2Box :=
  sound_of_literal_split component7Node2Box component7Node0Box component7Node1Box
    .k (17/16) (by rfl) (by rfl)
    component7Node0_sound component7Node1_sound

private noncomputable def component7Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node3_sound : Sound component7Node3Box :=
  sound_of_literal_split component7Node3Box leaf292Box leaf293Box
    .chi (11/32) (by rfl) (by rfl)
    leaf292FlatSound leaf293FlatSound

private noncomputable def component7Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node4_sound : Sound component7Node4Box :=
  sound_of_literal_split component7Node4Box leaf294Box leaf295Box
    .chi (11/32) (by rfl) (by rfl)
    leaf294FlatSound leaf295FlatSound

private noncomputable def component7Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node5_sound : Sound component7Node5Box :=
  sound_of_literal_split component7Node5Box component7Node3Box component7Node4Box
    .k (17/16) (by rfl) (by rfl)
    component7Node3_sound component7Node4_sound

private noncomputable def component7Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node6_sound : Sound component7Node6Box :=
  sound_of_literal_split component7Node6Box component7Node2Box component7Node5Box
    .chi (5/16) (by rfl) (by rfl)
    component7Node2_sound component7Node5_sound

private noncomputable def component7Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node7_sound : Sound component7Node7Box :=
  sound_of_literal_split component7Node7Box leaf296Box leaf297Box
    .chi (9/32) (by rfl) (by rfl)
    leaf296FlatSound leaf297FlatSound

private noncomputable def component7Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node8_sound : Sound component7Node8Box :=
  sound_of_literal_split component7Node8Box leaf298Box leaf299Box
    .chi (9/32) (by rfl) (by rfl)
    leaf298FlatSound leaf299FlatSound

private noncomputable def component7Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node9_sound : Sound component7Node9Box :=
  sound_of_literal_split component7Node9Box component7Node7Box component7Node8Box
    .k (19/16) (by rfl) (by rfl)
    component7Node7_sound component7Node8_sound

private noncomputable def component7Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node10_sound : Sound component7Node10Box :=
  sound_of_literal_split component7Node10Box leaf300Box leaf301Box
    .chi (11/32) (by rfl) (by rfl)
    leaf300FlatSound leaf301FlatSound

private noncomputable def component7Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node11_sound : Sound component7Node11Box :=
  sound_of_literal_split component7Node11Box leaf302Box leaf303Box
    .chi (11/32) (by rfl) (by rfl)
    leaf302FlatSound leaf303FlatSound

private noncomputable def component7Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node12_sound : Sound component7Node12Box :=
  sound_of_literal_split component7Node12Box component7Node10Box component7Node11Box
    .k (19/16) (by rfl) (by rfl)
    component7Node10_sound component7Node11_sound

private noncomputable def component7Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node13_sound : Sound component7Node13Box :=
  sound_of_literal_split component7Node13Box component7Node9Box component7Node12Box
    .chi (5/16) (by rfl) (by rfl)
    component7Node9_sound component7Node12_sound

private noncomputable def component7Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component7Node14_sound : Sound component7Node14Box :=
  sound_of_literal_split component7Node14Box component7Node6Box component7Node13Box
    .k (9/8) (by rfl) (by rfl)
    component7Node6_sound component7Node13_sound

private noncomputable def component7Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node15_sound : Sound component7Node15Box :=
  sound_of_literal_split component7Node15Box leaf305Box leaf306Box
    .chi (13/32) (by rfl) (by rfl)
    leaf305FlatSound leaf306FlatSound

private noncomputable def component7Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node16_sound : Sound component7Node16Box :=
  sound_of_literal_split component7Node16Box leaf304Box component7Node15Box
    .k (17/16) (by rfl) (by rfl)
    leaf304FlatSound component7Node15_sound

private noncomputable def component7Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component7Node17_sound : Sound component7Node17Box :=
  sound_of_literal_split component7Node17Box leaf307Box leaf308Box
    .k (17/16) (by rfl) (by rfl)
    leaf307FlatSound leaf308FlatSound

private noncomputable def component7Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component7Node18_sound : Sound component7Node18Box :=
  sound_of_literal_split component7Node18Box component7Node16Box component7Node17Box
    .chi (7/16) (by rfl) (by rfl)
    component7Node16_sound component7Node17_sound

private noncomputable def component7Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node19_sound : Sound component7Node19Box :=
  sound_of_literal_split component7Node19Box leaf309Box leaf310Box
    .chi (13/32) (by rfl) (by rfl)
    leaf309FlatSound leaf310FlatSound

private noncomputable def component7Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node20_sound : Sound component7Node20Box :=
  sound_of_literal_split component7Node20Box leaf311Box leaf312Box
    .chi (13/32) (by rfl) (by rfl)
    leaf311FlatSound leaf312FlatSound

private noncomputable def component7Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem component7Node21_sound : Sound component7Node21Box :=
  sound_of_literal_split component7Node21Box component7Node19Box component7Node20Box
    .k (19/16) (by rfl) (by rfl)
    component7Node19_sound component7Node20_sound

private noncomputable def component7Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component7Node22_sound : Sound component7Node22Box :=
  sound_of_literal_split component7Node22Box leaf313Box leaf314Box
    .chi (15/32) (by rfl) (by rfl)
    leaf313FlatSound leaf314FlatSound

private noncomputable def component7Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component7Node23_sound : Sound component7Node23Box :=
  sound_of_literal_split component7Node23Box leaf315Box leaf316Box
    .chi (15/32) (by rfl) (by rfl)
    leaf315FlatSound leaf316FlatSound

private noncomputable def component7Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component7Node24_sound : Sound component7Node24Box :=
  sound_of_literal_split component7Node24Box component7Node22Box component7Node23Box
    .k (19/16) (by rfl) (by rfl)
    component7Node22_sound component7Node23_sound

private noncomputable def component7Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component7Node25_sound : Sound component7Node25Box :=
  sound_of_literal_split component7Node25Box component7Node21Box component7Node24Box
    .chi (7/16) (by rfl) (by rfl)
    component7Node21_sound component7Node24_sound

private noncomputable def component7Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem component7Node26_sound : Sound component7Node26Box :=
  sound_of_literal_split component7Node26Box component7Node18Box component7Node25Box
    .k (9/8) (by rfl) (by rfl)
    component7Node18_sound component7Node25_sound

noncomputable def component7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem component7_sound : Sound component7Box :=
  sound_of_literal_split component7Box component7Node14Box component7Node26Box
    .chi (3/8) (by rfl) (by rfl)
    component7Node14_sound component7Node26_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
