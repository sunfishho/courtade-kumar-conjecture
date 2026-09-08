import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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

private noncomputable def leaf716Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (0), chiHi := (1/64) }

private noncomputable def leaf716Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554471/33554432) }, vSqrt := { lower := (65531/65536), upper := (8388640/8388589) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (33521627/16777216) }, upper := { exponent := 0, mantissa := (531/512) } }, logOuter := sk65LogOuterCertificate, logK := sk65LogKCertificate, logChi := chi100LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777229/16777178) } }, logDArg := sk65LogDArgCertificate }

private noncomputable def leaf716InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf716LocalValidity :
    LeafFacts leaf716Box leaf716Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf716Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388640/8388589) }) = true
      norm_num [leaf716Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf716CertificateValid :
    WideCertificateValid leaf716Box leaf716Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk65ValidityFacts chi100ValidityFacts
    leaf716LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf716CoverageChecked :
    coverageCheck (innerAD leaf716Box) leaf716InnerLog = true := by
  rfl'

private theorem leaf716InnerLogValid :
    leaf716InnerLog.Valid 8 (innerAD leaf716Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf716CoverageChecked

private noncomputable def leaf716InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907283/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf716InputLogOnePlusV_eq :
    leaf716InputLogOnePlusV = outerEnclosure 24
      (leaf716Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf716RoundedFacts : LeafRoundedFacts 8
    leaf716Certificate.logOnePlusV leaf716InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf716InputLogOnePlusV_eq }

private noncomputable def leaf716Inputs : Inputs :=
  inputsOfCaches globalInput sk65RoundedInputs
    chi100InputQChi innerPair1Input
    leaf716InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf716LowerChecked :
    lowerCheck 24 leaf716Box leaf716Inputs = true := by
  rfl'

private theorem leaf716CoversExact : CoversExact 8
    leaf716Box leaf716Certificate leaf716InnerLog leaf716Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk65RoundedFacts chi100RoundedFacts
    innerPair1RoundedFacts leaf716RoundedFacts (by rfl)

private theorem leaf716FlatSound : Sound leaf716Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf716CertificateValid
    leaf716InnerLogValid leaf716CoversExact leaf716LowerChecked

private noncomputable def leaf717Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (0), chiHi := (1/64) }

private noncomputable def leaf717Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554473/33554432) }, vSqrt := { lower := (32765/32768), upper := (161320/161319) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (33521625/16777216) }, upper := { exponent := 0, mantissa := (133/128) } }, logOuter := sk66LogOuterCertificate, logK := sk66LogKCertificate, logChi := chi100LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (322639/322638) } }, logDArg := sk66LogDArgCertificate }

private noncomputable def leaf717InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf717LocalValidity :
    LeafFacts leaf717Box leaf717Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf717Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (161320/161319) }) = true
      norm_num [leaf717Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf717CertificateValid :
    WideCertificateValid leaf717Box leaf717Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk66ValidityFacts chi100ValidityFacts
    leaf717LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf717CoverageChecked :
    coverageCheck (innerAD leaf717Box) leaf717InnerLog = true := by
  rfl'

private theorem leaf717InnerLogValid :
    leaf717InnerLog.Valid 8 (innerAD leaf717Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf717CoverageChecked

private noncomputable def leaf717InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629133/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf717InputLogOnePlusV_eq :
    leaf717InputLogOnePlusV = outerEnclosure 24
      (leaf717Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf717RoundedFacts : LeafRoundedFacts 8
    leaf717Certificate.logOnePlusV leaf717InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf717InputLogOnePlusV_eq }

private noncomputable def leaf717Inputs : Inputs :=
  inputsOfCaches globalInput sk66RoundedInputs
    chi100InputQChi innerPair1Input
    leaf717InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf717LowerChecked :
    lowerCheck 24 leaf717Box leaf717Inputs = true := by
  rfl'

private theorem leaf717CoversExact : CoversExact 8
    leaf717Box leaf717Certificate leaf717InnerLog leaf717Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk66RoundedFacts chi100RoundedFacts
    innerPair1RoundedFacts leaf717RoundedFacts (by rfl)

private theorem leaf717FlatSound : Sound leaf717Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf717CertificateValid
    leaf717InnerLogValid leaf717CoversExact leaf717LowerChecked

private noncomputable def leaf718Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf718Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108907/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777280/16777159) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (69435207/67108864) }, upper := { exponent := 0, mantissa := (1081/1024) } }, logOuter := sk65LogOuterCertificate, logK := sk65LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554439/33554318) } }, logDArg := sk65LogDArgCertificate }

private noncomputable def leaf718InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf718LocalValidity :
    LeafFacts leaf718Box leaf718Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf718Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777280/16777159) }) = true
      norm_num [leaf718Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf718CertificateValid :
    WideCertificateValid leaf718Box leaf718Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk65ValidityFacts chi101ValidityFacts
    leaf718LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf718CoverageChecked :
    coverageCheck (innerAD leaf718Box) leaf718InnerLog = true := by
  rfl'

private theorem leaf718InnerLogValid :
    leaf718InnerLog.Valid 8 (innerAD leaf718Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf718CoverageChecked

private noncomputable def leaf718InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629141/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf718InputLogOnePlusV_eq :
    leaf718InputLogOnePlusV = outerEnclosure 24
      (leaf718Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf718RoundedFacts : LeafRoundedFacts 8
    leaf718Certificate.logOnePlusV leaf718InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf718InputLogOnePlusV_eq }

private noncomputable def leaf718Inputs : Inputs :=
  inputsOfCaches globalInput sk65RoundedInputs
    chi101InputQChi innerPair10Input
    leaf718InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf718LowerChecked :
    lowerCheck 24 leaf718Box leaf718Inputs = true := by
  rfl'

private theorem leaf718CoversExact : CoversExact 8
    leaf718Box leaf718Certificate leaf718InnerLog leaf718Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk65RoundedFacts chi101RoundedFacts
    innerPair10RoundedFacts leaf718RoundedFacts (by rfl)

private theorem leaf718FlatSound : Sound leaf718Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf718CertificateValid
    leaf718InnerLogValid leaf718CoversExact leaf718LowerChecked

private noncomputable def leaf719Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/128), chiHi := (1/32) }

private noncomputable def leaf719Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108909/67108864) }, vSqrt := { lower := (65531/65536), upper := (838864/838857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (70614781/67108864) }, upper := { exponent := 0, mantissa := (275/256) } }, logOuter := sk65LogOuterCertificate, logK := sk65LogKCertificate, logChi := chi102LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1677721/1677714) } }, logDArg := sk65LogDArgCertificate }

private noncomputable def leaf719InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf719LocalValidity :
    LeafFacts leaf719Box leaf719Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf719Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (838864/838857) }) = true
      norm_num [leaf719Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf719CertificateValid :
    WideCertificateValid leaf719Box leaf719Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk65ValidityFacts chi102ValidityFacts
    leaf719LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf719CoverageChecked :
    coverageCheck (innerAD leaf719Box) leaf719InnerLog = true := by
  rfl'

private theorem leaf719InnerLogValid :
    leaf719InnerLog.Valid 8 (innerAD leaf719Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf719CoverageChecked

private noncomputable def leaf719InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629151/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf719InputLogOnePlusV_eq :
    leaf719InputLogOnePlusV = outerEnclosure 24
      (leaf719Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf719RoundedFacts : LeafRoundedFacts 8
    leaf719Certificate.logOnePlusV leaf719InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf719InputLogOnePlusV_eq }

private noncomputable def leaf719Inputs : Inputs :=
  inputsOfCaches globalInput sk65RoundedInputs
    chi102InputQChi innerPair9Input
    leaf719InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf719LowerChecked :
    lowerCheck 24 leaf719Box leaf719Inputs = true := by
  rfl'

private theorem leaf719CoversExact : CoversExact 8
    leaf719Box leaf719Certificate leaf719InnerLog leaf719Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk65RoundedFacts chi102RoundedFacts
    innerPair9RoundedFacts leaf719RoundedFacts (by rfl)

private theorem leaf719FlatSound : Sound leaf719Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf719CertificateValid
    leaf719InnerLogValid leaf719CoversExact leaf719LowerChecked

private noncomputable def leaf720Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf720Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108909/67108864) }, vSqrt := { lower := (32765/32768), upper := (4194320/4194289) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (69566269/67108864) }, upper := { exponent := 0, mantissa := (271/256) } }, logOuter := sk66LogOuterCertificate, logK := sk66LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388609/8388578) } }, logDArg := sk66LogDArgCertificate }

private noncomputable def leaf720InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf720LocalValidity :
    LeafFacts leaf720Box leaf720Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf720Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194320/4194289) }) = true
      norm_num [leaf720Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf720CertificateValid :
    WideCertificateValid leaf720Box leaf720Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk66ValidityFacts chi101ValidityFacts
    leaf720LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf720CoverageChecked :
    coverageCheck (innerAD leaf720Box) leaf720InnerLog = true := by
  rfl'

private theorem leaf720InnerLogValid :
    leaf720InnerLog.Valid 8 (innerAD leaf720Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf720CoverageChecked

private noncomputable def leaf720InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629143/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf720InputLogOnePlusV_eq :
    leaf720InputLogOnePlusV = outerEnclosure 24
      (leaf720Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf720RoundedFacts : LeafRoundedFacts 8
    leaf720Certificate.logOnePlusV leaf720InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf720InputLogOnePlusV_eq }

private noncomputable def leaf720Inputs : Inputs :=
  inputsOfCaches globalInput sk66RoundedInputs
    chi101InputQChi innerPair10Input
    leaf720InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf720LowerChecked :
    lowerCheck 24 leaf720Box leaf720Inputs = true := by
  rfl'

private theorem leaf720CoversExact : CoversExact 8
    leaf720Box leaf720Certificate leaf720InnerLog leaf720Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk66RoundedFacts chi101RoundedFacts
    innerPair10RoundedFacts leaf720RoundedFacts (by rfl)

private theorem leaf720FlatSound : Sound leaf720Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf720CertificateValid
    leaf720InnerLogValid leaf720CoversExact leaf720LowerChecked

private noncomputable def leaf721Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/128), chiHi := (1/32) }

private noncomputable def leaf721Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108911/67108864) }, vSqrt := { lower := (32765/32768), upper := (1048580/1048571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (70811375/67108864) }, upper := { exponent := 0, mantissa := (69/64) } }, logOuter := sk66LogOuterCertificate, logK := sk66LogKCertificate, logChi := chi102LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2097151/2097142) } }, logDArg := sk66LogDArgCertificate }

private noncomputable def leaf721InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf721LocalValidity :
    LeafFacts leaf721Box leaf721Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf721Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048580/1048571) }) = true
      norm_num [leaf721Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf721CertificateValid :
    WideCertificateValid leaf721Box leaf721Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk66ValidityFacts chi102ValidityFacts
    leaf721LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf721CoverageChecked :
    coverageCheck (innerAD leaf721Box) leaf721InnerLog = true := by
  rfl'

private theorem leaf721InnerLogValid :
    leaf721InnerLog.Valid 8 (innerAD leaf721Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf721CoverageChecked

private noncomputable def leaf721InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf721InputLogOnePlusV_eq :
    leaf721InputLogOnePlusV = outerEnclosure 24
      (leaf721Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf721RoundedFacts : LeafRoundedFacts 8
    leaf721Certificate.logOnePlusV leaf721InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf721InputLogOnePlusV_eq }

private noncomputable def leaf721Inputs : Inputs :=
  inputsOfCaches globalInput sk66RoundedInputs
    chi102InputQChi innerPair9Input
    leaf721InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf721LowerChecked :
    lowerCheck 24 leaf721Box leaf721Inputs = true := by
  rfl'

private theorem leaf721CoversExact : CoversExact 8
    leaf721Box leaf721Certificate leaf721InnerLog leaf721Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk66RoundedFacts chi102RoundedFacts
    innerPair9RoundedFacts leaf721RoundedFacts (by rfl)

private theorem leaf721FlatSound : Sound leaf721Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf721CertificateValid
    leaf721InnerLogValid leaf721CoversExact leaf721LowerChecked

private noncomputable def leaf722Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf722Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108911/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777280/16777121) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71794355/67108864) }, upper := { exponent := 0, mantissa := (1119/1024) } }, logOuter := sk65LogOuterCertificate, logK := sk65LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554401/33554242) } }, logDArg := sk65LogDArgCertificate }

private noncomputable def leaf722InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf722LocalValidity :
    LeafFacts leaf722Box leaf722Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf722Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777280/16777121) }) = true
      norm_num [leaf722Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf722CertificateValid :
    WideCertificateValid leaf722Box leaf722Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk65ValidityFacts chi38ValidityFacts
    leaf722LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf722CoverageChecked :
    coverageCheck (innerAD leaf722Box) leaf722InnerLog = true := by
  rfl'

private theorem leaf722InnerLogValid :
    leaf722InnerLog.Valid 8 (innerAD leaf722Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf722CoverageChecked

private noncomputable def leaf722InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf722InputLogOnePlusV_eq :
    leaf722InputLogOnePlusV = outerEnclosure 24
      (leaf722Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf722RoundedFacts : LeafRoundedFacts 8
    leaf722Certificate.logOnePlusV leaf722InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf722InputLogOnePlusV_eq }

private noncomputable def leaf722Inputs : Inputs :=
  inputsOfCaches globalInput sk65RoundedInputs
    chi38InputQChi innerPair5Input
    leaf722InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf722LowerChecked :
    lowerCheck 24 leaf722Box leaf722Inputs = true := by
  rfl'

private theorem leaf722CoversExact : CoversExact 8
    leaf722Box leaf722Certificate leaf722InnerLog leaf722Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk65RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf722RoundedFacts (by rfl)

private theorem leaf722FlatSound : Sound leaf722Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf722CertificateValid
    leaf722InnerLogValid leaf722CoversExact leaf722LowerChecked

private noncomputable def leaf723Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf723Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108913/67108864) }, vSqrt := { lower := (65531/65536), upper := (8388640/8388551) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72973929/67108864) }, upper := { exponent := 0, mantissa := (569/512) } }, logOuter := sk65LogOuterCertificate, logK := sk65LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777191/16777102) } }, logDArg := sk65LogDArgCertificate }

private noncomputable def leaf723InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf723LocalValidity :
    LeafFacts leaf723Box leaf723Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf723Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388640/8388551) }) = true
      norm_num [leaf723Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf723CertificateValid :
    WideCertificateValid leaf723Box leaf723Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk65ValidityFacts chi39ValidityFacts
    leaf723LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf723CoverageChecked :
    coverageCheck (innerAD leaf723Box) leaf723InnerLog = true := by
  rfl'

private theorem leaf723InnerLogValid :
    leaf723InnerLog.Valid 8 (innerAD leaf723Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf723CoverageChecked

private noncomputable def leaf723InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814585/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf723InputLogOnePlusV_eq :
    leaf723InputLogOnePlusV = outerEnclosure 24
      (leaf723Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf723RoundedFacts : LeafRoundedFacts 8
    leaf723Certificate.logOnePlusV leaf723InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf723InputLogOnePlusV_eq }

private noncomputable def leaf723Inputs : Inputs :=
  inputsOfCaches globalInput sk65RoundedInputs
    chi39InputQChi innerPair5Input
    leaf723InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf723LowerChecked :
    lowerCheck 24 leaf723Box leaf723Inputs = true := by
  rfl'

private theorem leaf723CoversExact : CoversExact 8
    leaf723Box leaf723Certificate leaf723InnerLog leaf723Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk65RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf723RoundedFacts (by rfl)

private theorem leaf723FlatSound : Sound leaf723Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf723CertificateValid
    leaf723InnerLogValid leaf723CoversExact leaf723LowerChecked

private noncomputable def leaf724Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf724Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108913/67108864) }, vSqrt := { lower := (32765/32768), upper := (4194320/4194279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72056481/67108864) }, upper := { exponent := 0, mantissa := (281/256) } }, logOuter := sk66LogOuterCertificate, logK := sk66LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388599/8388558) } }, logDArg := sk66LogDArgCertificate }

private noncomputable def leaf724InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf724LocalValidity :
    LeafFacts leaf724Box leaf724Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf724Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194320/4194279) }) = true
      norm_num [leaf724Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf724CertificateValid :
    WideCertificateValid leaf724Box leaf724Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk66ValidityFacts chi38ValidityFacts
    leaf724LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf724CoverageChecked :
    coverageCheck (innerAD leaf724Box) leaf724InnerLog = true := by
  rfl'

private theorem leaf724InnerLogValid :
    leaf724InnerLog.Valid 8 (innerAD leaf724Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf724CoverageChecked

private noncomputable def leaf724InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf724InputLogOnePlusV_eq :
    leaf724InputLogOnePlusV = outerEnclosure 24
      (leaf724Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf724RoundedFacts : LeafRoundedFacts 8
    leaf724Certificate.logOnePlusV leaf724InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf724InputLogOnePlusV_eq }

private noncomputable def leaf724Inputs : Inputs :=
  inputsOfCaches globalInput sk66RoundedInputs
    chi38InputQChi innerPair5Input
    leaf724InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf724LowerChecked :
    lowerCheck 24 leaf724Box leaf724Inputs = true := by
  rfl'

private theorem leaf724CoversExact : CoversExact 8
    leaf724Box leaf724Certificate leaf724InnerLog leaf724Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk66RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf724RoundedFacts (by rfl)

private theorem leaf724FlatSound : Sound leaf724Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf724CertificateValid
    leaf724InnerLogValid leaf724CoversExact leaf724LowerChecked

private noncomputable def leaf725Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf725Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217817/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777248/16777099) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (146635953/134217728) }, upper := { exponent := 0, mantissa := (1141/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554347/33554198) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf725InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf725LocalValidity :
    LeafFacts leaf725Box leaf725Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf725Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16777099) }) = true
      norm_num [leaf725Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf725CertificateValid :
    WideCertificateValid leaf725Box leaf725Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi39ValidityFacts
    leaf725LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf725CoverageChecked :
    coverageCheck (innerAD leaf725Box) leaf725InnerLog = true := by
  rfl'

private theorem leaf725InnerLogValid :
    leaf725InnerLog.Valid 8 (innerAD leaf725Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf725CoverageChecked

private noncomputable def leaf725InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf725InputLogOnePlusV_eq :
    leaf725InputLogOnePlusV = outerEnclosure 24
      (leaf725Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf725RoundedFacts : LeafRoundedFacts 8
    leaf725Certificate.logOnePlusV leaf725InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf725InputLogOnePlusV_eq }

private noncomputable def leaf725Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi39InputQChi innerPair5Input
    leaf725InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf725LowerChecked :
    lowerCheck 24 leaf725Box leaf725Inputs = true := by
  rfl'

private theorem leaf725CoversExact : CoversExact 8
    leaf725Box leaf725Certificate leaf725InnerLog leaf725Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf725RoundedFacts (by rfl)

private theorem leaf725FlatSound : Sound leaf725Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf725CertificateValid
    leaf725InnerLogValid leaf725CoversExact leaf725LowerChecked

private noncomputable def leaf726Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf726Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217819/134217728) }, vSqrt := { lower := (32765/32768), upper := (2097156/2097137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (146963611/134217728) }, upper := { exponent := 0, mantissa := (143/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194293/4194274) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf726InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf726LocalValidity :
    LeafFacts leaf726Box leaf726Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf726Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097156/2097137) }) = true
      norm_num [leaf726Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf726CertificateValid :
    WideCertificateValid leaf726Box leaf726Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi39ValidityFacts
    leaf726LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf726CoverageChecked :
    coverageCheck (innerAD leaf726Box) leaf726InnerLog = true := by
  rfl'

private theorem leaf726InnerLogValid :
    leaf726InnerLog.Valid 8 (innerAD leaf726Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf726CoverageChecked

private noncomputable def leaf726InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf726InputLogOnePlusV_eq :
    leaf726InputLogOnePlusV = outerEnclosure 24
      (leaf726Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf726RoundedFacts : LeafRoundedFacts 8
    leaf726Certificate.logOnePlusV leaf726InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf726InputLogOnePlusV_eq }

private noncomputable def leaf726Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi39InputQChi innerPair5Input
    leaf726InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf726LowerChecked :
    lowerCheck 24 leaf726Box leaf726Inputs = true := by
  rfl'

private theorem leaf726CoversExact : CoversExact 8
    leaf726Box leaf726Certificate leaf726InnerLog leaf726Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf726RoundedFacts (by rfl)

private theorem leaf726FlatSound : Sound leaf726Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf726CertificateValid
    leaf726InnerLogValid leaf726CoversExact leaf726LowerChecked

private noncomputable def leaf727Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf727Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217815/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33554173) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (148339787/134217728) }, upper := { exponent := 0, mantissa := (2307/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108669/67108346) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf727InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf727LocalValidity :
    LeafFacts leaf727Box leaf727Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf727Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33554173) }) = true
      norm_num [leaf727Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf727CertificateValid :
    WideCertificateValid leaf727Box leaf727Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi96ValidityFacts
    leaf727LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf727CoverageChecked :
    coverageCheck (innerAD leaf727Box) leaf727InnerLog = true := by
  rfl'

private theorem leaf727InnerLogValid :
    leaf727InnerLog.Valid 8 (innerAD leaf727Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf727CoverageChecked

private noncomputable def leaf727InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf727InputLogOnePlusV_eq :
    leaf727InputLogOnePlusV = outerEnclosure 24
      (leaf727Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf727RoundedFacts : LeafRoundedFacts 8
    leaf727Certificate.logOnePlusV leaf727InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf727InputLogOnePlusV_eq }

private noncomputable def leaf727Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi96InputQChi innerPair6Input
    leaf727InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf727LowerChecked :
    lowerCheck 24 leaf727Box leaf727Inputs = true := by
  rfl'

private theorem leaf727CoversExact : CoversExact 8
    leaf727Box leaf727Certificate leaf727InnerLog leaf727Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi96RoundedFacts
    innerPair6RoundedFacts leaf727RoundedFacts (by rfl)

private theorem leaf727FlatSound : Sound leaf727Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf727CertificateValid
    leaf727InnerLogValid leaf727CoversExact leaf727LowerChecked

private noncomputable def leaf728Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf728Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217817/134217728) }, vSqrt := { lower := (65531/65536), upper := (5592416/5592361) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (148732977/134217728) }, upper := { exponent := 0, mantissa := (1157/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11184777/11184722) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf728InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf728LocalValidity :
    LeafFacts leaf728Box leaf728Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf728Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5592416/5592361) }) = true
      norm_num [leaf728Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf728CertificateValid :
    WideCertificateValid leaf728Box leaf728Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi96ValidityFacts
    leaf728LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf728CoverageChecked :
    coverageCheck (innerAD leaf728Box) leaf728InnerLog = true := by
  rfl'

private theorem leaf728InnerLogValid :
    leaf728InnerLog.Valid 8 (innerAD leaf728Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf728CoverageChecked

private noncomputable def leaf728InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf728InputLogOnePlusV_eq :
    leaf728InputLogOnePlusV = outerEnclosure 24
      (leaf728Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf728RoundedFacts : LeafRoundedFacts 8
    leaf728Certificate.logOnePlusV leaf728InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf728InputLogOnePlusV_eq }

private noncomputable def leaf728Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi96InputQChi innerPair6Input
    leaf728InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf728LowerChecked :
    lowerCheck 24 leaf728Box leaf728Inputs = true := by
  rfl'

private theorem leaf728CoversExact : CoversExact 8
    leaf728Box leaf728Certificate leaf728InnerLog leaf728Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi96RoundedFacts
    innerPair6RoundedFacts leaf728RoundedFacts (by rfl)

private theorem leaf728FlatSound : Sound leaf728Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf728CertificateValid
    leaf728InnerLogValid leaf728CoversExact leaf728LowerChecked

private noncomputable def leaf729Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf729Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217817/134217728) }, vSqrt := { lower := (65531/65536), upper := (1398104/1398089) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (150698937/134217728) }, upper := { exponent := 0, mantissa := (293/256) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2796193/2796178) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf729InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf729LocalValidity :
    LeafFacts leaf729Box leaf729Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf729Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1398104/1398089) }) = true
      norm_num [leaf729Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf729CertificateValid :
    WideCertificateValid leaf729Box leaf729Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi97ValidityFacts
    leaf729LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf729CoverageChecked :
    coverageCheck (innerAD leaf729Box) leaf729InnerLog = true := by
  rfl'

private theorem leaf729InnerLogValid :
    leaf729InnerLog.Valid 8 (innerAD leaf729Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf729CoverageChecked

private noncomputable def leaf729InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629171/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf729InputLogOnePlusV_eq :
    leaf729InputLogOnePlusV = outerEnclosure 24
      (leaf729Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf729RoundedFacts : LeafRoundedFacts 8
    leaf729Certificate.logOnePlusV leaf729InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf729InputLogOnePlusV_eq }

private noncomputable def leaf729Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi97InputQChi innerPair6Input
    leaf729InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf729LowerChecked :
    lowerCheck 24 leaf729Box leaf729Inputs = true := by
  rfl'

private theorem leaf729CoversExact : CoversExact 8
    leaf729Box leaf729Certificate leaf729InnerLog leaf729Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi97RoundedFacts
    innerPair6RoundedFacts leaf729RoundedFacts (by rfl)

private theorem leaf729FlatSound : Sound leaf729Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf729CertificateValid
    leaf729InnerLogValid leaf729CoversExact leaf729LowerChecked

private noncomputable def leaf730Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf730Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217819/134217728) }, vSqrt := { lower := (65531/65536), upper := (2097156/2097133) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (151157659/134217728) }, upper := { exponent := 0, mantissa := (147/128) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194289/4194266) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf730InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf730LocalValidity :
    LeafFacts leaf730Box leaf730Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf730Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097156/2097133) }) = true
      norm_num [leaf730Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf730CertificateValid :
    WideCertificateValid leaf730Box leaf730Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi97ValidityFacts
    leaf730LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf730CoverageChecked :
    coverageCheck (innerAD leaf730Box) leaf730InnerLog = true := by
  rfl'

private theorem leaf730InnerLogValid :
    leaf730InnerLog.Valid 8 (innerAD leaf730Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf730CoverageChecked

private noncomputable def leaf730InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629173/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf730InputLogOnePlusV_eq :
    leaf730InputLogOnePlusV = outerEnclosure 24
      (leaf730Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf730RoundedFacts : LeafRoundedFacts 8
    leaf730Certificate.logOnePlusV leaf730InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf730InputLogOnePlusV_eq }

private noncomputable def leaf730Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi97InputQChi innerPair2Input
    leaf730InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf730LowerChecked :
    lowerCheck 24 leaf730Box leaf730Inputs = true := by
  rfl'

private theorem leaf730CoversExact : CoversExact 8
    leaf730Box leaf730Certificate leaf730InnerLog leaf730Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf730RoundedFacts (by rfl)

private theorem leaf730FlatSound : Sound leaf730Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf730CertificateValid
    leaf730InnerLogValid leaf730CoversExact leaf730LowerChecked

private noncomputable def leaf731Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf731Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217819/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33554159) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (149126167/134217728) }, upper := { exponent := 0, mantissa := (2321/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108655/67108318) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf731InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf731LocalValidity :
    LeafFacts leaf731Box leaf731Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf731Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33554159) }) = true
      norm_num [leaf731Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf731CertificateValid :
    WideCertificateValid leaf731Box leaf731Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi96ValidityFacts
    leaf731LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf731CoverageChecked :
    coverageCheck (innerAD leaf731Box) leaf731InnerLog = true := by
  rfl'

private theorem leaf731InnerLogValid :
    leaf731InnerLog.Valid 8 (innerAD leaf731Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf731CoverageChecked

private noncomputable def leaf731InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf731InputLogOnePlusV_eq :
    leaf731InputLogOnePlusV = outerEnclosure 24
      (leaf731Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf731RoundedFacts : LeafRoundedFacts 8
    leaf731Certificate.logOnePlusV leaf731InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf731InputLogOnePlusV_eq }

private noncomputable def leaf731Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi96InputQChi innerPair6Input
    leaf731InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf731LowerChecked :
    lowerCheck 24 leaf731Box leaf731Inputs = true := by
  rfl'

private theorem leaf731CoversExact : CoversExact 8
    leaf731Box leaf731Certificate leaf731InnerLog leaf731Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi96RoundedFacts
    innerPair6RoundedFacts leaf731RoundedFacts (by rfl)

private theorem leaf731FlatSound : Sound leaf731Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf731CertificateValid
    leaf731InnerLogValid leaf731CoversExact leaf731LowerChecked

private noncomputable def leaf732Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf732Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217821/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194269) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (149519357/134217728) }, upper := { exponent := 0, mantissa := (291/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388581/8388538) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf732InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf732LocalValidity :
    LeafFacts leaf732Box leaf732Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf732Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194269) }) = true
      norm_num [leaf732Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf732CertificateValid :
    WideCertificateValid leaf732Box leaf732Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi96ValidityFacts
    leaf732LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf732CoverageChecked :
    coverageCheck (innerAD leaf732Box) leaf732InnerLog = true := by
  rfl'

private theorem leaf732InnerLogValid :
    leaf732InnerLog.Valid 8 (innerAD leaf732Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf732CoverageChecked

private noncomputable def leaf732InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629167/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf732InputLogOnePlusV_eq :
    leaf732InputLogOnePlusV = outerEnclosure 24
      (leaf732Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf732RoundedFacts : LeafRoundedFacts 8
    leaf732Certificate.logOnePlusV leaf732InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf732InputLogOnePlusV_eq }

private noncomputable def leaf732Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi96InputQChi innerPair6Input
    leaf732InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf732LowerChecked :
    lowerCheck 24 leaf732Box leaf732Inputs = true := by
  rfl'

private theorem leaf732CoversExact : CoversExact 8
    leaf732Box leaf732Certificate leaf732InnerLog leaf732Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi96RoundedFacts
    innerPair6RoundedFacts leaf732RoundedFacts (by rfl)

private theorem leaf732FlatSound : Sound leaf732Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf732CertificateValid
    leaf732InnerLogValid leaf732CoversExact leaf732LowerChecked

private noncomputable def leaf733Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf733Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217821/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194265) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (151616381/134217728) }, upper := { exponent := 0, mantissa := (295/256) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388577/8388530) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf733InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf733LocalValidity :
    LeafFacts leaf733Box leaf733Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf733Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194265) }) = true
      norm_num [leaf733Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf733CertificateValid :
    WideCertificateValid leaf733Box leaf733Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi97ValidityFacts
    leaf733LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf733CoverageChecked :
    coverageCheck (innerAD leaf733Box) leaf733InnerLog = true := by
  rfl'

private theorem leaf733InnerLogValid :
    leaf733InnerLog.Valid 8 (innerAD leaf733Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf733CoverageChecked

private noncomputable def leaf733InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629175/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf733InputLogOnePlusV_eq :
    leaf733InputLogOnePlusV = outerEnclosure 24
      (leaf733Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf733RoundedFacts : LeafRoundedFacts 8
    leaf733Certificate.logOnePlusV leaf733InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf733InputLogOnePlusV_eq }

private noncomputable def leaf733Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi97InputQChi innerPair2Input
    leaf733InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf733LowerChecked :
    lowerCheck 24 leaf733Box leaf733Inputs = true := by
  rfl'

private theorem leaf733CoversExact : CoversExact 8
    leaf733Box leaf733Certificate leaf733InnerLog leaf733Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf733RoundedFacts (by rfl)

private theorem leaf733FlatSound : Sound leaf733Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf733CertificateValid
    leaf733InnerLogValid leaf733CoversExact leaf733LowerChecked

private noncomputable def leaf734Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf734Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217823/134217728) }, vSqrt := { lower := (32765/32768), upper := (174763/174761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (152075103/134217728) }, upper := { exponent := 0, mantissa := (37/32) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (174762/174761) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf734InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf734LocalValidity :
    LeafFacts leaf734Box leaf734Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf734Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (174763/174761) }) = true
      norm_num [leaf734Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf734CertificateValid :
    WideCertificateValid leaf734Box leaf734Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi97ValidityFacts
    leaf734LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf734CoverageChecked :
    coverageCheck (innerAD leaf734Box) leaf734InnerLog = true := by
  rfl'

private theorem leaf734InnerLogValid :
    leaf734InnerLog.Valid 8 (innerAD leaf734Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf734CoverageChecked

private noncomputable def leaf734InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629177/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf734InputLogOnePlusV_eq :
    leaf734InputLogOnePlusV = outerEnclosure 24
      (leaf734Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf734RoundedFacts : LeafRoundedFacts 8
    leaf734Certificate.logOnePlusV leaf734InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf734InputLogOnePlusV_eq }

private noncomputable def leaf734Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi97InputQChi innerPair2Input
    leaf734InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf734LowerChecked :
    lowerCheck 24 leaf734Box leaf734Inputs = true := by
  rfl'

private theorem leaf734CoversExact : CoversExact 8
    leaf734Box leaf734Certificate leaf734InnerLog leaf734Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf734RoundedFacts (by rfl)

private theorem leaf734FlatSound : Sound leaf734Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf734CertificateValid
    leaf734InnerLogValid leaf734CoversExact leaf734LowerChecked

private noncomputable def leaf735Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf735Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777248/16777031) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (76512623/67108864) }, upper := { exponent := 0, mantissa := (1209/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554279/33554062) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf735InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf735LocalValidity :
    LeafFacts leaf735Box leaf735Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf735Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16777031) }) = true
      norm_num [leaf735Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf735CertificateValid :
    WideCertificateValid leaf735Box leaf735Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi32ValidityFacts
    leaf735LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf735CoverageChecked :
    coverageCheck (innerAD leaf735Box) leaf735InnerLog = true := by
  rfl'

private theorem leaf735InnerLogValid :
    leaf735InnerLog.Valid 8 (innerAD leaf735Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf735CoverageChecked

private noncomputable def leaf735InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629189/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf735InputLogOnePlusV_eq :
    leaf735InputLogOnePlusV = outerEnclosure 24
      (leaf735Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf735RoundedFacts : LeafRoundedFacts 8
    leaf735Certificate.logOnePlusV leaf735InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf735InputLogOnePlusV_eq }

private noncomputable def leaf735Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi32InputQChi innerPair2Input
    leaf735InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf735LowerChecked :
    lowerCheck 24 leaf735Box leaf735Inputs = true := by
  rfl'

private theorem leaf735CoversExact : CoversExact 8
    leaf735Box leaf735Certificate leaf735InnerLog leaf735Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi32RoundedFacts
    innerPair2RoundedFacts leaf735RoundedFacts (by rfl)

private theorem leaf735FlatSound : Sound leaf735Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf735CertificateValid
    leaf735InnerLogValid leaf735CoversExact leaf735LowerChecked

private noncomputable def leaf736Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf736Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108949/67108864) }, vSqrt := { lower := (65531/65536), upper := (2796208/2796171) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (76774749/67108864) }, upper := { exponent := 0, mantissa := (607/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5592379/5592342) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf736InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf736LocalValidity :
    LeafFacts leaf736Box leaf736Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf736Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2796208/2796171) }) = true
      norm_num [leaf736Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf736CertificateValid :
    WideCertificateValid leaf736Box leaf736Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi32ValidityFacts
    leaf736LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf736CoverageChecked :
    coverageCheck (innerAD leaf736Box) leaf736InnerLog = true := by
  rfl'

private theorem leaf736InnerLogValid :
    leaf736InnerLog.Valid 8 (innerAD leaf736Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf736CoverageChecked

private noncomputable def leaf736InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453649/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf736InputLogOnePlusV_eq :
    leaf736InputLogOnePlusV = outerEnclosure 24
      (leaf736Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf736RoundedFacts : LeafRoundedFacts 8
    leaf736Certificate.logOnePlusV leaf736InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf736InputLogOnePlusV_eq }

private noncomputable def leaf736Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi32InputQChi innerPair2Input
    leaf736InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf736LowerChecked :
    lowerCheck 24 leaf736Box leaf736Inputs = true := by
  rfl'

private theorem leaf736CoversExact : CoversExact 8
    leaf736Box leaf736Certificate leaf736InnerLog leaf736Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi32RoundedFacts
    innerPair2RoundedFacts leaf736RoundedFacts (by rfl)

private theorem leaf736FlatSound : Sound leaf736Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf736CertificateValid
    leaf736InnerLogValid leaf736CoversExact leaf736LowerChecked

private noncomputable def leaf737Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf737Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108949/67108864) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388497) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (78871773/67108864) }, upper := { exponent := 0, mantissa := (623/512) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777121/16776994) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf737InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf737LocalValidity :
    LeafFacts leaf737Box leaf737Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf737Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388497) }) = true
      norm_num [leaf737Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf737CertificateValid :
    WideCertificateValid leaf737Box leaf737Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi33ValidityFacts
    leaf737LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf737CoverageChecked :
    coverageCheck (innerAD leaf737Box) leaf737InnerLog = true := by
  rfl'

private theorem leaf737InnerLogValid :
    leaf737InnerLog.Valid 8 (innerAD leaf737Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf737CoverageChecked

private noncomputable def leaf737InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453651/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf737InputLogOnePlusV_eq :
    leaf737InputLogOnePlusV = outerEnclosure 24
      (leaf737Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf737RoundedFacts : LeafRoundedFacts 8
    leaf737Certificate.logOnePlusV leaf737InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf737InputLogOnePlusV_eq }

private noncomputable def leaf737Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi33InputQChi innerPair3Input
    leaf737InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf737LowerChecked :
    lowerCheck 24 leaf737Box leaf737Inputs = true := by
  rfl'

private theorem leaf737CoversExact : CoversExact 8
    leaf737Box leaf737Certificate leaf737InnerLog leaf737Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi33RoundedFacts
    innerPair3RoundedFacts leaf737RoundedFacts (by rfl)

private theorem leaf737FlatSound : Sound leaf737Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf737CertificateValid
    leaf737InnerLogValid leaf737CoversExact leaf737LowerChecked

private noncomputable def leaf738Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf738Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108951/67108864) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194247) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (79199431/67108864) }, upper := { exponent := 0, mantissa := (313/256) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388559/8388494) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf738InnerLog : WideLogData :=
  innerPair391Data

set_option maxRecDepth 1000000 in
private theorem leaf738LocalValidity :
    LeafFacts leaf738Box leaf738Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf738Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194247) }) = true
      norm_num [leaf738Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf738CertificateValid :
    WideCertificateValid leaf738Box leaf738Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi33ValidityFacts
    leaf738LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf738CoverageChecked :
    coverageCheck (innerAD leaf738Box) leaf738InnerLog = true := by
  rfl'

private theorem leaf738InnerLogValid :
    leaf738InnerLog.Valid 8 (innerAD leaf738Box) :=
  wideLogDataValid_of_cachedCheck endpoint101PositiveFacts
    endpoint102PositiveFacts.valid leaf738CoverageChecked

private noncomputable def leaf738InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf738InputLogOnePlusV_eq :
    leaf738InputLogOnePlusV = outerEnclosure 24
      (leaf738Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf738RoundedFacts : LeafRoundedFacts 8
    leaf738Certificate.logOnePlusV leaf738InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf738InputLogOnePlusV_eq }

private noncomputable def leaf738Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi33InputQChi innerPair391Input
    leaf738InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf738LowerChecked :
    lowerCheck 24 leaf738Box leaf738Inputs = true := by
  rfl'

private theorem leaf738CoversExact : CoversExact 8
    leaf738Box leaf738Certificate leaf738InnerLog leaf738Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi33RoundedFacts
    innerPair391RoundedFacts leaf738RoundedFacts (by rfl)

private theorem leaf738FlatSound : Sound leaf738Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf738CertificateValid
    leaf738InnerLogValid leaf738CoversExact leaf738LowerChecked

private noncomputable def leaf739Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf739Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108951/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777248/16777021) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (77036875/67108864) }, upper := { exponent := 0, mantissa := (1219/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554269/33554042) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf739InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf739LocalValidity :
    LeafFacts leaf739Box leaf739Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf739Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16777021) }) = true
      norm_num [leaf739Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf739CertificateValid :
    WideCertificateValid leaf739Box leaf739Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi32ValidityFacts
    leaf739LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf739CoverageChecked :
    coverageCheck (innerAD leaf739Box) leaf739InnerLog = true := by
  rfl'

private theorem leaf739InnerLogValid :
    leaf739InnerLog.Valid 8 (innerAD leaf739Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf739CoverageChecked

private noncomputable def leaf739InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814597/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf739InputLogOnePlusV_eq :
    leaf739InputLogOnePlusV = outerEnclosure 24
      (leaf739Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf739RoundedFacts : LeafRoundedFacts 8
    leaf739Certificate.logOnePlusV leaf739InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf739InputLogOnePlusV_eq }

private noncomputable def leaf739Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi32InputQChi innerPair3Input
    leaf739InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf739LowerChecked :
    lowerCheck 24 leaf739Box leaf739Inputs = true := by
  rfl'

private theorem leaf739CoversExact : CoversExact 8
    leaf739Box leaf739Certificate leaf739InnerLog leaf739Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi32RoundedFacts
    innerPair3RoundedFacts leaf739RoundedFacts (by rfl)

private theorem leaf739FlatSound : Sound leaf739Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf739CertificateValid
    leaf739InnerLogValid leaf739CoversExact leaf739LowerChecked

private noncomputable def leaf740Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf740Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108953/67108864) }, vSqrt := { lower := (32765/32768), upper := (2097156/2097127) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (77299001/67108864) }, upper := { exponent := 0, mantissa := (153/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194283/4194254) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf740InnerLog : WideLogData :=
  innerPair135Data

set_option maxRecDepth 1000000 in
private theorem leaf740LocalValidity :
    LeafFacts leaf740Box leaf740Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf740Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097156/2097127) }) = true
      norm_num [leaf740Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf740CertificateValid :
    WideCertificateValid leaf740Box leaf740Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi32ValidityFacts
    leaf740LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf740CoverageChecked :
    coverageCheck (innerAD leaf740Box) leaf740InnerLog = true := by
  rfl'

private theorem leaf740InnerLogValid :
    leaf740InnerLog.Valid 8 (innerAD leaf740Box) :=
  wideLogDataValid_of_cachedCheck endpoint31PositiveFacts
    endpoint26PositiveFacts.valid leaf740CoverageChecked

private noncomputable def leaf740InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629197/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf740InputLogOnePlusV_eq :
    leaf740InputLogOnePlusV = outerEnclosure 24
      (leaf740Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf740RoundedFacts : LeafRoundedFacts 8
    leaf740Certificate.logOnePlusV leaf740InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf740InputLogOnePlusV_eq }

private noncomputable def leaf740Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi32InputQChi innerPair135Input
    leaf740InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf740LowerChecked :
    lowerCheck 24 leaf740Box leaf740Inputs = true := by
  rfl'

private theorem leaf740CoversExact : CoversExact 8
    leaf740Box leaf740Certificate leaf740InnerLog leaf740Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi32RoundedFacts
    innerPair135RoundedFacts leaf740RoundedFacts (by rfl)

private theorem leaf740FlatSound : Sound leaf740Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf740CertificateValid
    leaf740InnerLogValid leaf740CoversExact leaf740LowerChecked

private noncomputable def leaf741Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf741Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33554003) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (159087023/134217728) }, upper := { exponent := 0, mantissa := (2477/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108499/67108006) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf741InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf741LocalValidity :
    LeafFacts leaf741Box leaf741Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf741Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33554003) }) = true
      norm_num [leaf741Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf741CertificateValid :
    WideCertificateValid leaf741Box leaf741Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi103ValidityFacts
    leaf741LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf741CoverageChecked :
    coverageCheck (innerAD leaf741Box) leaf741InnerLog = true := by
  rfl'

private theorem leaf741InnerLogValid :
    leaf741InnerLog.Valid 8 (innerAD leaf741Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf741CoverageChecked

private noncomputable def leaf741InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907301/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf741InputLogOnePlusV_eq :
    leaf741InputLogOnePlusV = outerEnclosure 24
      (leaf741Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf741RoundedFacts : LeafRoundedFacts 8
    leaf741Certificate.logOnePlusV leaf741InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf741InputLogOnePlusV_eq }

private noncomputable def leaf741Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi103InputQChi innerPair3Input
    leaf741InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf741LowerChecked :
    lowerCheck 24 leaf741Box leaf741Inputs = true := by
  rfl'

private theorem leaf741CoversExact : CoversExact 8
    leaf741Box leaf741Certificate leaf741InnerLog leaf741Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi103RoundedFacts
    innerPair3RoundedFacts leaf741RoundedFacts (by rfl)

private theorem leaf741FlatSound : Sound leaf741Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf741CertificateValid
    leaf741InnerLogValid leaf741CoversExact leaf741LowerChecked

private noncomputable def leaf742Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf742Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388491) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (161577237/134217728) }, upper := { exponent := 0, mantissa := (629/512) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777115/16776982) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf742InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf742LocalValidity :
    LeafFacts leaf742Box leaf742Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf742Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388491) }) = true
      norm_num [leaf742Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf742CertificateValid :
    WideCertificateValid leaf742Box leaf742Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi104ValidityFacts
    leaf742LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf742CoverageChecked :
    coverageCheck (innerAD leaf742Box) leaf742InnerLog = true := by
  rfl'

private theorem leaf742InnerLogValid :
    leaf742InnerLog.Valid 8 (innerAD leaf742Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf742CoverageChecked

private noncomputable def leaf742InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf742InputLogOnePlusV_eq :
    leaf742InputLogOnePlusV = outerEnclosure 24
      (leaf742Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf742RoundedFacts : LeafRoundedFacts 8
    leaf742Certificate.logOnePlusV leaf742InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf742InputLogOnePlusV_eq }

private noncomputable def leaf742Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi104InputQChi innerPair12Input
    leaf742InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf742LowerChecked :
    lowerCheck 24 leaf742Box leaf742Inputs = true := by
  rfl'

private theorem leaf742CoversExact : CoversExact 8
    leaf742Box leaf742Certificate leaf742InnerLog leaf742Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi104RoundedFacts
    innerPair12RoundedFacts leaf742RoundedFacts (by rfl)

private theorem leaf742FlatSound : Sound leaf742Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf742CertificateValid
    leaf742InnerLogValid leaf742CoversExact leaf742LowerChecked

private noncomputable def leaf743Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf743Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (32765/32768), upper := (1398104/1398083) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (159742341/134217728) }, upper := { exponent := 0, mantissa := (311/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2796187/2796166) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf743InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf743LocalValidity :
    LeafFacts leaf743Box leaf743Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf743Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1398104/1398083) }) = true
      norm_num [leaf743Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf743CertificateValid :
    WideCertificateValid leaf743Box leaf743Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi103ValidityFacts
    leaf743LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf743CoverageChecked :
    coverageCheck (innerAD leaf743Box) leaf743InnerLog = true := by
  rfl'

private theorem leaf743InnerLogValid :
    leaf743InnerLog.Valid 8 (innerAD leaf743Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf743CoverageChecked

private noncomputable def leaf743InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629207/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf743InputLogOnePlusV_eq :
    leaf743InputLogOnePlusV = outerEnclosure 24
      (leaf743Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf743RoundedFacts : LeafRoundedFacts 8
    leaf743Certificate.logOnePlusV leaf743InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf743InputLogOnePlusV_eq }

private noncomputable def leaf743Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi103InputQChi innerPair12Input
    leaf743InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf743LowerChecked :
    lowerCheck 24 leaf743Box leaf743Inputs = true := by
  rfl'

private theorem leaf743CoversExact : CoversExact 8
    leaf743Box leaf743Certificate leaf743InnerLog leaf743Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi103RoundedFacts
    innerPair12RoundedFacts leaf743RoundedFacts (by rfl)

private theorem leaf743FlatSound : Sound leaf743Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf743CertificateValid
    leaf743InnerLogValid leaf743CoversExact leaf743LowerChecked

private noncomputable def leaf744Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf744Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (162298087/134217728) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf744InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf744LocalValidity :
    LeafFacts leaf744Box leaf744Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf744Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048578/1048561) }) = true
      norm_num [leaf744Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf744CertificateValid :
    WideCertificateValid leaf744Box leaf744Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi104ValidityFacts
    leaf744LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf744CoverageChecked :
    coverageCheck (innerAD leaf744Box) leaf744InnerLog = true := by
  rfl'

private theorem leaf744InnerLogValid :
    leaf744InnerLog.Valid 8 (innerAD leaf744Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf744CoverageChecked

private noncomputable def leaf744InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf744InputLogOnePlusV_eq :
    leaf744InputLogOnePlusV = outerEnclosure 24
      (leaf744Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf744RoundedFacts : LeafRoundedFacts 8
    leaf744Certificate.logOnePlusV leaf744InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf744InputLogOnePlusV_eq }

private noncomputable def leaf744Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi104InputQChi innerPair12Input
    leaf744InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf744LowerChecked :
    lowerCheck 24 leaf744Box leaf744Inputs = true := by
  rfl'

private theorem leaf744CoversExact : CoversExact 8
    leaf744Box leaf744Certificate leaf744InnerLog leaf744Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi104RoundedFacts
    innerPair12RoundedFacts leaf744RoundedFacts (by rfl)

private theorem leaf744FlatSound : Sound leaf744Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf744CertificateValid
    leaf744InnerLogValid leaf744CoversExact leaf744LowerChecked

private noncomputable def leaf745Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf745Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553951) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (162494687/134217728) }, upper := { exponent := 0, mantissa := (2529/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108447/67107902) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf745InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf745LocalValidity :
    LeafFacts leaf745Box leaf745Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf745Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553951) }) = true
      norm_num [leaf745Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf745CertificateValid :
    WideCertificateValid leaf745Box leaf745Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi105ValidityFacts
    leaf745LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf745CoverageChecked :
    coverageCheck (innerAD leaf745Box) leaf745InnerLog = true := by
  rfl'

private theorem leaf745InnerLogValid :
    leaf745InnerLog.Valid 8 (innerAD leaf745Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf745CoverageChecked

private noncomputable def leaf745InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf745InputLogOnePlusV_eq :
    leaf745InputLogOnePlusV = outerEnclosure 24
      (leaf745Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf745RoundedFacts : LeafRoundedFacts 8
    leaf745Certificate.logOnePlusV leaf745InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf745InputLogOnePlusV_eq }

private noncomputable def leaf745Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi105InputQChi innerPair12Input
    leaf745InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf745LowerChecked :
    lowerCheck 24 leaf745Box leaf745Inputs = true := by
  rfl'

private theorem leaf745CoversExact : CoversExact 8
    leaf745Box leaf745Certificate leaf745InnerLog leaf745Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi105RoundedFacts
    innerPair12RoundedFacts leaf745RoundedFacts (by rfl)

private theorem leaf745FlatSound : Sound leaf745Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf745CertificateValid
    leaf745InnerLogValid leaf745CoversExact leaf745LowerChecked

private noncomputable def leaf746Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf746Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (65531/65536), upper := (5592416/5592319) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (164853837/134217728) }, upper := { exponent := 0, mantissa := (1283/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11184735/11184638) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf746InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf746LocalValidity :
    LeafFacts leaf746Box leaf746Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf746Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5592416/5592319) }) = true
      norm_num [leaf746Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf746CertificateValid :
    WideCertificateValid leaf746Box leaf746Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi106ValidityFacts
    leaf746LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf746CoverageChecked :
    coverageCheck (innerAD leaf746Box) leaf746InnerLog = true := by
  rfl'

private theorem leaf746InnerLogValid :
    leaf746InnerLog.Valid 8 (innerAD leaf746Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf746CoverageChecked

private noncomputable def leaf746InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf746InputLogOnePlusV_eq :
    leaf746InputLogOnePlusV = outerEnclosure 24
      (leaf746Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf746RoundedFacts : LeafRoundedFacts 8
    leaf746Certificate.logOnePlusV leaf746InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf746InputLogOnePlusV_eq }

private noncomputable def leaf746Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi106InputQChi innerPair13Input
    leaf746InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf746LowerChecked :
    lowerCheck 24 leaf746Box leaf746Inputs = true := by
  rfl'

private theorem leaf746CoversExact : CoversExact 8
    leaf746Box leaf746Certificate leaf746InnerLog leaf746Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi106RoundedFacts
    innerPair13RoundedFacts leaf746RoundedFacts (by rfl)

private theorem leaf746FlatSound : Sound leaf746Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf746CertificateValid
    leaf746InnerLogValid leaf746CoversExact leaf746LowerChecked

private noncomputable def leaf747Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf747Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (65531/65536), upper := (5592416/5592323) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (163281069/134217728) }, upper := { exponent := 0, mantissa := (1271/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11184739/11184646) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf747InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf747LocalValidity :
    LeafFacts leaf747Box leaf747Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf747Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5592416/5592323) }) = true
      norm_num [leaf747Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf747CertificateValid :
    WideCertificateValid leaf747Box leaf747Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi105ValidityFacts
    leaf747LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf747CoverageChecked :
    coverageCheck (innerAD leaf747Box) leaf747InnerLog = true := by
  rfl'

private theorem leaf747InnerLogValid :
    leaf747InnerLog.Valid 8 (innerAD leaf747Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf747CoverageChecked

private noncomputable def leaf747InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf747InputLogOnePlusV_eq :
    leaf747InputLogOnePlusV = outerEnclosure 24
      (leaf747Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf747RoundedFacts : LeafRoundedFacts 8
    leaf747Certificate.logOnePlusV leaf747InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf747InputLogOnePlusV_eq }

private noncomputable def leaf747Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi105InputQChi innerPair12Input
    leaf747InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf747LowerChecked :
    lowerCheck 24 leaf747Box leaf747Inputs = true := by
  rfl'

private theorem leaf747CoversExact : CoversExact 8
    leaf747Box leaf747Certificate leaf747InnerLog leaf747Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi105RoundedFacts
    innerPair12RoundedFacts leaf747RoundedFacts (by rfl)

private theorem leaf747FlatSound : Sound leaf747Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf747CertificateValid
    leaf747InnerLogValid leaf747CoversExact leaf747LowerChecked

private noncomputable def leaf748Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf748Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388475) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (165705751/134217728) }, upper := { exponent := 0, mantissa := (645/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777099/16776950) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf748InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf748LocalValidity :
    LeafFacts leaf748Box leaf748Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf748Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388475) }) = true
      norm_num [leaf748Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf748CertificateValid :
    WideCertificateValid leaf748Box leaf748Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi106ValidityFacts
    leaf748LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf748CoverageChecked :
    coverageCheck (innerAD leaf748Box) leaf748InnerLog = true := by
  rfl'

private theorem leaf748InnerLogValid :
    leaf748InnerLog.Valid 8 (innerAD leaf748Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf748CoverageChecked

private noncomputable def leaf748InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf748InputLogOnePlusV_eq :
    leaf748InputLogOnePlusV = outerEnclosure 24
      (leaf748Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf748RoundedFacts : LeafRoundedFacts 8
    leaf748Certificate.logOnePlusV leaf748InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf748InputLogOnePlusV_eq }

private noncomputable def leaf748Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi106InputQChi innerPair13Input
    leaf748InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf748LowerChecked :
    lowerCheck 24 leaf748Box leaf748Inputs = true := by
  rfl'

private theorem leaf748CoversExact : CoversExact 8
    leaf748Box leaf748Certificate leaf748InnerLog leaf748Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi106RoundedFacts
    innerPair13RoundedFacts leaf748RoundedFacts (by rfl)

private theorem leaf748FlatSound : Sound leaf748Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf748CertificateValid
    leaf748InnerLogValid leaf748CoversExact leaf748LowerChecked

private noncomputable def leaf749Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf749Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553877) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (167212987/134217728) }, upper := { exponent := 0, mantissa := (2603/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108373/67107754) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf749InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf749LocalValidity :
    LeafFacts leaf749Box leaf749Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf749Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553877) }) = true
      norm_num [leaf749Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf749CertificateValid :
    WideCertificateValid leaf749Box leaf749Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi98ValidityFacts
    leaf749LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf749CoverageChecked :
    coverageCheck (innerAD leaf749Box) leaf749InnerLog = true := by
  rfl'

private theorem leaf749InnerLogValid :
    leaf749InnerLog.Valid 8 (innerAD leaf749Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf749CoverageChecked

private noncomputable def leaf749InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf749InputLogOnePlusV_eq :
    leaf749InputLogOnePlusV = outerEnclosure 24
      (leaf749Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf749RoundedFacts : LeafRoundedFacts 8
    leaf749Certificate.logOnePlusV leaf749InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf749InputLogOnePlusV_eq }

private noncomputable def leaf749Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi98InputQChi innerPair13Input
    leaf749InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf749LowerChecked :
    lowerCheck 24 leaf749Box leaf749Inputs = true := by
  rfl'

private theorem leaf749CoversExact : CoversExact 8
    leaf749Box leaf749Certificate leaf749InnerLog leaf749Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi98RoundedFacts
    innerPair13RoundedFacts leaf749RoundedFacts (by rfl)

private theorem leaf749FlatSound : Sound leaf749Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf749CertificateValid
    leaf749InnerLogValid leaf749CoversExact leaf749LowerChecked

private noncomputable def leaf750Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf750Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (65531/65536), upper := (2097156/2097115) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (169572137/134217728) }, upper := { exponent := 0, mantissa := (165/128) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194271/4194230) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf750InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf750LocalValidity :
    LeafFacts leaf750Box leaf750Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf750Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097156/2097115) }) = true
      norm_num [leaf750Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf750CertificateValid :
    WideCertificateValid leaf750Box leaf750Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi99ValidityFacts
    leaf750LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf750CoverageChecked :
    coverageCheck (innerAD leaf750Box) leaf750InnerLog = true := by
  rfl'

private theorem leaf750InnerLogValid :
    leaf750InnerLog.Valid 8 (innerAD leaf750Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf750CoverageChecked

private noncomputable def leaf750InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf750InputLogOnePlusV_eq :
    leaf750InputLogOnePlusV = outerEnclosure 24
      (leaf750Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf750RoundedFacts : LeafRoundedFacts 8
    leaf750Certificate.logOnePlusV leaf750InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf750InputLogOnePlusV_eq }

private noncomputable def leaf750Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi99InputQChi innerPair16Input
    leaf750InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf750LowerChecked :
    lowerCheck 24 leaf750Box leaf750Inputs = true := by
  rfl'

private theorem leaf750CoversExact : CoversExact 8
    leaf750Box leaf750Certificate leaf750InnerLog leaf750Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi99RoundedFacts
    innerPair16RoundedFacts leaf750RoundedFacts (by rfl)

private theorem leaf750FlatSound : Sound leaf750Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf750CertificateValid
    leaf750InnerLogValid leaf750CoversExact leaf750LowerChecked

private noncomputable def leaf751Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf751Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776931) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (168130433/134217728) }, upper := { exponent := 0, mantissa := (1309/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554179/33553862) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf751InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf751LocalValidity :
    LeafFacts leaf751Box leaf751Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf751Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776931) }) = true
      norm_num [leaf751Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf751CertificateValid :
    WideCertificateValid leaf751Box leaf751Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi98ValidityFacts
    leaf751LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf751CoverageChecked :
    coverageCheck (innerAD leaf751Box) leaf751InnerLog = true := by
  rfl'

private theorem leaf751InnerLogValid :
    leaf751InnerLog.Valid 8 (innerAD leaf751Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf751CoverageChecked

private noncomputable def leaf751InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf751InputLogOnePlusV_eq :
    leaf751InputLogOnePlusV = outerEnclosure 24
      (leaf751Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf751RoundedFacts : LeafRoundedFacts 8
    leaf751Certificate.logOnePlusV leaf751InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf751InputLogOnePlusV_eq }

private noncomputable def leaf751Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi98InputQChi innerPair16Input
    leaf751InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf751LowerChecked :
    lowerCheck 24 leaf751Box leaf751Inputs = true := by
  rfl'

private theorem leaf751CoversExact : CoversExact 8
    leaf751Box leaf751Certificate leaf751InnerLog leaf751Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi98RoundedFacts
    innerPair16RoundedFacts leaf751RoundedFacts (by rfl)

private theorem leaf751FlatSound : Sound leaf751Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf751CertificateValid
    leaf751InnerLogValid leaf751CoversExact leaf751LowerChecked

private noncomputable def leaf752Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf752Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (65531/65536), upper := (349526/349519) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (170555115/134217728) }, upper := { exponent := 0, mantissa := (83/64) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (699045/699038) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf752InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf752LocalValidity :
    LeafFacts leaf752Box leaf752Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf752Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (349526/349519) }) = true
      norm_num [leaf752Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf752CertificateValid :
    WideCertificateValid leaf752Box leaf752Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi99ValidityFacts
    leaf752LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf752CoverageChecked :
    coverageCheck (innerAD leaf752Box) leaf752InnerLog = true := by
  rfl'

private theorem leaf752InnerLogValid :
    leaf752InnerLog.Valid 8 (innerAD leaf752Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf752CoverageChecked

private noncomputable def leaf752InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf752InputLogOnePlusV_eq :
    leaf752InputLogOnePlusV = outerEnclosure 24
      (leaf752Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf752RoundedFacts : LeafRoundedFacts 8
    leaf752Certificate.logOnePlusV leaf752InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf752InputLogOnePlusV_eq }

private noncomputable def leaf752Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi99InputQChi innerPair16Input
    leaf752InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf752LowerChecked :
    lowerCheck 24 leaf752Box leaf752Inputs = true := by
  rfl'

private theorem leaf752CoversExact : CoversExact 8
    leaf752Box leaf752Certificate leaf752InnerLog leaf752Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi99RoundedFacts
    innerPair16RoundedFacts leaf752RoundedFacts (by rfl)

private theorem leaf752FlatSound : Sound leaf752Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf752CertificateValid
    leaf752InnerLogValid leaf752CoversExact leaf752LowerChecked

private noncomputable def leaf753Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf753Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553925) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (164067451/134217728) }, upper := { exponent := 0, mantissa := (2555/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108421/67107850) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf753InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf753LocalValidity :
    LeafFacts leaf753Box leaf753Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf753Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553925) }) = true
      norm_num [leaf753Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf753CertificateValid :
    WideCertificateValid leaf753Box leaf753Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi105ValidityFacts
    leaf753LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf753CoverageChecked :
    coverageCheck (innerAD leaf753Box) leaf753InnerLog = true := by
  rfl'

private theorem leaf753InnerLogValid :
    leaf753InnerLog.Valid 8 (innerAD leaf753Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf753CoverageChecked

private noncomputable def leaf753InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf753InputLogOnePlusV_eq :
    leaf753InputLogOnePlusV = outerEnclosure 24
      (leaf753Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf753RoundedFacts : LeafRoundedFacts 8
    leaf753Certificate.logOnePlusV leaf753InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf753InputLogOnePlusV_eq }

private noncomputable def leaf753Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi105InputQChi innerPair12Input
    leaf753InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf753LowerChecked :
    lowerCheck 24 leaf753Box leaf753Inputs = true := by
  rfl'

private theorem leaf753CoversExact : CoversExact 8
    leaf753Box leaf753Certificate leaf753InnerLog leaf753Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi105RoundedFacts
    innerPair12RoundedFacts leaf753RoundedFacts (by rfl)

private theorem leaf753FlatSound : Sound leaf753Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf753CertificateValid
    leaf753InnerLogValid leaf753CoversExact leaf753LowerChecked

private noncomputable def leaf754Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf754Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776943) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (166557665/134217728) }, upper := { exponent := 0, mantissa := (1297/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554191/33553886) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf754InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf754LocalValidity :
    LeafFacts leaf754Box leaf754Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf754Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776943) }) = true
      norm_num [leaf754Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf754CertificateValid :
    WideCertificateValid leaf754Box leaf754Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi106ValidityFacts
    leaf754LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf754CoverageChecked :
    coverageCheck (innerAD leaf754Box) leaf754InnerLog = true := by
  rfl'

private theorem leaf754InnerLogValid :
    leaf754InnerLog.Valid 8 (innerAD leaf754Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf754CoverageChecked

private noncomputable def leaf754InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf754InputLogOnePlusV_eq :
    leaf754InputLogOnePlusV = outerEnclosure 24
      (leaf754Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf754RoundedFacts : LeafRoundedFacts 8
    leaf754Certificate.logOnePlusV leaf754InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf754InputLogOnePlusV_eq }

private noncomputable def leaf754Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi106InputQChi innerPair13Input
    leaf754InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf754LowerChecked :
    lowerCheck 24 leaf754Box leaf754Inputs = true := by
  rfl'

private theorem leaf754CoversExact : CoversExact 8
    leaf754Box leaf754Certificate leaf754InnerLog leaf754Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi106RoundedFacts
    innerPair13RoundedFacts leaf754RoundedFacts (by rfl)

private theorem leaf754FlatSound : Sound leaf754Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf754CertificateValid
    leaf754InnerLogValid leaf754CoversExact leaf754LowerChecked

private noncomputable def leaf755Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf755Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194239) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (164853833/134217728) }, upper := { exponent := 0, mantissa := (321/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388551/8388478) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf755InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf755LocalValidity :
    LeafFacts leaf755Box leaf755Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf755Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194239) }) = true
      norm_num [leaf755Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf755CertificateValid :
    WideCertificateValid leaf755Box leaf755Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi105ValidityFacts
    leaf755LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf755CoverageChecked :
    coverageCheck (innerAD leaf755Box) leaf755InnerLog = true := by
  rfl'

private theorem leaf755InnerLogValid :
    leaf755InnerLog.Valid 8 (innerAD leaf755Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf755CoverageChecked

private noncomputable def leaf755InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf755InputLogOnePlusV_eq :
    leaf755InputLogOnePlusV = outerEnclosure 24
      (leaf755Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf755RoundedFacts : LeafRoundedFacts 8
    leaf755Certificate.logOnePlusV leaf755InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf755InputLogOnePlusV_eq }

private noncomputable def leaf755Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi105InputQChi innerPair13Input
    leaf755InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf755LowerChecked :
    lowerCheck 24 leaf755Box leaf755Inputs = true := by
  rfl'

private theorem leaf755CoversExact : CoversExact 8
    leaf755Box leaf755Certificate leaf755InnerLog leaf755Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi105RoundedFacts
    innerPair13RoundedFacts leaf755RoundedFacts (by rfl)

private theorem leaf755FlatSound : Sound leaf755Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf755CertificateValid
    leaf755InnerLogValid leaf755CoversExact leaf755LowerChecked

private noncomputable def leaf756Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf756Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (699052/699039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (167409579/134217728) }, upper := { exponent := 0, mantissa := (163/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1398091/1398078) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf756InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf756LocalValidity :
    LeafFacts leaf756Box leaf756Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf756Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (699052/699039) }) = true
      norm_num [leaf756Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf756CertificateValid :
    WideCertificateValid leaf756Box leaf756Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi106ValidityFacts
    leaf756LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf756CoverageChecked :
    coverageCheck (innerAD leaf756Box) leaf756InnerLog = true := by
  rfl'

private theorem leaf756InnerLogValid :
    leaf756InnerLog.Valid 8 (innerAD leaf756Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf756CoverageChecked

private noncomputable def leaf756InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf756InputLogOnePlusV_eq :
    leaf756InputLogOnePlusV = outerEnclosure 24
      (leaf756Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf756RoundedFacts : LeafRoundedFacts 8
    leaf756Certificate.logOnePlusV leaf756InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf756InputLogOnePlusV_eq }

private noncomputable def leaf756Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi106InputQChi innerPair13Input
    leaf756InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf756LowerChecked :
    lowerCheck 24 leaf756Box leaf756Inputs = true := by
  rfl'

private theorem leaf756CoversExact : CoversExact 8
    leaf756Box leaf756Certificate leaf756InnerLog leaf756Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi106RoundedFacts
    innerPair13RoundedFacts leaf756RoundedFacts (by rfl)

private theorem leaf756FlatSound : Sound leaf756Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf756CertificateValid
    leaf756InnerLogValid leaf756CoversExact leaf756LowerChecked

private noncomputable def leaf757Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf757Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553847) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (169047879/134217728) }, upper := { exponent := 0, mantissa := (2633/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108343/67107694) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf757InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf757LocalValidity :
    LeafFacts leaf757Box leaf757Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf757Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553847) }) = true
      norm_num [leaf757Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf757CertificateValid :
    WideCertificateValid leaf757Box leaf757Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi98ValidityFacts
    leaf757LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf757CoverageChecked :
    coverageCheck (innerAD leaf757Box) leaf757InnerLog = true := by
  rfl'

private theorem leaf757InnerLogValid :
    leaf757InnerLog.Valid 8 (innerAD leaf757Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf757CoverageChecked

private noncomputable def leaf757InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf757InputLogOnePlusV_eq :
    leaf757InputLogOnePlusV = outerEnclosure 24
      (leaf757Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf757RoundedFacts : LeafRoundedFacts 8
    leaf757Certificate.logOnePlusV leaf757InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf757InputLogOnePlusV_eq }

private noncomputable def leaf757Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi98InputQChi innerPair16Input
    leaf757InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf757LowerChecked :
    lowerCheck 24 leaf757Box leaf757Inputs = true := by
  rfl'

private theorem leaf757CoversExact : CoversExact 8
    leaf757Box leaf757Certificate leaf757InnerLog leaf757Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi98RoundedFacts
    innerPair16RoundedFacts leaf757RoundedFacts (by rfl)

private theorem leaf757FlatSound : Sound leaf757Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf757CertificateValid
    leaf757InnerLogValid leaf757CoversExact leaf757LowerChecked

private noncomputable def leaf758Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf758Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (65531/65536), upper := (2097156/2097113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (171538093/134217728) }, upper := { exponent := 0, mantissa := (167/128) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194269/4194226) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf758InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf758LocalValidity :
    LeafFacts leaf758Box leaf758Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf758Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097156/2097113) }) = true
      norm_num [leaf758Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf758CertificateValid :
    WideCertificateValid leaf758Box leaf758Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi99ValidityFacts
    leaf758LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf758CoverageChecked :
    coverageCheck (innerAD leaf758Box) leaf758InnerLog = true := by
  rfl'

private theorem leaf758InnerLogValid :
    leaf758InnerLog.Valid 8 (innerAD leaf758Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf758CoverageChecked

private noncomputable def leaf758InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf758InputLogOnePlusV_eq :
    leaf758InputLogOnePlusV = outerEnclosure 24
      (leaf758Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf758RoundedFacts : LeafRoundedFacts 8
    leaf758Certificate.logOnePlusV leaf758InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf758InputLogOnePlusV_eq }

private noncomputable def leaf758Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi99InputQChi innerPair16Input
    leaf758InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf758LowerChecked :
    lowerCheck 24 leaf758Box leaf758Inputs = true := by
  rfl'

private theorem leaf758CoversExact : CoversExact 8
    leaf758Box leaf758Certificate leaf758InnerLog leaf758Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi99RoundedFacts
    innerPair16RoundedFacts leaf758RoundedFacts (by rfl)

private theorem leaf758FlatSound : Sound leaf758Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf758CertificateValid
    leaf758InnerLogValid leaf758CoversExact leaf758LowerChecked

private noncomputable def leaf759Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf759Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (169965325/134217728) }, upper := { exponent := 0, mantissa := (331/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388541/8388458) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf759InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf759LocalValidity :
    LeafFacts leaf759Box leaf759Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf759Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194229) }) = true
      norm_num [leaf759Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf759CertificateValid :
    WideCertificateValid leaf759Box leaf759Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi98ValidityFacts
    leaf759LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf759CoverageChecked :
    coverageCheck (innerAD leaf759Box) leaf759InnerLog = true := by
  rfl'

private theorem leaf759InnerLogValid :
    leaf759InnerLog.Valid 8 (innerAD leaf759Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf759CoverageChecked

private noncomputable def leaf759InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf759InputLogOnePlusV_eq :
    leaf759InputLogOnePlusV = outerEnclosure 24
      (leaf759Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf759RoundedFacts : LeafRoundedFacts 8
    leaf759Certificate.logOnePlusV leaf759InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf759InputLogOnePlusV_eq }

private noncomputable def leaf759Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi98InputQChi innerPair16Input
    leaf759InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf759LowerChecked :
    lowerCheck 24 leaf759Box leaf759Inputs = true := by
  rfl'

private theorem leaf759CoversExact : CoversExact 8
    leaf759Box leaf759Certificate leaf759InnerLog leaf759Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi98RoundedFacts
    innerPair16RoundedFacts leaf759RoundedFacts (by rfl)

private theorem leaf759FlatSound : Sound leaf759Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf759CertificateValid
    leaf759InnerLogValid leaf759CoversExact leaf759LowerChecked

private noncomputable def leaf760Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf760Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (524289/524278) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (172521071/134217728) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1048567/1048556) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf760InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf760LocalValidity :
    LeafFacts leaf760Box leaf760Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf760Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (524289/524278) }) = true
      norm_num [leaf760Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf760CertificateValid :
    WideCertificateValid leaf760Box leaf760Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi99ValidityFacts
    leaf760LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf760CoverageChecked :
    coverageCheck (innerAD leaf760Box) leaf760InnerLog = true := by
  rfl'

private theorem leaf760InnerLogValid :
    leaf760InnerLog.Valid 8 (innerAD leaf760Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf760CoverageChecked

private noncomputable def leaf760InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf760InputLogOnePlusV_eq :
    leaf760InputLogOnePlusV = outerEnclosure 24
      (leaf760Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf760RoundedFacts : LeafRoundedFacts 8
    leaf760Certificate.logOnePlusV leaf760InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf760InputLogOnePlusV_eq }

private noncomputable def leaf760Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi99InputQChi innerPair16Input
    leaf760InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf760LowerChecked :
    lowerCheck 24 leaf760Box leaf760Inputs = true := by
  rfl'

private theorem leaf760CoversExact : CoversExact 8
    leaf760Box leaf760Certificate leaf760InnerLog leaf760Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi99RoundedFacts
    innerPair16RoundedFacts leaf760RoundedFacts (by rfl)

private theorem leaf760FlatSound : Sound leaf760Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf760CertificateValid
    leaf760InnerLogValid leaf760CoversExact leaf760LowerChecked

private noncomputable def component18Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (0), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node0_sound : Sound component18Node0Box :=
  sound_of_literal_split component18Node0Box leaf716Box leaf717Box
    .k (19/8) (by rfl) (by rfl)
    leaf716FlatSound leaf717FlatSound

private noncomputable def component18Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node1_sound : Sound component18Node1Box :=
  sound_of_literal_split component18Node1Box leaf718Box leaf719Box
    .chi (3/128) (by rfl) (by rfl)
    leaf718FlatSound leaf719FlatSound

private noncomputable def component18Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node2_sound : Sound component18Node2Box :=
  sound_of_literal_split component18Node2Box leaf720Box leaf721Box
    .chi (3/128) (by rfl) (by rfl)
    leaf720FlatSound leaf721FlatSound

private noncomputable def component18Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node3_sound : Sound component18Node3Box :=
  sound_of_literal_split component18Node3Box component18Node1Box component18Node2Box
    .k (19/8) (by rfl) (by rfl)
    component18Node1_sound component18Node2_sound

private noncomputable def component18Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node4_sound : Sound component18Node4Box :=
  sound_of_literal_split component18Node4Box component18Node0Box component18Node3Box
    .chi (1/64) (by rfl) (by rfl)
    component18Node0_sound component18Node3_sound

private noncomputable def component18Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node5_sound : Sound component18Node5Box :=
  sound_of_literal_split component18Node5Box leaf722Box leaf723Box
    .chi (5/128) (by rfl) (by rfl)
    leaf722FlatSound leaf723FlatSound

private noncomputable def component18Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node6_sound : Sound component18Node6Box :=
  sound_of_literal_split component18Node6Box leaf725Box leaf726Box
    .k (39/16) (by rfl) (by rfl)
    leaf725FlatSound leaf726FlatSound

private noncomputable def component18Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node7_sound : Sound component18Node7Box :=
  sound_of_literal_split component18Node7Box leaf724Box component18Node6Box
    .chi (5/128) (by rfl) (by rfl)
    leaf724FlatSound component18Node6_sound

private noncomputable def component18Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node8_sound : Sound component18Node8Box :=
  sound_of_literal_split component18Node8Box component18Node5Box component18Node7Box
    .k (19/8) (by rfl) (by rfl)
    component18Node5_sound component18Node7_sound

private noncomputable def component18Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component18Node9_sound : Sound component18Node9Box :=
  sound_of_literal_split component18Node9Box leaf727Box leaf728Box
    .k (37/16) (by rfl) (by rfl)
    leaf727FlatSound leaf728FlatSound

private noncomputable def component18Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component18Node10_sound : Sound component18Node10Box :=
  sound_of_literal_split component18Node10Box leaf729Box leaf730Box
    .k (37/16) (by rfl) (by rfl)
    leaf729FlatSound leaf730FlatSound

private noncomputable def component18Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component18Node11_sound : Sound component18Node11Box :=
  sound_of_literal_split component18Node11Box component18Node9Box component18Node10Box
    .chi (7/128) (by rfl) (by rfl)
    component18Node9_sound component18Node10_sound

private noncomputable def component18Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component18Node12_sound : Sound component18Node12Box :=
  sound_of_literal_split component18Node12Box leaf731Box leaf732Box
    .k (39/16) (by rfl) (by rfl)
    leaf731FlatSound leaf732FlatSound

private noncomputable def component18Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component18Node13_sound : Sound component18Node13Box :=
  sound_of_literal_split component18Node13Box leaf733Box leaf734Box
    .k (39/16) (by rfl) (by rfl)
    leaf733FlatSound leaf734FlatSound

private noncomputable def component18Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component18Node14_sound : Sound component18Node14Box :=
  sound_of_literal_split component18Node14Box component18Node12Box component18Node13Box
    .chi (7/128) (by rfl) (by rfl)
    component18Node12_sound component18Node13_sound

private noncomputable def component18Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component18Node15_sound : Sound component18Node15Box :=
  sound_of_literal_split component18Node15Box component18Node11Box component18Node14Box
    .k (19/8) (by rfl) (by rfl)
    component18Node11_sound component18Node14_sound

private noncomputable def component18Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component18Node16_sound : Sound component18Node16Box :=
  sound_of_literal_split component18Node16Box component18Node8Box component18Node15Box
    .chi (3/64) (by rfl) (by rfl)
    component18Node8_sound component18Node15_sound

private noncomputable def component18Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component18Node17_sound : Sound component18Node17Box :=
  sound_of_literal_split component18Node17Box component18Node4Box component18Node16Box
    .chi (1/32) (by rfl) (by rfl)
    component18Node4_sound component18Node16_sound

private noncomputable def component18Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node18_sound : Sound component18Node18Box :=
  sound_of_literal_split component18Node18Box leaf735Box leaf736Box
    .k (37/16) (by rfl) (by rfl)
    leaf735FlatSound leaf736FlatSound

private noncomputable def component18Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node19_sound : Sound component18Node19Box :=
  sound_of_literal_split component18Node19Box leaf737Box leaf738Box
    .k (37/16) (by rfl) (by rfl)
    leaf737FlatSound leaf738FlatSound

private noncomputable def component18Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node20_sound : Sound component18Node20Box :=
  sound_of_literal_split component18Node20Box component18Node18Box component18Node19Box
    .chi (5/64) (by rfl) (by rfl)
    component18Node18_sound component18Node19_sound

private noncomputable def component18Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node21_sound : Sound component18Node21Box :=
  sound_of_literal_split component18Node21Box leaf739Box leaf740Box
    .k (39/16) (by rfl) (by rfl)
    leaf739FlatSound leaf740FlatSound

private noncomputable def component18Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node22_sound : Sound component18Node22Box :=
  sound_of_literal_split component18Node22Box leaf741Box leaf742Box
    .chi (11/128) (by rfl) (by rfl)
    leaf741FlatSound leaf742FlatSound

private noncomputable def component18Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node23_sound : Sound component18Node23Box :=
  sound_of_literal_split component18Node23Box leaf743Box leaf744Box
    .chi (11/128) (by rfl) (by rfl)
    leaf743FlatSound leaf744FlatSound

private noncomputable def component18Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node24_sound : Sound component18Node24Box :=
  sound_of_literal_split component18Node24Box component18Node22Box component18Node23Box
    .k (39/16) (by rfl) (by rfl)
    component18Node22_sound component18Node23_sound

private noncomputable def component18Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node25_sound : Sound component18Node25Box :=
  sound_of_literal_split component18Node25Box component18Node21Box component18Node24Box
    .chi (5/64) (by rfl) (by rfl)
    component18Node21_sound component18Node24_sound

private noncomputable def component18Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component18Node26_sound : Sound component18Node26Box :=
  sound_of_literal_split component18Node26Box component18Node20Box component18Node25Box
    .k (19/8) (by rfl) (by rfl)
    component18Node20_sound component18Node25_sound

private noncomputable def component18Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node27_sound : Sound component18Node27Box :=
  sound_of_literal_split component18Node27Box leaf745Box leaf746Box
    .chi (13/128) (by rfl) (by rfl)
    leaf745FlatSound leaf746FlatSound

private noncomputable def component18Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node28_sound : Sound component18Node28Box :=
  sound_of_literal_split component18Node28Box leaf747Box leaf748Box
    .chi (13/128) (by rfl) (by rfl)
    leaf747FlatSound leaf748FlatSound

private noncomputable def component18Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node29_sound : Sound component18Node29Box :=
  sound_of_literal_split component18Node29Box component18Node27Box component18Node28Box
    .k (37/16) (by rfl) (by rfl)
    component18Node27_sound component18Node28_sound

private noncomputable def component18Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node30_sound : Sound component18Node30Box :=
  sound_of_literal_split component18Node30Box leaf749Box leaf750Box
    .chi (15/128) (by rfl) (by rfl)
    leaf749FlatSound leaf750FlatSound

private noncomputable def component18Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node31_sound : Sound component18Node31Box :=
  sound_of_literal_split component18Node31Box leaf751Box leaf752Box
    .chi (15/128) (by rfl) (by rfl)
    leaf751FlatSound leaf752FlatSound

private noncomputable def component18Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node32_sound : Sound component18Node32Box :=
  sound_of_literal_split component18Node32Box component18Node30Box component18Node31Box
    .k (37/16) (by rfl) (by rfl)
    component18Node30_sound component18Node31_sound

private noncomputable def component18Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node33_sound : Sound component18Node33Box :=
  sound_of_literal_split component18Node33Box component18Node29Box component18Node32Box
    .chi (7/64) (by rfl) (by rfl)
    component18Node29_sound component18Node32_sound

private noncomputable def component18Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node34_sound : Sound component18Node34Box :=
  sound_of_literal_split component18Node34Box leaf753Box leaf754Box
    .chi (13/128) (by rfl) (by rfl)
    leaf753FlatSound leaf754FlatSound

private noncomputable def component18Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node35_sound : Sound component18Node35Box :=
  sound_of_literal_split component18Node35Box leaf755Box leaf756Box
    .chi (13/128) (by rfl) (by rfl)
    leaf755FlatSound leaf756FlatSound

private noncomputable def component18Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component18Node36_sound : Sound component18Node36Box :=
  sound_of_literal_split component18Node36Box component18Node34Box component18Node35Box
    .k (39/16) (by rfl) (by rfl)
    component18Node34_sound component18Node35_sound

private noncomputable def component18Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node37_sound : Sound component18Node37Box :=
  sound_of_literal_split component18Node37Box leaf757Box leaf758Box
    .chi (15/128) (by rfl) (by rfl)
    leaf757FlatSound leaf758FlatSound

private noncomputable def component18Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node38_sound : Sound component18Node38Box :=
  sound_of_literal_split component18Node38Box leaf759Box leaf760Box
    .chi (15/128) (by rfl) (by rfl)
    leaf759FlatSound leaf760FlatSound

private noncomputable def component18Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node39_sound : Sound component18Node39Box :=
  sound_of_literal_split component18Node39Box component18Node37Box component18Node38Box
    .k (39/16) (by rfl) (by rfl)
    component18Node37_sound component18Node38_sound

private noncomputable def component18Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node40_sound : Sound component18Node40Box :=
  sound_of_literal_split component18Node40Box component18Node36Box component18Node39Box
    .chi (7/64) (by rfl) (by rfl)
    component18Node36_sound component18Node39_sound

private noncomputable def component18Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node41_sound : Sound component18Node41Box :=
  sound_of_literal_split component18Node41Box component18Node33Box component18Node40Box
    .k (19/8) (by rfl) (by rfl)
    component18Node33_sound component18Node40_sound

private noncomputable def component18Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component18Node42_sound : Sound component18Node42Box :=
  sound_of_literal_split component18Node42Box component18Node26Box component18Node41Box
    .chi (3/32) (by rfl) (by rfl)
    component18Node26_sound component18Node41_sound

noncomputable def component18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component18_sound : Sound component18Box :=
  sound_of_literal_split component18Box component18Node17Box component18Node42Box
    .chi (1/16) (by rfl) (by rfl)
    component18Node17_sound component18Node42_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
