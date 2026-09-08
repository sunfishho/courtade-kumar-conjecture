import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf916Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (0), chiHi := (1/64) }

private noncomputable def leaf916Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554475/33554432) }, vSqrt := { lower := (32765/32768), upper := (8388640/8388587) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (33521623/16777216) }, upper := { exponent := 0, mantissa := (533/512) } }, logOuter := sk87LogOuterCertificate, logK := sk87LogKCertificate, logChi := chi100LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777227/16777174) } }, logDArg := sk87LogDArgCertificate }

private noncomputable def leaf916InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf916LocalValidity :
    LeafFacts leaf916Box leaf916Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf916Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388640/8388587) }) = true
      norm_num [leaf916Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf916CertificateValid :
    WideCertificateValid leaf916Box leaf916Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk87ValidityFacts chi100ValidityFacts
    leaf916LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf916CoverageChecked :
    coverageCheck (innerAD leaf916Box) leaf916InnerLog = true := by
  rfl'

private theorem leaf916InnerLogValid :
    leaf916InnerLog.Valid 8 (innerAD leaf916Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf916CoverageChecked

private noncomputable def leaf916InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814567/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf916InputLogOnePlusV_eq :
    leaf916InputLogOnePlusV = outerEnclosure 24
      (leaf916Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf916RoundedFacts : LeafRoundedFacts 8
    leaf916Certificate.logOnePlusV leaf916InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf916InputLogOnePlusV_eq }

private noncomputable def leaf916Inputs : Inputs :=
  inputsOfCaches globalInput sk87RoundedInputs
    chi100InputQChi innerPair1Input
    leaf916InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf916LowerChecked :
    lowerCheck 24 leaf916Box leaf916Inputs = true := by
  rfl'

private theorem leaf916CoversExact : CoversExact 8
    leaf916Box leaf916Certificate leaf916InnerLog leaf916Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk87RoundedFacts chi100RoundedFacts
    innerPair1RoundedFacts leaf916RoundedFacts (by rfl)

private theorem leaf916FlatSound : Sound leaf916Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf916CertificateValid
    leaf916InnerLogValid leaf916CoversExact leaf916LowerChecked

private noncomputable def leaf917Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (0), chiHi := (1/64) }

private noncomputable def leaf917Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554477/33554432) }, vSqrt := { lower := (32765/32768), upper := (4194320/4194293) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (33521621/16777216) }, upper := { exponent := 0, mantissa := (267/256) } }, logOuter := sk88LogOuterCertificate, logK := sk88LogKCertificate, logChi := chi100LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388613/8388586) } }, logDArg := sk88LogDArgCertificate }

private noncomputable def leaf917InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf917LocalValidity :
    LeafFacts leaf917Box leaf917Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf917Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194320/4194293) }) = true
      norm_num [leaf917Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf917CertificateValid :
    WideCertificateValid leaf917Box leaf917Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk88ValidityFacts chi100ValidityFacts
    leaf917LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf917CoverageChecked :
    coverageCheck (innerAD leaf917Box) leaf917InnerLog = true := by
  rfl'

private theorem leaf917InnerLogValid :
    leaf917InnerLog.Valid 8 (innerAD leaf917Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf917CoverageChecked

private noncomputable def leaf917InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629135/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf917InputLogOnePlusV_eq :
    leaf917InputLogOnePlusV = outerEnclosure 24
      (leaf917Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf917RoundedFacts : LeafRoundedFacts 8
    leaf917Certificate.logOnePlusV leaf917InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf917InputLogOnePlusV_eq }

private noncomputable def leaf917Inputs : Inputs :=
  inputsOfCaches globalInput sk88RoundedInputs
    chi100InputQChi innerPair1Input
    leaf917InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf917LowerChecked :
    lowerCheck 24 leaf917Box leaf917Inputs = true := by
  rfl'

private theorem leaf917CoversExact : CoversExact 8
    leaf917Box leaf917Certificate leaf917InnerLog leaf917Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk88RoundedFacts chi100RoundedFacts
    innerPair1RoundedFacts leaf917RoundedFacts (by rfl)

private theorem leaf917FlatSound : Sound leaf917Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf917CertificateValid
    leaf917InnerLogValid leaf917CoversExact leaf917LowerChecked

private noncomputable def leaf918Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf918Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108911/67108864) }, vSqrt := { lower := (32765/32768), upper := (16777280/16777153) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (69697331/67108864) }, upper := { exponent := 0, mantissa := (1087/1024) } }, logOuter := sk87LogOuterCertificate, logK := sk87LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554433/33554306) } }, logDArg := sk87LogDArgCertificate }

private noncomputable def leaf918InnerLog : WideLogData :=
  innerPair10Data

set_option maxRecDepth 1000000 in
private theorem leaf918LocalValidity :
    LeafFacts leaf918Box leaf918Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf918Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777280/16777153) }) = true
      norm_num [leaf918Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf918CertificateValid :
    WideCertificateValid leaf918Box leaf918Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk87ValidityFacts chi101ValidityFacts
    leaf918LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf918CoverageChecked :
    coverageCheck (innerAD leaf918Box) leaf918InnerLog = true := by
  rfl'

private theorem leaf918InnerLogValid :
    leaf918InnerLog.Valid 8 (innerAD leaf918Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint2PositiveFacts.valid leaf918CoverageChecked

private noncomputable def leaf918InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453643/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf918InputLogOnePlusV_eq :
    leaf918InputLogOnePlusV = outerEnclosure 24
      (leaf918Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf918RoundedFacts : LeafRoundedFacts 8
    leaf918Certificate.logOnePlusV leaf918InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf918InputLogOnePlusV_eq }

private noncomputable def leaf918Inputs : Inputs :=
  inputsOfCaches globalInput sk87RoundedInputs
    chi101InputQChi innerPair10Input
    leaf918InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf918LowerChecked :
    lowerCheck 24 leaf918Box leaf918Inputs = true := by
  rfl'

private theorem leaf918CoversExact : CoversExact 8
    leaf918Box leaf918Certificate leaf918InnerLog leaf918Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk87RoundedFacts chi101RoundedFacts
    innerPair10RoundedFacts leaf918RoundedFacts (by rfl)

private theorem leaf918FlatSound : Sound leaf918Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf918CertificateValid
    leaf918InnerLogValid leaf918CoversExact leaf918LowerChecked

private noncomputable def leaf919Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/128), chiHi := (1/32) }

private noncomputable def leaf919Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108913/67108864) }, vSqrt := { lower := (32765/32768), upper := (113360/113359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71007969/67108864) }, upper := { exponent := 0, mantissa := (277/256) } }, logOuter := sk87LogOuterCertificate, logK := sk87LogKCertificate, logChi := chi102LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (226719/226718) } }, logDArg := sk87LogDArgCertificate }

private noncomputable def leaf919InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf919LocalValidity :
    LeafFacts leaf919Box leaf919Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf919Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (113360/113359) }) = true
      norm_num [leaf919Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf919CertificateValid :
    WideCertificateValid leaf919Box leaf919Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk87ValidityFacts chi102ValidityFacts
    leaf919LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf919CoverageChecked :
    coverageCheck (innerAD leaf919Box) leaf919InnerLog = true := by
  rfl'

private theorem leaf919InnerLogValid :
    leaf919InnerLog.Valid 8 (innerAD leaf919Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf919CoverageChecked

private noncomputable def leaf919InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf919InputLogOnePlusV_eq :
    leaf919InputLogOnePlusV = outerEnclosure 24
      (leaf919Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf919RoundedFacts : LeafRoundedFacts 8
    leaf919Certificate.logOnePlusV leaf919InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf919InputLogOnePlusV_eq }

private noncomputable def leaf919Inputs : Inputs :=
  inputsOfCaches globalInput sk87RoundedInputs
    chi102InputQChi innerPair9Input
    leaf919InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf919LowerChecked :
    lowerCheck 24 leaf919Box leaf919Inputs = true := by
  rfl'

private theorem leaf919CoversExact : CoversExact 8
    leaf919Box leaf919Certificate leaf919InnerLog leaf919Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk87RoundedFacts chi102RoundedFacts
    innerPair9RoundedFacts leaf919RoundedFacts (by rfl)

private theorem leaf919FlatSound : Sound leaf919Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf919CertificateValid
    leaf919InnerLogValid leaf919CoversExact leaf919LowerChecked

private noncomputable def leaf920Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf920Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108913/67108864) }, vSqrt := { lower := (32765/32768), upper := (129056/129055) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (69828393/67108864) }, upper := { exponent := 0, mantissa := (545/512) } }, logOuter := sk88LogOuterCertificate, logK := sk88LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (258111/258110) } }, logDArg := sk88LogDArgCertificate }

private noncomputable def leaf920InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf920LocalValidity :
    LeafFacts leaf920Box leaf920Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf920Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (129056/129055) }) = true
      norm_num [leaf920Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf920CertificateValid :
    WideCertificateValid leaf920Box leaf920Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk88ValidityFacts chi101ValidityFacts
    leaf920LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf920CoverageChecked :
    coverageCheck (innerAD leaf920Box) leaf920InnerLog = true := by
  rfl'

private theorem leaf920InnerLogValid :
    leaf920InnerLog.Valid 8 (innerAD leaf920Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf920CoverageChecked

private noncomputable def leaf920InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814573/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf920InputLogOnePlusV_eq :
    leaf920InputLogOnePlusV = outerEnclosure 24
      (leaf920Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf920RoundedFacts : LeafRoundedFacts 8
    leaf920Certificate.logOnePlusV leaf920InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf920InputLogOnePlusV_eq }

private noncomputable def leaf920Inputs : Inputs :=
  inputsOfCaches globalInput sk88RoundedInputs
    chi101InputQChi innerPair9Input
    leaf920InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf920LowerChecked :
    lowerCheck 24 leaf920Box leaf920Inputs = true := by
  rfl'

private theorem leaf920CoversExact : CoversExact 8
    leaf920Box leaf920Certificate leaf920InnerLog leaf920Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk88RoundedFacts chi101RoundedFacts
    innerPair9RoundedFacts leaf920RoundedFacts (by rfl)

private theorem leaf920FlatSound : Sound leaf920Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf920CertificateValid
    leaf920InnerLogValid leaf920CoversExact leaf920LowerChecked

private noncomputable def leaf921Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/128), chiHi := (1/32) }

private noncomputable def leaf921Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108915/67108864) }, vSqrt := { lower := (32765/32768), upper := (2097160/2097141) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71204563/67108864) }, upper := { exponent := 0, mantissa := (139/128) } }, logOuter := sk88LogOuterCertificate, logK := sk88LogKCertificate, logChi := chi102LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194301/4194282) } }, logDArg := sk88LogDArgCertificate }

private noncomputable def leaf921InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf921LocalValidity :
    LeafFacts leaf921Box leaf921Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf921Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097160/2097141) }) = true
      norm_num [leaf921Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf921CertificateValid :
    WideCertificateValid leaf921Box leaf921Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk88ValidityFacts chi102ValidityFacts
    leaf921LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf921CoverageChecked :
    coverageCheck (innerAD leaf921Box) leaf921InnerLog = true := by
  rfl'

private theorem leaf921InnerLogValid :
    leaf921InnerLog.Valid 8 (innerAD leaf921Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf921CoverageChecked

private noncomputable def leaf921InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf921InputLogOnePlusV_eq :
    leaf921InputLogOnePlusV = outerEnclosure 24
      (leaf921Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf921RoundedFacts : LeafRoundedFacts 8
    leaf921Certificate.logOnePlusV leaf921InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf921InputLogOnePlusV_eq }

private noncomputable def leaf921Inputs : Inputs :=
  inputsOfCaches globalInput sk88RoundedInputs
    chi102InputQChi innerPair9Input
    leaf921InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf921LowerChecked :
    lowerCheck 24 leaf921Box leaf921Inputs = true := by
  rfl'

private theorem leaf921CoversExact : CoversExact 8
    leaf921Box leaf921Certificate leaf921InnerLog leaf921Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk88RoundedFacts chi102RoundedFacts
    innerPair9RoundedFacts leaf921RoundedFacts (by rfl)

private theorem leaf921FlatSound : Sound leaf921Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf921CertificateValid
    leaf921InnerLogValid leaf921CoversExact leaf921LowerChecked

private noncomputable def leaf922Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf922Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108915/67108864) }, vSqrt := { lower := (32765/32768), upper := (1290560/1290547) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72318607/67108864) }, upper := { exponent := 0, mantissa := (1129/1024) } }, logOuter := sk87LogOuterCertificate, logK := sk87LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2581107/2581094) } }, logDArg := sk87LogDArgCertificate }

private noncomputable def leaf922InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf922LocalValidity :
    LeafFacts leaf922Box leaf922Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf922Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1290560/1290547) }) = true
      norm_num [leaf922Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf922CertificateValid :
    WideCertificateValid leaf922Box leaf922Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk87ValidityFacts chi38ValidityFacts
    leaf922LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf922CoverageChecked :
    coverageCheck (innerAD leaf922Box) leaf922InnerLog = true := by
  rfl'

private theorem leaf922InnerLogValid :
    leaf922InnerLog.Valid 8 (innerAD leaf922Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf922CoverageChecked

private noncomputable def leaf922InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf922InputLogOnePlusV_eq :
    leaf922InputLogOnePlusV = outerEnclosure 24
      (leaf922Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf922RoundedFacts : LeafRoundedFacts 8
    leaf922Certificate.logOnePlusV leaf922InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf922InputLogOnePlusV_eq }

private noncomputable def leaf922Inputs : Inputs :=
  inputsOfCaches globalInput sk87RoundedInputs
    chi38InputQChi innerPair5Input
    leaf922InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf922LowerChecked :
    lowerCheck 24 leaf922Box leaf922Inputs = true := by
  rfl'

private theorem leaf922CoversExact : CoversExact 8
    leaf922Box leaf922Certificate leaf922InnerLog leaf922Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk87RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf922RoundedFacts (by rfl)

private theorem leaf922FlatSound : Sound leaf922Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf922CertificateValid
    leaf922InnerLogValid leaf922CoversExact leaf922LowerChecked

private noncomputable def leaf923Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf923Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217821/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777093) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (147291269/134217728) }, upper := { exponent := 0, mantissa := (1147/1024) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554341/33554186) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf923InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf923LocalValidity :
    LeafFacts leaf923Box leaf923Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf923Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777093) }) = true
      norm_num [leaf923Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf923CertificateValid :
    WideCertificateValid leaf923Box leaf923Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi39ValidityFacts
    leaf923LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf923CoverageChecked :
    coverageCheck (innerAD leaf923Box) leaf923InnerLog = true := by
  rfl'

private theorem leaf923InnerLogValid :
    leaf923InnerLog.Valid 8 (innerAD leaf923Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf923CoverageChecked

private noncomputable def leaf923InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf923InputLogOnePlusV_eq :
    leaf923InputLogOnePlusV = outerEnclosure 24
      (leaf923Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf923RoundedFacts : LeafRoundedFacts 8
    leaf923Certificate.logOnePlusV leaf923InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf923InputLogOnePlusV_eq }

private noncomputable def leaf923Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi39InputQChi innerPair5Input
    leaf923InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf923LowerChecked :
    lowerCheck 24 leaf923Box leaf923Inputs = true := by
  rfl'

private theorem leaf923CoversExact : CoversExact 8
    leaf923Box leaf923Certificate leaf923InnerLog leaf923Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf923RoundedFacts (by rfl)

private theorem leaf923FlatSound : Sound leaf923Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf923CertificateValid
    leaf923InnerLogValid leaf923CoversExact leaf923LowerChecked

private noncomputable def leaf924Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf924Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217823/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388545) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (147618927/134217728) }, upper := { exponent := 0, mantissa := (575/512) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777169/16777090) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf924InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf924LocalValidity :
    LeafFacts leaf924Box leaf924Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf924Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388545) }) = true
      norm_num [leaf924Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf924CertificateValid :
    WideCertificateValid leaf924Box leaf924Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi39ValidityFacts
    leaf924LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf924CoverageChecked :
    coverageCheck (innerAD leaf924Box) leaf924InnerLog = true := by
  rfl'

private theorem leaf924InnerLogValid :
    leaf924InnerLog.Valid 8 (innerAD leaf924Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf924CoverageChecked

private noncomputable def leaf924InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf924InputLogOnePlusV_eq :
    leaf924InputLogOnePlusV = outerEnclosure 24
      (leaf924Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf924RoundedFacts : LeafRoundedFacts 8
    leaf924Certificate.logOnePlusV leaf924InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf924InputLogOnePlusV_eq }

private noncomputable def leaf924Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi39InputQChi innerPair5Input
    leaf924InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf924LowerChecked :
    lowerCheck 24 leaf924Box leaf924Inputs = true := by
  rfl'

private theorem leaf924CoversExact : CoversExact 8
    leaf924Box leaf924Certificate leaf924InnerLog leaf924Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf924RoundedFacts (by rfl)

private theorem leaf924FlatSound : Sound leaf924Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf924CertificateValid
    leaf924InnerLogValid leaf924CoversExact leaf924LowerChecked

private noncomputable def leaf925Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf925Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217823/134217728) }, vSqrt := { lower := (32765/32768), upper := (11184832/11184739) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145194243/134217728) }, upper := { exponent := 0, mantissa := (2263/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22369571/22369478) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf925InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf925LocalValidity :
    LeafFacts leaf925Box leaf925Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf925Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11184832/11184739) }) = true
      norm_num [leaf925Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf925CertificateValid :
    WideCertificateValid leaf925Box leaf925Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi38ValidityFacts
    leaf925LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf925CoverageChecked :
    coverageCheck (innerAD leaf925Box) leaf925InnerLog = true := by
  rfl'

private theorem leaf925InnerLogValid :
    leaf925InnerLog.Valid 8 (innerAD leaf925Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf925CoverageChecked

private noncomputable def leaf925InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814575/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf925InputLogOnePlusV_eq :
    leaf925InputLogOnePlusV = outerEnclosure 24
      (leaf925Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf925RoundedFacts : LeafRoundedFacts 8
    leaf925Certificate.logOnePlusV leaf925InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf925InputLogOnePlusV_eq }

private noncomputable def leaf925Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi38InputQChi innerPair5Input
    leaf925InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf925LowerChecked :
    lowerCheck 24 leaf925Box leaf925Inputs = true := by
  rfl'

private theorem leaf925CoversExact : CoversExact 8
    leaf925Box leaf925Certificate leaf925InnerLog leaf925Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf925RoundedFacts (by rfl)

private theorem leaf925FlatSound : Sound leaf925Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf925CertificateValid
    leaf925InnerLogValid leaf925CoversExact leaf925LowerChecked

private noncomputable def leaf926Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf926Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217825/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145456369/134217728) }, upper := { exponent := 0, mantissa := (567/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777177/16777106) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf926InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf926LocalValidity :
    LeafFacts leaf926Box leaf926Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf926Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388553) }) = true
      norm_num [leaf926Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf926CertificateValid :
    WideCertificateValid leaf926Box leaf926Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi38ValidityFacts
    leaf926LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf926CoverageChecked :
    coverageCheck (innerAD leaf926Box) leaf926InnerLog = true := by
  rfl'

private theorem leaf926InnerLogValid :
    leaf926InnerLog.Valid 8 (innerAD leaf926Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf926CoverageChecked

private noncomputable def leaf926InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363411/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf926InputLogOnePlusV_eq :
    leaf926InputLogOnePlusV = outerEnclosure 24
      (leaf926Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf926RoundedFacts : LeafRoundedFacts 8
    leaf926Certificate.logOnePlusV leaf926InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf926InputLogOnePlusV_eq }

private noncomputable def leaf926Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi38InputQChi innerPair5Input
    leaf926InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf926LowerChecked :
    lowerCheck 24 leaf926Box leaf926Inputs = true := by
  rfl'

private theorem leaf926CoversExact : CoversExact 8
    leaf926Box leaf926Certificate leaf926InnerLog leaf926Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf926RoundedFacts (by rfl)

private theorem leaf926FlatSound : Sound leaf926Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf926CertificateValid
    leaf926InnerLogValid leaf926CoversExact leaf926LowerChecked

private noncomputable def leaf927Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf927Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217825/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777087) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (147946585/134217728) }, upper := { exponent := 0, mantissa := (1153/1024) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554335/33554174) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf927InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf927LocalValidity :
    LeafFacts leaf927Box leaf927Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf927Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777087) }) = true
      norm_num [leaf927Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf927CertificateValid :
    WideCertificateValid leaf927Box leaf927Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi39ValidityFacts
    leaf927LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf927CoverageChecked :
    coverageCheck (innerAD leaf927Box) leaf927InnerLog = true := by
  rfl'

private theorem leaf927InnerLogValid :
    leaf927InnerLog.Valid 8 (innerAD leaf927Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf927CoverageChecked

private noncomputable def leaf927InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf927InputLogOnePlusV_eq :
    leaf927InputLogOnePlusV = outerEnclosure 24
      (leaf927Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf927RoundedFacts : LeafRoundedFacts 8
    leaf927Certificate.logOnePlusV leaf927InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf927InputLogOnePlusV_eq }

private noncomputable def leaf927Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi39InputQChi innerPair6Input
    leaf927InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf927LowerChecked :
    lowerCheck 24 leaf927Box leaf927Inputs = true := by
  rfl'

private theorem leaf927CoversExact : CoversExact 8
    leaf927Box leaf927Certificate leaf927InnerLog leaf927Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf927RoundedFacts (by rfl)

private theorem leaf927FlatSound : Sound leaf927Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf927CertificateValid
    leaf927InnerLogValid leaf927CoversExact leaf927LowerChecked

private noncomputable def leaf928Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf928Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194271) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (148274243/134217728) }, upper := { exponent := 0, mantissa := (289/256) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388583/8388542) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf928InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf928LocalValidity :
    LeafFacts leaf928Box leaf928Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf928Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194271) }) = true
      norm_num [leaf928Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf928CertificateValid :
    WideCertificateValid leaf928Box leaf928Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi39ValidityFacts
    leaf928LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf928CoverageChecked :
    coverageCheck (innerAD leaf928Box) leaf928InnerLog = true := by
  rfl'

private theorem leaf928InnerLogValid :
    leaf928InnerLog.Valid 8 (innerAD leaf928Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf928CoverageChecked

private noncomputable def leaf928InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf928InputLogOnePlusV_eq :
    leaf928InputLogOnePlusV = outerEnclosure 24
      (leaf928Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf928RoundedFacts : LeafRoundedFacts 8
    leaf928Certificate.logOnePlusV leaf928InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf928InputLogOnePlusV_eq }

private noncomputable def leaf928Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi39InputQChi innerPair6Input
    leaf928InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf928LowerChecked :
    lowerCheck 24 leaf928Box leaf928Inputs = true := by
  rfl'

private theorem leaf928CoversExact : CoversExact 8
    leaf928Box leaf928Certificate leaf928InnerLog leaf928Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf928RoundedFacts (by rfl)

private theorem leaf928FlatSound : Sound leaf928Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf928CertificateValid
    leaf928InnerLogValid leaf928CoversExact leaf928LowerChecked

private noncomputable def leaf929Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf929Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217823/134217728) }, vSqrt := { lower := (32765/32768), upper := (11184832/11184715) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (149912547/134217728) }, upper := { exponent := 0, mantissa := (2335/2048) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22369547/22369430) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf929InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf929LocalValidity :
    LeafFacts leaf929Box leaf929Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf929Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11184832/11184715) }) = true
      norm_num [leaf929Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf929CertificateValid :
    WideCertificateValid leaf929Box leaf929Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi96ValidityFacts
    leaf929LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf929CoverageChecked :
    coverageCheck (innerAD leaf929Box) leaf929InnerLog = true := by
  rfl'

private theorem leaf929InnerLogValid :
    leaf929InnerLog.Valid 8 (innerAD leaf929Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf929CoverageChecked

private noncomputable def leaf929InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726823/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf929InputLogOnePlusV_eq :
    leaf929InputLogOnePlusV = outerEnclosure 24
      (leaf929Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf929RoundedFacts : LeafRoundedFacts 8
    leaf929Certificate.logOnePlusV leaf929InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf929InputLogOnePlusV_eq }

private noncomputable def leaf929Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi96InputQChi innerPair6Input
    leaf929InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf929LowerChecked :
    lowerCheck 24 leaf929Box leaf929Inputs = true := by
  rfl'

private theorem leaf929CoversExact : CoversExact 8
    leaf929Box leaf929Certificate leaf929InnerLog leaf929Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi96RoundedFacts
    innerPair6RoundedFacts leaf929RoundedFacts (by rfl)

private theorem leaf929FlatSound : Sound leaf929Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf929CertificateValid
    leaf929InnerLogValid leaf929CoversExact leaf929LowerChecked

private noncomputable def leaf930Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf930Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217825/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777069) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (150305737/134217728) }, upper := { exponent := 0, mantissa := (1171/1024) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554317/33554138) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf930InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf930LocalValidity :
    LeafFacts leaf930Box leaf930Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf930Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777069) }) = true
      norm_num [leaf930Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf930CertificateValid :
    WideCertificateValid leaf930Box leaf930Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi96ValidityFacts
    leaf930LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf930CoverageChecked :
    coverageCheck (innerAD leaf930Box) leaf930InnerLog = true := by
  rfl'

private theorem leaf930InnerLogValid :
    leaf930InnerLog.Valid 8 (innerAD leaf930Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf930CoverageChecked

private noncomputable def leaf930InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814585/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf930InputLogOnePlusV_eq :
    leaf930InputLogOnePlusV = outerEnclosure 24
      (leaf930Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf930RoundedFacts : LeafRoundedFacts 8
    leaf930Certificate.logOnePlusV leaf930InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf930InputLogOnePlusV_eq }

private noncomputable def leaf930Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi96InputQChi innerPair6Input
    leaf930InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf930LowerChecked :
    lowerCheck 24 leaf930Box leaf930Inputs = true := by
  rfl'

private theorem leaf930CoversExact : CoversExact 8
    leaf930Box leaf930Certificate leaf930InnerLog leaf930Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi96RoundedFacts
    innerPair6RoundedFacts leaf930RoundedFacts (by rfl)

private theorem leaf930FlatSound : Sound leaf930Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf930CertificateValid
    leaf930InnerLogValid leaf930CoversExact leaf930LowerChecked

private noncomputable def leaf931Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf931Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217825/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194263) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (152533825/134217728) }, upper := { exponent := 0, mantissa := (297/256) } }, logOuter := sk89LogOuterCertificate, logK := sk89LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388575/8388526) } }, logDArg := sk89LogDArgCertificate }

private noncomputable def leaf931InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf931LocalValidity :
    LeafFacts leaf931Box leaf931Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf931Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194263) }) = true
      norm_num [leaf931Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf931CertificateValid :
    WideCertificateValid leaf931Box leaf931Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk89ValidityFacts chi97ValidityFacts
    leaf931LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf931CoverageChecked :
    coverageCheck (innerAD leaf931Box) leaf931InnerLog = true := by
  rfl'

private theorem leaf931InnerLogValid :
    leaf931InnerLog.Valid 8 (innerAD leaf931Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf931CoverageChecked

private noncomputable def leaf931InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629179/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf931InputLogOnePlusV_eq :
    leaf931InputLogOnePlusV = outerEnclosure 24
      (leaf931Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf931RoundedFacts : LeafRoundedFacts 8
    leaf931Certificate.logOnePlusV leaf931InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf931InputLogOnePlusV_eq }

private noncomputable def leaf931Inputs : Inputs :=
  inputsOfCaches globalInput sk89RoundedInputs
    chi97InputQChi innerPair2Input
    leaf931InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf931LowerChecked :
    lowerCheck 24 leaf931Box leaf931Inputs = true := by
  rfl'

private theorem leaf931CoversExact : CoversExact 8
    leaf931Box leaf931Certificate leaf931InnerLog leaf931Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk89RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf931RoundedFacts (by rfl)

private theorem leaf931FlatSound : Sound leaf931Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf931CertificateValid
    leaf931InnerLogValid leaf931CoversExact leaf931LowerChecked

private noncomputable def leaf932Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf932Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (32765/32768), upper := (2097156/2097131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (152992547/134217728) }, upper := { exponent := 0, mantissa := (149/128) } }, logOuter := sk90LogOuterCertificate, logK := sk90LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194287/4194262) } }, logDArg := sk90LogDArgCertificate }

private noncomputable def leaf932InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf932LocalValidity :
    LeafFacts leaf932Box leaf932Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf932Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097156/2097131) }) = true
      norm_num [leaf932Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf932CertificateValid :
    WideCertificateValid leaf932Box leaf932Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk90ValidityFacts chi97ValidityFacts
    leaf932LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf932CoverageChecked :
    coverageCheck (innerAD leaf932Box) leaf932InnerLog = true := by
  rfl'

private theorem leaf932InnerLogValid :
    leaf932InnerLog.Valid 8 (innerAD leaf932Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf932CoverageChecked

private noncomputable def leaf932InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf932InputLogOnePlusV_eq :
    leaf932InputLogOnePlusV = outerEnclosure 24
      (leaf932Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf932RoundedFacts : LeafRoundedFacts 8
    leaf932Certificate.logOnePlusV leaf932InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf932InputLogOnePlusV_eq }

private noncomputable def leaf932Inputs : Inputs :=
  inputsOfCaches globalInput sk90RoundedInputs
    chi97InputQChi innerPair2Input
    leaf932InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf932LowerChecked :
    lowerCheck 24 leaf932Box leaf932Inputs = true := by
  rfl'

private theorem leaf932CoversExact : CoversExact 8
    leaf932Box leaf932Certificate leaf932InnerLog leaf932Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk90RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf932RoundedFacts (by rfl)

private theorem leaf932FlatSound : Sound leaf932Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf932CertificateValid
    leaf932InnerLogValid leaf932CoversExact leaf932LowerChecked

private noncomputable def leaf933Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf933Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (150698927/134217728) }, upper := { exponent := 0, mantissa := (2349/2048) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108627/67108262) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf933InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf933LocalValidity :
    LeafFacts leaf933Box leaf933Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf933Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554131) }) = true
      norm_num [leaf933Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf933CertificateValid :
    WideCertificateValid leaf933Box leaf933Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi96ValidityFacts
    leaf933LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf933CoverageChecked :
    coverageCheck (innerAD leaf933Box) leaf933InnerLog = true := by
  rfl'

private theorem leaf933InnerLogValid :
    leaf933InnerLog.Valid 8 (innerAD leaf933Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf933CoverageChecked

private noncomputable def leaf933InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907293/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf933InputLogOnePlusV_eq :
    leaf933InputLogOnePlusV = outerEnclosure 24
      (leaf933Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf933RoundedFacts : LeafRoundedFacts 8
    leaf933Certificate.logOnePlusV leaf933InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf933InputLogOnePlusV_eq }

private noncomputable def leaf933Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi96InputQChi innerPair6Input
    leaf933InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf933LowerChecked :
    lowerCheck 24 leaf933Box leaf933Inputs = true := by
  rfl'

private theorem leaf933CoversExact : CoversExact 8
    leaf933Box leaf933Certificate leaf933InnerLog leaf933Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi96RoundedFacts
    innerPair6RoundedFacts leaf933RoundedFacts (by rfl)

private theorem leaf933FlatSound : Sound leaf933Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf933CertificateValid
    leaf933InnerLogValid leaf933CoversExact leaf933LowerChecked

private noncomputable def leaf934Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf934Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (32765/32768), upper := (2796208/2796177) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (151092117/134217728) }, upper := { exponent := 0, mantissa := (589/512) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (5592385/5592354) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf934InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf934LocalValidity :
    LeafFacts leaf934Box leaf934Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf934Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2796208/2796177) }) = true
      norm_num [leaf934Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf934CertificateValid :
    WideCertificateValid leaf934Box leaf934Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi96ValidityFacts
    leaf934LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf934CoverageChecked :
    coverageCheck (innerAD leaf934Box) leaf934InnerLog = true := by
  rfl'

private theorem leaf934InnerLogValid :
    leaf934InnerLog.Valid 8 (innerAD leaf934Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf934CoverageChecked

private noncomputable def leaf934InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814587/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf934InputLogOnePlusV_eq :
    leaf934InputLogOnePlusV = outerEnclosure 24
      (leaf934Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf934RoundedFacts : LeafRoundedFacts 8
    leaf934Certificate.logOnePlusV leaf934InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf934InputLogOnePlusV_eq }

private noncomputable def leaf934Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi96InputQChi innerPair2Input
    leaf934InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf934LowerChecked :
    lowerCheck 24 leaf934Box leaf934Inputs = true := by
  rfl'

private theorem leaf934CoversExact : CoversExact 8
    leaf934Box leaf934Certificate leaf934InnerLog leaf934Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf934RoundedFacts (by rfl)

private theorem leaf934FlatSound : Sound leaf934Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf934CertificateValid
    leaf934InnerLogValid leaf934CoversExact leaf934LowerChecked

private noncomputable def leaf935Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf935Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (32765/32768), upper := (1398104/1398087) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (153451269/134217728) }, upper := { exponent := 0, mantissa := (299/256) } }, logOuter := sk91LogOuterCertificate, logK := sk91LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2796191/2796174) } }, logDArg := sk91LogDArgCertificate }

private noncomputable def leaf935InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf935LocalValidity :
    LeafFacts leaf935Box leaf935Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf935Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1398104/1398087) }) = true
      norm_num [leaf935Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf935CertificateValid :
    WideCertificateValid leaf935Box leaf935Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk91ValidityFacts chi97ValidityFacts
    leaf935LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf935CoverageChecked :
    coverageCheck (innerAD leaf935Box) leaf935InnerLog = true := by
  rfl'

private theorem leaf935InnerLogValid :
    leaf935InnerLog.Valid 8 (innerAD leaf935Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf935CoverageChecked

private noncomputable def leaf935InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629183/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf935InputLogOnePlusV_eq :
    leaf935InputLogOnePlusV = outerEnclosure 24
      (leaf935Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf935RoundedFacts : LeafRoundedFacts 8
    leaf935Certificate.logOnePlusV leaf935InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf935InputLogOnePlusV_eq }

private noncomputable def leaf935Inputs : Inputs :=
  inputsOfCaches globalInput sk91RoundedInputs
    chi97InputQChi innerPair2Input
    leaf935InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf935LowerChecked :
    lowerCheck 24 leaf935Box leaf935Inputs = true := by
  rfl'

private theorem leaf935CoversExact : CoversExact 8
    leaf935Box leaf935Certificate leaf935InnerLog leaf935Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk91RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf935RoundedFacts (by rfl)

private theorem leaf935FlatSound : Sound leaf935Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf935CertificateValid
    leaf935InnerLogValid leaf935CoversExact leaf935LowerChecked

private noncomputable def leaf936Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf936Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (1048578/1048565) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (153909991/134217728) }, upper := { exponent := 0, mantissa := (75/64) } }, logOuter := sk92LogOuterCertificate, logK := sk92LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2097143/2097130) } }, logDArg := sk92LogDArgCertificate }

private noncomputable def leaf936InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf936LocalValidity :
    LeafFacts leaf936Box leaf936Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf936Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048578/1048565) }) = true
      norm_num [leaf936Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf936CertificateValid :
    WideCertificateValid leaf936Box leaf936Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk92ValidityFacts chi97ValidityFacts
    leaf936LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf936CoverageChecked :
    coverageCheck (innerAD leaf936Box) leaf936InnerLog = true := by
  rfl'

private theorem leaf936InnerLogValid :
    leaf936InnerLog.Valid 8 (innerAD leaf936Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf936CoverageChecked

private noncomputable def leaf936InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf936InputLogOnePlusV_eq :
    leaf936InputLogOnePlusV = outerEnclosure 24
      (leaf936Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf936RoundedFacts : LeafRoundedFacts 8
    leaf936Certificate.logOnePlusV leaf936InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf936InputLogOnePlusV_eq }

private noncomputable def leaf936Inputs : Inputs :=
  inputsOfCaches globalInput sk92RoundedInputs
    chi97InputQChi innerPair2Input
    leaf936InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf936LowerChecked :
    lowerCheck 24 leaf936Box leaf936Inputs = true := by
  rfl'

private theorem leaf936CoversExact : CoversExact 8
    leaf936Box leaf936Certificate leaf936InnerLog leaf936Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk92RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf936RoundedFacts (by rfl)

private theorem leaf936FlatSound : Sound leaf936Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf936CertificateValid
    leaf936InnerLogValid leaf936CoversExact leaf936LowerChecked

private noncomputable def leaf937Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (0), chiHi := (1/64) }

private noncomputable def leaf937Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554479/33554432) }, vSqrt := { lower := (32765/32768), upper := (1677728/1677717) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (33521619/16777216) }, upper := { exponent := 0, mantissa := (535/512) } }, logOuter := sk93LogOuterCertificate, logK := sk93LogKCertificate, logChi := chi100LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (3355445/3355434) } }, logDArg := sk93LogDArgCertificate }

private noncomputable def leaf937InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf937LocalValidity :
    LeafFacts leaf937Box leaf937Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf937Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1677728/1677717) }) = true
      norm_num [leaf937Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf937CertificateValid :
    WideCertificateValid leaf937Box leaf937Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk93ValidityFacts chi100ValidityFacts
    leaf937LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf937CoverageChecked :
    coverageCheck (innerAD leaf937Box) leaf937InnerLog = true := by
  rfl'

private theorem leaf937InnerLogValid :
    leaf937InnerLog.Valid 8 (innerAD leaf937Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf937CoverageChecked

private noncomputable def leaf937InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726821/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf937InputLogOnePlusV_eq :
    leaf937InputLogOnePlusV = outerEnclosure 24
      (leaf937Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf937RoundedFacts : LeafRoundedFacts 8
    leaf937Certificate.logOnePlusV leaf937InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf937InputLogOnePlusV_eq }

private noncomputable def leaf937Inputs : Inputs :=
  inputsOfCaches globalInput sk93RoundedInputs
    chi100InputQChi innerPair1Input
    leaf937InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf937LowerChecked :
    lowerCheck 24 leaf937Box leaf937Inputs = true := by
  rfl'

private theorem leaf937CoversExact : CoversExact 8
    leaf937Box leaf937Certificate leaf937InnerLog leaf937Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk93RoundedFacts chi100RoundedFacts
    innerPair1RoundedFacts leaf937RoundedFacts (by rfl)

private theorem leaf937FlatSound : Sound leaf937Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf937CertificateValid
    leaf937InnerLogValid leaf937CoversExact leaf937LowerChecked

private noncomputable def leaf938Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (0), chiHi := (1/64) }

private noncomputable def leaf938Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554481/33554432) }, vSqrt := { lower := (65529/65536), upper := (1048580/1048573) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (33521617/16777216) }, upper := { exponent := 0, mantissa := (67/64) } }, logOuter := sk94LogOuterCertificate, logK := sk94LogKCertificate, logChi := chi100LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2097153/2097146) } }, logDArg := sk94LogDArgCertificate }

private noncomputable def leaf938InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf938LocalValidity :
    LeafFacts leaf938Box leaf938Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf938Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048580/1048573) }) = true
      norm_num [leaf938Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf938CertificateValid :
    WideCertificateValid leaf938Box leaf938Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk94ValidityFacts chi100ValidityFacts
    leaf938LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf938CoverageChecked :
    coverageCheck (innerAD leaf938Box) leaf938InnerLog = true := by
  rfl'

private theorem leaf938InnerLogValid :
    leaf938InnerLog.Valid 8 (innerAD leaf938Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf938CoverageChecked

private noncomputable def leaf938InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629137/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf938InputLogOnePlusV_eq :
    leaf938InputLogOnePlusV = outerEnclosure 24
      (leaf938Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf938RoundedFacts : LeafRoundedFacts 8
    leaf938Certificate.logOnePlusV leaf938InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf938InputLogOnePlusV_eq }

private noncomputable def leaf938Inputs : Inputs :=
  inputsOfCaches globalInput sk94RoundedInputs
    chi100InputQChi innerPair1Input
    leaf938InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf938LowerChecked :
    lowerCheck 24 leaf938Box leaf938Inputs = true := by
  rfl'

private theorem leaf938CoversExact : CoversExact 8
    leaf938Box leaf938Certificate leaf938InnerLog leaf938Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk94RoundedFacts chi100RoundedFacts
    innerPair1RoundedFacts leaf938RoundedFacts (by rfl)

private theorem leaf938FlatSound : Sound leaf938Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf938CertificateValid
    leaf938InnerLogValid leaf938CoversExact leaf938LowerChecked

private noncomputable def leaf939Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf939Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108915/67108864) }, vSqrt := { lower := (32765/32768), upper := (16777280/16777147) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (69959455/67108864) }, upper := { exponent := 0, mantissa := (1093/1024) } }, logOuter := sk93LogOuterCertificate, logK := sk93LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554427/33554294) } }, logDArg := sk93LogDArgCertificate }

private noncomputable def leaf939InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf939LocalValidity :
    LeafFacts leaf939Box leaf939Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf939Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777280/16777147) }) = true
      norm_num [leaf939Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf939CertificateValid :
    WideCertificateValid leaf939Box leaf939Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk93ValidityFacts chi101ValidityFacts
    leaf939LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf939CoverageChecked :
    coverageCheck (innerAD leaf939Box) leaf939InnerLog = true := by
  rfl'

private theorem leaf939InnerLogValid :
    leaf939InnerLog.Valid 8 (innerAD leaf939Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf939CoverageChecked

private noncomputable def leaf939InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629147/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf939InputLogOnePlusV_eq :
    leaf939InputLogOnePlusV = outerEnclosure 24
      (leaf939Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf939RoundedFacts : LeafRoundedFacts 8
    leaf939Certificate.logOnePlusV leaf939InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf939InputLogOnePlusV_eq }

private noncomputable def leaf939Inputs : Inputs :=
  inputsOfCaches globalInput sk93RoundedInputs
    chi101InputQChi innerPair9Input
    leaf939InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf939LowerChecked :
    lowerCheck 24 leaf939Box leaf939Inputs = true := by
  rfl'

private theorem leaf939CoversExact : CoversExact 8
    leaf939Box leaf939Certificate leaf939InnerLog leaf939Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk93RoundedFacts chi101RoundedFacts
    innerPair9RoundedFacts leaf939RoundedFacts (by rfl)

private theorem leaf939FlatSound : Sound leaf939Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf939CertificateValid
    leaf939InnerLogValid leaf939CoversExact leaf939LowerChecked

private noncomputable def leaf940Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/128), chiHi := (1/32) }

private noncomputable def leaf940Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108917/67108864) }, vSqrt := { lower := (32765/32768), upper := (322640/322637) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71401157/67108864) }, upper := { exponent := 0, mantissa := (279/256) } }, logOuter := sk93LogOuterCertificate, logK := sk93LogKCertificate, logChi := chi102LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (645277/645274) } }, logDArg := sk93LogDArgCertificate }

private noncomputable def leaf940InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf940LocalValidity :
    LeafFacts leaf940Box leaf940Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf940Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (322640/322637) }) = true
      norm_num [leaf940Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf940CertificateValid :
    WideCertificateValid leaf940Box leaf940Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk93ValidityFacts chi102ValidityFacts
    leaf940LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf940CoverageChecked :
    coverageCheck (innerAD leaf940Box) leaf940InnerLog = true := by
  rfl'

private theorem leaf940InnerLogValid :
    leaf940InnerLog.Valid 8 (innerAD leaf940Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf940CoverageChecked

private noncomputable def leaf940InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629159/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf940InputLogOnePlusV_eq :
    leaf940InputLogOnePlusV = outerEnclosure 24
      (leaf940Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf940RoundedFacts : LeafRoundedFacts 8
    leaf940Certificate.logOnePlusV leaf940InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf940InputLogOnePlusV_eq }

private noncomputable def leaf940Inputs : Inputs :=
  inputsOfCaches globalInput sk93RoundedInputs
    chi102InputQChi innerPair5Input
    leaf940InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf940LowerChecked :
    lowerCheck 24 leaf940Box leaf940Inputs = true := by
  rfl'

private theorem leaf940CoversExact : CoversExact 8
    leaf940Box leaf940Certificate leaf940InnerLog leaf940Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk93RoundedFacts chi102RoundedFacts
    innerPair5RoundedFacts leaf940RoundedFacts (by rfl)

private theorem leaf940FlatSound : Sound leaf940Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf940CertificateValid
    leaf940InnerLogValid leaf940CoversExact leaf940LowerChecked

private noncomputable def leaf941Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/64), chiHi := (3/128) }

private noncomputable def leaf941Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108917/67108864) }, vSqrt := { lower := (65529/65536), upper := (2097160/2097143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (70090517/67108864) }, upper := { exponent := 0, mantissa := (137/128) } }, logOuter := sk94LogOuterCertificate, logK := sk94LogKCertificate, logChi := chi101LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194303/4194286) } }, logDArg := sk94LogDArgCertificate }

private noncomputable def leaf941InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf941LocalValidity :
    LeafFacts leaf941Box leaf941Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf941Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097160/2097143) }) = true
      norm_num [leaf941Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf941CertificateValid :
    WideCertificateValid leaf941Box leaf941Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk94ValidityFacts chi101ValidityFacts
    leaf941LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf941CoverageChecked :
    coverageCheck (innerAD leaf941Box) leaf941InnerLog = true := by
  rfl'

private theorem leaf941InnerLogValid :
    leaf941InnerLog.Valid 8 (innerAD leaf941Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf941CoverageChecked

private noncomputable def leaf941InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629149/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf941InputLogOnePlusV_eq :
    leaf941InputLogOnePlusV = outerEnclosure 24
      (leaf941Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf941RoundedFacts : LeafRoundedFacts 8
    leaf941Certificate.logOnePlusV leaf941InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf941InputLogOnePlusV_eq }

private noncomputable def leaf941Inputs : Inputs :=
  inputsOfCaches globalInput sk94RoundedInputs
    chi101InputQChi innerPair9Input
    leaf941InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf941LowerChecked :
    lowerCheck 24 leaf941Box leaf941Inputs = true := by
  rfl'

private theorem leaf941CoversExact : CoversExact 8
    leaf941Box leaf941Certificate leaf941InnerLog leaf941Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk94RoundedFacts chi101RoundedFacts
    innerPair9RoundedFacts leaf941RoundedFacts (by rfl)

private theorem leaf941FlatSound : Sound leaf941Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf941CertificateValid
    leaf941InnerLogValid leaf941CoversExact leaf941LowerChecked

private noncomputable def leaf942Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/128), chiHi := (7/256) }

private noncomputable def leaf942Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217789/134217728) }, vSqrt := { lower := (65529/65536), upper := (113360/113359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (143228317/134217728) }, upper := { exponent := 0, mantissa := (277/256) } }, logOuter := sk94LogOuterCertificate, logK := sk94LogKCertificate, logChi := chi123LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (226719/226718) } }, logDArg := sk94LogDArgCertificate }

private noncomputable def leaf942InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf942LocalValidity :
    LeafFacts leaf942Box leaf942Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf942Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (113360/113359) }) = true
      norm_num [leaf942Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf942CertificateValid :
    WideCertificateValid leaf942Box leaf942Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk94ValidityFacts chi123ValidityFacts
    leaf942LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf942CoverageChecked :
    coverageCheck (innerAD leaf942Box) leaf942InnerLog = true := by
  rfl'

private theorem leaf942InnerLogValid :
    leaf942InnerLog.Valid 8 (innerAD leaf942Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf942CoverageChecked

private noncomputable def leaf942InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf942InputLogOnePlusV_eq :
    leaf942InputLogOnePlusV = outerEnclosure 24
      (leaf942Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf942RoundedFacts : LeafRoundedFacts 8
    leaf942Certificate.logOnePlusV leaf942InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf942InputLogOnePlusV_eq }

private noncomputable def leaf942Inputs : Inputs :=
  inputsOfCaches globalInput sk94RoundedInputs
    chi123InputQChi innerPair5Input
    leaf942InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf942LowerChecked :
    lowerCheck 24 leaf942Box leaf942Inputs = true := by
  rfl'

private theorem leaf942CoversExact : CoversExact 8
    leaf942Box leaf942Certificate leaf942InnerLog leaf942Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk94RoundedFacts chi123RoundedFacts
    innerPair5RoundedFacts leaf942RoundedFacts (by rfl)

private theorem leaf942FlatSound : Sound leaf942Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf942CertificateValid
    leaf942InnerLogValid leaf942CoversExact leaf942LowerChecked

private noncomputable def leaf943Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/256), chiHi := (1/32) }

private noncomputable def leaf943Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217791/134217728) }, vSqrt := { lower := (65529/65536), upper := (104858/104857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (144735551/134217728) }, upper := { exponent := 0, mantissa := (35/32) } }, logOuter := sk94LogOuterCertificate, logK := sk94LogKCertificate, logChi := chi124LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (209715/209714) } }, logDArg := sk94LogDArgCertificate }

private noncomputable def leaf943InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf943LocalValidity :
    LeafFacts leaf943Box leaf943Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf943Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (104858/104857) }) = true
      norm_num [leaf943Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf943CertificateValid :
    WideCertificateValid leaf943Box leaf943Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk94ValidityFacts chi124ValidityFacts
    leaf943LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf943CoverageChecked :
    coverageCheck (innerAD leaf943Box) leaf943InnerLog = true := by
  rfl'

private theorem leaf943InnerLogValid :
    leaf943InnerLog.Valid 8 (innerAD leaf943Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf943CoverageChecked

private noncomputable def leaf943InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf943InputLogOnePlusV_eq :
    leaf943InputLogOnePlusV = outerEnclosure 24
      (leaf943Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf943RoundedFacts : LeafRoundedFacts 8
    leaf943Certificate.logOnePlusV leaf943InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf943InputLogOnePlusV_eq }

private noncomputable def leaf943Inputs : Inputs :=
  inputsOfCaches globalInput sk94RoundedInputs
    chi124InputQChi innerPair5Input
    leaf943InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf943LowerChecked :
    lowerCheck 24 leaf943Box leaf943Inputs = true := by
  rfl'

private theorem leaf943CoversExact : CoversExact 8
    leaf943Box leaf943Certificate leaf943InnerLog leaf943Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk94RoundedFacts chi124RoundedFacts
    innerPair5RoundedFacts leaf943RoundedFacts (by rfl)

private theorem leaf943FlatSound : Sound leaf943Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf943CertificateValid
    leaf943InnerLogValid leaf943CoversExact leaf943LowerChecked

private noncomputable def leaf944Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf944Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554207) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145718495/134217728) }, upper := { exponent := 0, mantissa := (2273/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108703/67108414) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf944InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf944LocalValidity :
    LeafFacts leaf944Box leaf944Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf944Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554207) }) = true
      norm_num [leaf944Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf944CertificateValid :
    WideCertificateValid leaf944Box leaf944Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi38ValidityFacts
    leaf944LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf944CoverageChecked :
    coverageCheck (innerAD leaf944Box) leaf944InnerLog = true := by
  rfl'

private theorem leaf944InnerLogValid :
    leaf944InnerLog.Valid 8 (innerAD leaf944Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf944CoverageChecked

private noncomputable def leaf944InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf944InputLogOnePlusV_eq :
    leaf944InputLogOnePlusV = outerEnclosure 24
      (leaf944Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf944RoundedFacts : LeafRoundedFacts 8
    leaf944Certificate.logOnePlusV leaf944InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf944InputLogOnePlusV_eq }

private noncomputable def leaf944Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi38InputQChi innerPair5Input
    leaf944InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf944LowerChecked :
    lowerCheck 24 leaf944Box leaf944Inputs = true := by
  rfl'

private theorem leaf944CoversExact : CoversExact 8
    leaf944Box leaf944Certificate leaf944InnerLog leaf944Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf944RoundedFacts (by rfl)

private theorem leaf944FlatSound : Sound leaf944Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf944CertificateValid
    leaf944InnerLogValid leaf944CoversExact leaf944LowerChecked

private noncomputable def leaf945Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf945Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (32765/32768), upper := (5592416/5592367) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (145980621/134217728) }, upper := { exponent := 0, mantissa := (1139/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11184783/11184734) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf945InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf945LocalValidity :
    LeafFacts leaf945Box leaf945Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf945Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5592416/5592367) }) = true
      norm_num [leaf945Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf945CertificateValid :
    WideCertificateValid leaf945Box leaf945Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi38ValidityFacts
    leaf945LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf945CoverageChecked :
    coverageCheck (innerAD leaf945Box) leaf945InnerLog = true := by
  rfl'

private theorem leaf945InnerLogValid :
    leaf945InnerLog.Valid 8 (innerAD leaf945Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf945CoverageChecked

private noncomputable def leaf945InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814577/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf945InputLogOnePlusV_eq :
    leaf945InputLogOnePlusV = outerEnclosure 24
      (leaf945Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf945RoundedFacts : LeafRoundedFacts 8
    leaf945Certificate.logOnePlusV leaf945InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf945InputLogOnePlusV_eq }

private noncomputable def leaf945Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi38InputQChi innerPair5Input
    leaf945InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf945LowerChecked :
    lowerCheck 24 leaf945Box leaf945Inputs = true := by
  rfl'

private theorem leaf945CoversExact : CoversExact 8
    leaf945Box leaf945Certificate leaf945InnerLog leaf945Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf945RoundedFacts (by rfl)

private theorem leaf945FlatSound : Sound leaf945Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf945CertificateValid
    leaf945InnerLogValid leaf945CoversExact leaf945LowerChecked

private noncomputable def leaf946Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf946Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777081) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (148601901/134217728) }, upper := { exponent := 0, mantissa := (1159/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554329/33554162) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf946InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf946LocalValidity :
    LeafFacts leaf946Box leaf946Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf946Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777081) }) = true
      norm_num [leaf946Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf946CertificateValid :
    WideCertificateValid leaf946Box leaf946Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi39ValidityFacts
    leaf946LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf946CoverageChecked :
    coverageCheck (innerAD leaf946Box) leaf946InnerLog = true := by
  rfl'

private theorem leaf946InnerLogValid :
    leaf946InnerLog.Valid 8 (innerAD leaf946Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf946CoverageChecked

private noncomputable def leaf946InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907291/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf946InputLogOnePlusV_eq :
    leaf946InputLogOnePlusV = outerEnclosure 24
      (leaf946Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf946RoundedFacts : LeafRoundedFacts 8
    leaf946Certificate.logOnePlusV leaf946InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf946InputLogOnePlusV_eq }

private noncomputable def leaf946Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi39InputQChi innerPair6Input
    leaf946InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf946LowerChecked :
    lowerCheck 24 leaf946Box leaf946Inputs = true := by
  rfl'

private theorem leaf946CoversExact : CoversExact 8
    leaf946Box leaf946Certificate leaf946InnerLog leaf946Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf946RoundedFacts (by rfl)

private theorem leaf946FlatSound : Sound leaf946Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf946CertificateValid
    leaf946InnerLogValid leaf946CoversExact leaf946LowerChecked

private noncomputable def leaf947Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf947Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388539) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (148929559/134217728) }, upper := { exponent := 0, mantissa := (581/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777163/16777078) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf947InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf947LocalValidity :
    LeafFacts leaf947Box leaf947Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf947Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388539) }) = true
      norm_num [leaf947Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf947CertificateValid :
    WideCertificateValid leaf947Box leaf947Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi39ValidityFacts
    leaf947LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf947CoverageChecked :
    coverageCheck (innerAD leaf947Box) leaf947InnerLog = true := by
  rfl'

private theorem leaf947InnerLogValid :
    leaf947InnerLog.Valid 8 (innerAD leaf947Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf947CoverageChecked

private noncomputable def leaf947InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814583/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf947InputLogOnePlusV_eq :
    leaf947InputLogOnePlusV = outerEnclosure 24
      (leaf947Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf947RoundedFacts : LeafRoundedFacts 8
    leaf947Certificate.logOnePlusV leaf947InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf947InputLogOnePlusV_eq }

private noncomputable def leaf947Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi39InputQChi innerPair6Input
    leaf947InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf947LowerChecked :
    lowerCheck 24 leaf947Box leaf947Inputs = true := by
  rfl'

private theorem leaf947CoversExact : CoversExact 8
    leaf947Box leaf947Certificate leaf947InnerLog leaf947Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf947RoundedFacts (by rfl)

private theorem leaf947FlatSound : Sound leaf947Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf947CertificateValid
    leaf947InnerLogValid leaf947CoversExact leaf947LowerChecked

private noncomputable def leaf948Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf948Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554197) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (146242747/134217728) }, upper := { exponent := 0, mantissa := (2283/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108693/67108394) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf948InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf948LocalValidity :
    LeafFacts leaf948Box leaf948Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf948Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554197) }) = true
      norm_num [leaf948Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf948CertificateValid :
    WideCertificateValid leaf948Box leaf948Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi38ValidityFacts
    leaf948LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf948CoverageChecked :
    coverageCheck (innerAD leaf948Box) leaf948InnerLog = true := by
  rfl'

private theorem leaf948InnerLogValid :
    leaf948InnerLog.Valid 8 (innerAD leaf948Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf948CoverageChecked

private noncomputable def leaf948InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf948InputLogOnePlusV_eq :
    leaf948InputLogOnePlusV = outerEnclosure 24
      (leaf948Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf948RoundedFacts : LeafRoundedFacts 8
    leaf948Certificate.logOnePlusV leaf948InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf948InputLogOnePlusV_eq }

private noncomputable def leaf948Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi38InputQChi innerPair5Input
    leaf948InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf948LowerChecked :
    lowerCheck 24 leaf948Box leaf948Inputs = true := by
  rfl'

private theorem leaf948CoversExact : CoversExact 8
    leaf948Box leaf948Certificate leaf948InnerLog leaf948Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf948RoundedFacts (by rfl)

private theorem leaf948FlatSound : Sound leaf948Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf948CertificateValid
    leaf948InnerLogValid leaf948CoversExact leaf948LowerChecked

private noncomputable def leaf949Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf949Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (146504873/134217728) }, upper := { exponent := 0, mantissa := (143/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194293/4194274) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf949InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf949LocalValidity :
    LeafFacts leaf949Box leaf949Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf949Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097137) }) = true
      norm_num [leaf949Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf949CertificateValid :
    WideCertificateValid leaf949Box leaf949Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi38ValidityFacts
    leaf949LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf949CoverageChecked :
    coverageCheck (innerAD leaf949Box) leaf949InnerLog = true := by
  rfl'

private theorem leaf949InnerLogValid :
    leaf949InnerLog.Valid 8 (innerAD leaf949Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf949CoverageChecked

private noncomputable def leaf949InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf949InputLogOnePlusV_eq :
    leaf949InputLogOnePlusV = outerEnclosure 24
      (leaf949Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf949RoundedFacts : LeafRoundedFacts 8
    leaf949Certificate.logOnePlusV leaf949InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf949InputLogOnePlusV_eq }

private noncomputable def leaf949Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi38InputQChi innerPair5Input
    leaf949InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf949LowerChecked :
    lowerCheck 24 leaf949Box leaf949Inputs = true := by
  rfl'

private theorem leaf949CoversExact : CoversExact 8
    leaf949Box leaf949Certificate leaf949InnerLog leaf949Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf949RoundedFacts (by rfl)

private theorem leaf949FlatSound : Sound leaf949Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf949CertificateValid
    leaf949InnerLogValid leaf949CoversExact leaf949LowerChecked

private noncomputable def leaf950Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf950Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777075) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (149257217/134217728) }, upper := { exponent := 0, mantissa := (1165/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554323/33554150) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf950InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf950LocalValidity :
    LeafFacts leaf950Box leaf950Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf950Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777075) }) = true
      norm_num [leaf950Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf950CertificateValid :
    WideCertificateValid leaf950Box leaf950Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi39ValidityFacts
    leaf950LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf950CoverageChecked :
    coverageCheck (innerAD leaf950Box) leaf950InnerLog = true := by
  rfl'

private theorem leaf950InnerLogValid :
    leaf950InnerLog.Valid 8 (innerAD leaf950Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf950CoverageChecked

private noncomputable def leaf950InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629167/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf950InputLogOnePlusV_eq :
    leaf950InputLogOnePlusV = outerEnclosure 24
      (leaf950Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf950RoundedFacts : LeafRoundedFacts 8
    leaf950Certificate.logOnePlusV leaf950InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf950InputLogOnePlusV_eq }

private noncomputable def leaf950Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi39InputQChi innerPair6Input
    leaf950InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf950LowerChecked :
    lowerCheck 24 leaf950Box leaf950Inputs = true := by
  rfl'

private theorem leaf950CoversExact : CoversExact 8
    leaf950Box leaf950Certificate leaf950InnerLog leaf950Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf950RoundedFacts (by rfl)

private theorem leaf950FlatSound : Sound leaf950Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf950CertificateValid
    leaf950InnerLogValid leaf950CoversExact leaf950LowerChecked

private noncomputable def leaf951Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf951Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (65529/65536), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (149584875/134217728) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf951InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf951LocalValidity :
    LeafFacts leaf951Box leaf951Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf951Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048578/1048567) }) = true
      norm_num [leaf951Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf951CertificateValid :
    WideCertificateValid leaf951Box leaf951Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi39ValidityFacts
    leaf951LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf951CoverageChecked :
    coverageCheck (innerAD leaf951Box) leaf951InnerLog = true := by
  rfl'

private theorem leaf951InnerLogValid :
    leaf951InnerLog.Valid 8 (innerAD leaf951Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf951CoverageChecked

private noncomputable def leaf951InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf951InputLogOnePlusV_eq :
    leaf951InputLogOnePlusV = outerEnclosure 24
      (leaf951Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf951RoundedFacts : LeafRoundedFacts 8
    leaf951Certificate.logOnePlusV leaf951InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf951InputLogOnePlusV_eq }

private noncomputable def leaf951Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi39InputQChi innerPair6Input
    leaf951InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf951LowerChecked :
    lowerCheck 24 leaf951Box leaf951Inputs = true := by
  rfl'

private theorem leaf951CoversExact : CoversExact 8
    leaf951Box leaf951Certificate leaf951InnerLog leaf951Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi39RoundedFacts
    innerPair6RoundedFacts leaf951RoundedFacts (by rfl)

private theorem leaf951FlatSound : Sound leaf951Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf951CertificateValid
    leaf951InnerLogValid leaf951CoversExact leaf951LowerChecked

private noncomputable def leaf952Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf952Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554117) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (151485307/134217728) }, upper := { exponent := 0, mantissa := (2363/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108613/67108234) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf952InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf952LocalValidity :
    LeafFacts leaf952Box leaf952Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf952Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554117) }) = true
      norm_num [leaf952Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf952CertificateValid :
    WideCertificateValid leaf952Box leaf952Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi96ValidityFacts
    leaf952LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf952CoverageChecked :
    coverageCheck (innerAD leaf952Box) leaf952InnerLog = true := by
  rfl'

private theorem leaf952InnerLogValid :
    leaf952InnerLog.Valid 8 (innerAD leaf952Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf952CoverageChecked

private noncomputable def leaf952InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629175/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf952InputLogOnePlusV_eq :
    leaf952InputLogOnePlusV = outerEnclosure 24
      (leaf952Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf952RoundedFacts : LeafRoundedFacts 8
    leaf952Certificate.logOnePlusV leaf952InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf952InputLogOnePlusV_eq }

private noncomputable def leaf952Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi96InputQChi innerPair2Input
    leaf952InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf952LowerChecked :
    lowerCheck 24 leaf952Box leaf952Inputs = true := by
  rfl'

private theorem leaf952CoversExact : CoversExact 8
    leaf952Box leaf952Certificate leaf952InnerLog leaf952Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf952RoundedFacts (by rfl)

private theorem leaf952FlatSound : Sound leaf952Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf952CertificateValid
    leaf952InnerLogValid leaf952CoversExact leaf952LowerChecked

private noncomputable def leaf953Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf953Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777055) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (151878497/134217728) }, upper := { exponent := 0, mantissa := (1185/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554303/33554110) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf953InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf953LocalValidity :
    LeafFacts leaf953Box leaf953Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf953Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777055) }) = true
      norm_num [leaf953Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf953CertificateValid :
    WideCertificateValid leaf953Box leaf953Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi96ValidityFacts
    leaf953LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf953CoverageChecked :
    coverageCheck (innerAD leaf953Box) leaf953InnerLog = true := by
  rfl'

private theorem leaf953InnerLogValid :
    leaf953InnerLog.Valid 8 (innerAD leaf953Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf953CoverageChecked

private noncomputable def leaf953InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629177/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf953InputLogOnePlusV_eq :
    leaf953InputLogOnePlusV = outerEnclosure 24
      (leaf953Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf953RoundedFacts : LeafRoundedFacts 8
    leaf953Certificate.logOnePlusV leaf953InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf953InputLogOnePlusV_eq }

private noncomputable def leaf953Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi96InputQChi innerPair2Input
    leaf953InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf953LowerChecked :
    lowerCheck 24 leaf953Box leaf953Inputs = true := by
  rfl'

private theorem leaf953CoversExact : CoversExact 8
    leaf953Box leaf953Certificate leaf953InnerLog leaf953Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf953RoundedFacts (by rfl)

private theorem leaf953FlatSound : Sound leaf953Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf953CertificateValid
    leaf953InnerLogValid leaf953CoversExact leaf953LowerChecked

private noncomputable def leaf954Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf954Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217833/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (154368713/134217728) }, upper := { exponent := 0, mantissa := (301/256) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388571/8388518) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf954InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf954LocalValidity :
    LeafFacts leaf954Box leaf954Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf954Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194259) }) = true
      norm_num [leaf954Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf954CertificateValid :
    WideCertificateValid leaf954Box leaf954Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi97ValidityFacts
    leaf954LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf954CoverageChecked :
    coverageCheck (innerAD leaf954Box) leaf954InnerLog = true := by
  rfl'

private theorem leaf954InnerLogValid :
    leaf954InnerLog.Valid 8 (innerAD leaf954Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf954CoverageChecked

private noncomputable def leaf954InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629187/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf954InputLogOnePlusV_eq :
    leaf954InputLogOnePlusV = outerEnclosure 24
      (leaf954Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf954RoundedFacts : LeafRoundedFacts 8
    leaf954Certificate.logOnePlusV leaf954InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf954InputLogOnePlusV_eq }

private noncomputable def leaf954Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi97InputQChi innerPair2Input
    leaf954InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf954LowerChecked :
    lowerCheck 24 leaf954Box leaf954Inputs = true := by
  rfl'

private theorem leaf954CoversExact : CoversExact 8
    leaf954Box leaf954Certificate leaf954InnerLog leaf954Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf954RoundedFacts (by rfl)

private theorem leaf954FlatSound : Sound leaf954Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf954CertificateValid
    leaf954InnerLogValid leaf954CoversExact leaf954LowerChecked

private noncomputable def leaf955Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf955Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (699052/699043) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (154827435/134217728) }, upper := { exponent := 0, mantissa := (151/128) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1398095/1398086) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf955InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf955LocalValidity :
    LeafFacts leaf955Box leaf955Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf955Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (699052/699043) }) = true
      norm_num [leaf955Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf955CertificateValid :
    WideCertificateValid leaf955Box leaf955Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi97ValidityFacts
    leaf955LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf955CoverageChecked :
    coverageCheck (innerAD leaf955Box) leaf955InnerLog = true := by
  rfl'

private theorem leaf955InnerLogValid :
    leaf955InnerLog.Valid 8 (innerAD leaf955Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf955CoverageChecked

private noncomputable def leaf955InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629189/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf955InputLogOnePlusV_eq :
    leaf955InputLogOnePlusV = outerEnclosure 24
      (leaf955Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf955RoundedFacts : LeafRoundedFacts 8
    leaf955Certificate.logOnePlusV leaf955InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf955InputLogOnePlusV_eq }

private noncomputable def leaf955Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi97InputQChi innerPair2Input
    leaf955InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf955LowerChecked :
    lowerCheck 24 leaf955Box leaf955Inputs = true := by
  rfl'

private theorem leaf955CoversExact : CoversExact 8
    leaf955Box leaf955Certificate leaf955InnerLog leaf955Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf955RoundedFacts (by rfl)

private theorem leaf955FlatSound : Sound leaf955Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf955CertificateValid
    leaf955InnerLogValid leaf955CoversExact leaf955LowerChecked

private noncomputable def leaf956Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf956Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (11184832/11184701) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (152271687/134217728) }, upper := { exponent := 0, mantissa := (2377/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22369533/22369402) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf956InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf956LocalValidity :
    LeafFacts leaf956Box leaf956Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf956Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11184832/11184701) }) = true
      norm_num [leaf956Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf956CertificateValid :
    WideCertificateValid leaf956Box leaf956Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi96ValidityFacts
    leaf956LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf956CoverageChecked :
    coverageCheck (innerAD leaf956Box) leaf956InnerLog = true := by
  rfl'

private theorem leaf956InnerLogValid :
    leaf956InnerLog.Valid 8 (innerAD leaf956Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf956CoverageChecked

private noncomputable def leaf956InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629179/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf956InputLogOnePlusV_eq :
    leaf956InputLogOnePlusV = outerEnclosure 24
      (leaf956Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf956RoundedFacts : LeafRoundedFacts 8
    leaf956Certificate.logOnePlusV leaf956InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf956InputLogOnePlusV_eq }

private noncomputable def leaf956Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi96InputQChi innerPair2Input
    leaf956InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf956LowerChecked :
    lowerCheck 24 leaf956Box leaf956Inputs = true := by
  rfl'

private theorem leaf956CoversExact : CoversExact 8
    leaf956Box leaf956Certificate leaf956InnerLog leaf956Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf956RoundedFacts (by rfl)

private theorem leaf956FlatSound : Sound leaf956Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf956CertificateValid
    leaf956InnerLogValid leaf956CoversExact leaf956LowerChecked

private noncomputable def leaf957Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf957Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (152664877/134217728) }, upper := { exponent := 0, mantissa := (149/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194287/4194262) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf957InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf957LocalValidity :
    LeafFacts leaf957Box leaf957Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf957Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097131) }) = true
      norm_num [leaf957Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf957CertificateValid :
    WideCertificateValid leaf957Box leaf957Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi96ValidityFacts
    leaf957LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf957CoverageChecked :
    coverageCheck (innerAD leaf957Box) leaf957InnerLog = true := by
  rfl'

private theorem leaf957InnerLogValid :
    leaf957InnerLog.Valid 8 (innerAD leaf957Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf957CoverageChecked

private noncomputable def leaf957InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf957InputLogOnePlusV_eq :
    leaf957InputLogOnePlusV = outerEnclosure 24
      (leaf957Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf957RoundedFacts : LeafRoundedFacts 8
    leaf957Certificate.logOnePlusV leaf957InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf957InputLogOnePlusV_eq }

private noncomputable def leaf957Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi96InputQChi innerPair2Input
    leaf957InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf957LowerChecked :
    lowerCheck 24 leaf957Box leaf957Inputs = true := by
  rfl'

private theorem leaf957CoversExact : CoversExact 8
    leaf957Box leaf957Certificate leaf957InnerLog leaf957Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi96RoundedFacts
    innerPair2RoundedFacts leaf957RoundedFacts (by rfl)

private theorem leaf957FlatSound : Sound leaf957Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf957CertificateValid
    leaf957InnerLogValid leaf957CoversExact leaf957LowerChecked

private noncomputable def leaf958Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf958Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194257) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (155286157/134217728) }, upper := { exponent := 0, mantissa := (303/256) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388569/8388514) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf958InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf958LocalValidity :
    LeafFacts leaf958Box leaf958Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf958Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194257) }) = true
      norm_num [leaf958Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf958CertificateValid :
    WideCertificateValid leaf958Box leaf958Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi97ValidityFacts
    leaf958LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf958CoverageChecked :
    coverageCheck (innerAD leaf958Box) leaf958InnerLog = true := by
  rfl'

private theorem leaf958InnerLogValid :
    leaf958InnerLog.Valid 8 (innerAD leaf958Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf958CoverageChecked

private noncomputable def leaf958InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629191/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf958InputLogOnePlusV_eq :
    leaf958InputLogOnePlusV = outerEnclosure 24
      (leaf958Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf958RoundedFacts : LeafRoundedFacts 8
    leaf958Certificate.logOnePlusV leaf958InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf958InputLogOnePlusV_eq }

private noncomputable def leaf958Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi97InputQChi innerPair2Input
    leaf958InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf958LowerChecked :
    lowerCheck 24 leaf958Box leaf958Inputs = true := by
  rfl'

private theorem leaf958CoversExact : CoversExact 8
    leaf958Box leaf958Certificate leaf958InnerLog leaf958Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf958RoundedFacts (by rfl)

private theorem leaf958FlatSound : Sound leaf958Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf958CertificateValid
    leaf958InnerLogValid leaf958CoversExact leaf958LowerChecked

private noncomputable def leaf959Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf959Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (65529/65536), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (155744879/134217728) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf959InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf959LocalValidity :
    LeafFacts leaf959Box leaf959Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf959Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (524289/524282) }) = true
      norm_num [leaf959Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf959CertificateValid :
    WideCertificateValid leaf959Box leaf959Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi97ValidityFacts
    leaf959LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf959CoverageChecked :
    coverageCheck (innerAD leaf959Box) leaf959InnerLog = true := by
  rfl'

private theorem leaf959InnerLogValid :
    leaf959InnerLog.Valid 8 (innerAD leaf959Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf959CoverageChecked

private noncomputable def leaf959InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf959InputLogOnePlusV_eq :
    leaf959InputLogOnePlusV = outerEnclosure 24
      (leaf959Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf959RoundedFacts : LeafRoundedFacts 8
    leaf959Certificate.logOnePlusV leaf959InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf959InputLogOnePlusV_eq }

private noncomputable def leaf959Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi97InputQChi innerPair2Input
    leaf959InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf959LowerChecked :
    lowerCheck 24 leaf959Box leaf959Inputs = true := by
  rfl'

private theorem leaf959CoversExact : CoversExact 8
    leaf959Box leaf959Certificate leaf959InnerLog leaf959Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi97RoundedFacts
    innerPair2RoundedFacts leaf959RoundedFacts (by rfl)

private theorem leaf959FlatSound : Sound leaf959Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf959CertificateValid
    leaf959InnerLogValid leaf959CoversExact leaf959LowerChecked

private noncomputable def component22Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (0), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node0_sound : Sound component22Node0Box :=
  sound_of_literal_split component22Node0Box leaf916Box leaf917Box
    .k (21/8) (by rfl) (by rfl)
    leaf916FlatSound leaf917FlatSound

private noncomputable def component22Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node1_sound : Sound component22Node1Box :=
  sound_of_literal_split component22Node1Box leaf918Box leaf919Box
    .chi (3/128) (by rfl) (by rfl)
    leaf918FlatSound leaf919FlatSound

private noncomputable def component22Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node2_sound : Sound component22Node2Box :=
  sound_of_literal_split component22Node2Box leaf920Box leaf921Box
    .chi (3/128) (by rfl) (by rfl)
    leaf920FlatSound leaf921FlatSound

private noncomputable def component22Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node3_sound : Sound component22Node3Box :=
  sound_of_literal_split component22Node3Box component22Node1Box component22Node2Box
    .k (21/8) (by rfl) (by rfl)
    component22Node1_sound component22Node2_sound

private noncomputable def component22Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node4_sound : Sound component22Node4Box :=
  sound_of_literal_split component22Node4Box component22Node0Box component22Node3Box
    .chi (1/64) (by rfl) (by rfl)
    component22Node0_sound component22Node3_sound

private noncomputable def component22Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node5_sound : Sound component22Node5Box :=
  sound_of_literal_split component22Node5Box leaf923Box leaf924Box
    .k (41/16) (by rfl) (by rfl)
    leaf923FlatSound leaf924FlatSound

private noncomputable def component22Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node6_sound : Sound component22Node6Box :=
  sound_of_literal_split component22Node6Box leaf922Box component22Node5Box
    .chi (5/128) (by rfl) (by rfl)
    leaf922FlatSound component22Node5_sound

private noncomputable def component22Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component22Node7_sound : Sound component22Node7Box :=
  sound_of_literal_split component22Node7Box leaf925Box leaf926Box
    .k (43/16) (by rfl) (by rfl)
    leaf925FlatSound leaf926FlatSound

private noncomputable def component22Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node8_sound : Sound component22Node8Box :=
  sound_of_literal_split component22Node8Box leaf927Box leaf928Box
    .k (43/16) (by rfl) (by rfl)
    leaf927FlatSound leaf928FlatSound

private noncomputable def component22Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node9_sound : Sound component22Node9Box :=
  sound_of_literal_split component22Node9Box component22Node7Box component22Node8Box
    .chi (5/128) (by rfl) (by rfl)
    component22Node7_sound component22Node8_sound

private noncomputable def component22Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node10_sound : Sound component22Node10Box :=
  sound_of_literal_split component22Node10Box component22Node6Box component22Node9Box
    .k (21/8) (by rfl) (by rfl)
    component22Node6_sound component22Node9_sound

private noncomputable def component22Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component22Node11_sound : Sound component22Node11Box :=
  sound_of_literal_split component22Node11Box leaf929Box leaf930Box
    .k (41/16) (by rfl) (by rfl)
    leaf929FlatSound leaf930FlatSound

private noncomputable def component22Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node12_sound : Sound component22Node12Box :=
  sound_of_literal_split component22Node12Box leaf931Box leaf932Box
    .k (41/16) (by rfl) (by rfl)
    leaf931FlatSound leaf932FlatSound

private noncomputable def component22Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node13_sound : Sound component22Node13Box :=
  sound_of_literal_split component22Node13Box component22Node11Box component22Node12Box
    .chi (7/128) (by rfl) (by rfl)
    component22Node11_sound component22Node12_sound

private noncomputable def component22Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component22Node14_sound : Sound component22Node14Box :=
  sound_of_literal_split component22Node14Box leaf933Box leaf934Box
    .k (43/16) (by rfl) (by rfl)
    leaf933FlatSound leaf934FlatSound

private noncomputable def component22Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node15_sound : Sound component22Node15Box :=
  sound_of_literal_split component22Node15Box leaf935Box leaf936Box
    .k (43/16) (by rfl) (by rfl)
    leaf935FlatSound leaf936FlatSound

private noncomputable def component22Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node16_sound : Sound component22Node16Box :=
  sound_of_literal_split component22Node16Box component22Node14Box component22Node15Box
    .chi (7/128) (by rfl) (by rfl)
    component22Node14_sound component22Node15_sound

private noncomputable def component22Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node17_sound : Sound component22Node17Box :=
  sound_of_literal_split component22Node17Box component22Node13Box component22Node16Box
    .k (21/8) (by rfl) (by rfl)
    component22Node13_sound component22Node16_sound

private noncomputable def component22Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node18_sound : Sound component22Node18Box :=
  sound_of_literal_split component22Node18Box component22Node10Box component22Node17Box
    .chi (3/64) (by rfl) (by rfl)
    component22Node10_sound component22Node17_sound

private noncomputable def component22Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node19_sound : Sound component22Node19Box :=
  sound_of_literal_split component22Node19Box component22Node4Box component22Node18Box
    .chi (1/32) (by rfl) (by rfl)
    component22Node4_sound component22Node18_sound

private noncomputable def component22Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (0), chiHi := (1/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node20_sound : Sound component22Node20Box :=
  sound_of_literal_split component22Node20Box leaf937Box leaf938Box
    .k (23/8) (by rfl) (by rfl)
    leaf937FlatSound leaf938FlatSound

private noncomputable def component22Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node21_sound : Sound component22Node21Box :=
  sound_of_literal_split component22Node21Box leaf939Box leaf940Box
    .chi (3/128) (by rfl) (by rfl)
    leaf939FlatSound leaf940FlatSound

private noncomputable def component22Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/128), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node22_sound : Sound component22Node22Box :=
  sound_of_literal_split component22Node22Box leaf942Box leaf943Box
    .chi (7/256) (by rfl) (by rfl)
    leaf942FlatSound leaf943FlatSound

private noncomputable def component22Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node23_sound : Sound component22Node23Box :=
  sound_of_literal_split component22Node23Box leaf941Box component22Node22Box
    .chi (3/128) (by rfl) (by rfl)
    leaf941FlatSound component22Node22_sound

private noncomputable def component22Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/64), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node24_sound : Sound component22Node24Box :=
  sound_of_literal_split component22Node24Box component22Node21Box component22Node23Box
    .k (23/8) (by rfl) (by rfl)
    component22Node21_sound component22Node23_sound

private noncomputable def component22Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component22Node25_sound : Sound component22Node25Box :=
  sound_of_literal_split component22Node25Box component22Node20Box component22Node24Box
    .chi (1/64) (by rfl) (by rfl)
    component22Node20_sound component22Node24_sound

private noncomputable def component22Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component22Node26_sound : Sound component22Node26Box :=
  sound_of_literal_split component22Node26Box leaf944Box leaf945Box
    .k (45/16) (by rfl) (by rfl)
    leaf944FlatSound leaf945FlatSound

private noncomputable def component22Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node27_sound : Sound component22Node27Box :=
  sound_of_literal_split component22Node27Box leaf946Box leaf947Box
    .k (45/16) (by rfl) (by rfl)
    leaf946FlatSound leaf947FlatSound

private noncomputable def component22Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node28_sound : Sound component22Node28Box :=
  sound_of_literal_split component22Node28Box component22Node26Box component22Node27Box
    .chi (5/128) (by rfl) (by rfl)
    component22Node26_sound component22Node27_sound

private noncomputable def component22Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/32), chiHi := (5/128) }

set_option maxRecDepth 1000000 in
private theorem component22Node29_sound : Sound component22Node29Box :=
  sound_of_literal_split component22Node29Box leaf948Box leaf949Box
    .k (47/16) (by rfl) (by rfl)
    leaf948FlatSound leaf949FlatSound

private noncomputable def component22Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/128), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node30_sound : Sound component22Node30Box :=
  sound_of_literal_split component22Node30Box leaf950Box leaf951Box
    .k (47/16) (by rfl) (by rfl)
    leaf950FlatSound leaf951FlatSound

private noncomputable def component22Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node31_sound : Sound component22Node31Box :=
  sound_of_literal_split component22Node31Box component22Node29Box component22Node30Box
    .chi (5/128) (by rfl) (by rfl)
    component22Node29_sound component22Node30_sound

private noncomputable def component22Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component22Node32_sound : Sound component22Node32Box :=
  sound_of_literal_split component22Node32Box component22Node28Box component22Node31Box
    .k (23/8) (by rfl) (by rfl)
    component22Node28_sound component22Node31_sound

private noncomputable def component22Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component22Node33_sound : Sound component22Node33Box :=
  sound_of_literal_split component22Node33Box leaf952Box leaf953Box
    .k (45/16) (by rfl) (by rfl)
    leaf952FlatSound leaf953FlatSound

private noncomputable def component22Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node34_sound : Sound component22Node34Box :=
  sound_of_literal_split component22Node34Box leaf954Box leaf955Box
    .k (45/16) (by rfl) (by rfl)
    leaf954FlatSound leaf955FlatSound

private noncomputable def component22Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node35_sound : Sound component22Node35Box :=
  sound_of_literal_split component22Node35Box component22Node33Box component22Node34Box
    .chi (7/128) (by rfl) (by rfl)
    component22Node33_sound component22Node34_sound

private noncomputable def component22Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component22Node36_sound : Sound component22Node36Box :=
  sound_of_literal_split component22Node36Box leaf956Box leaf957Box
    .k (47/16) (by rfl) (by rfl)
    leaf956FlatSound leaf957FlatSound

private noncomputable def component22Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node37_sound : Sound component22Node37Box :=
  sound_of_literal_split component22Node37Box leaf958Box leaf959Box
    .k (47/16) (by rfl) (by rfl)
    leaf958FlatSound leaf959FlatSound

private noncomputable def component22Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node38_sound : Sound component22Node38Box :=
  sound_of_literal_split component22Node38Box component22Node36Box component22Node37Box
    .chi (7/128) (by rfl) (by rfl)
    component22Node36_sound component22Node37_sound

private noncomputable def component22Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node39_sound : Sound component22Node39Box :=
  sound_of_literal_split component22Node39Box component22Node35Box component22Node38Box
    .k (23/8) (by rfl) (by rfl)
    component22Node35_sound component22Node38_sound

private noncomputable def component22Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node40_sound : Sound component22Node40Box :=
  sound_of_literal_split component22Node40Box component22Node32Box component22Node39Box
    .chi (3/64) (by rfl) (by rfl)
    component22Node32_sound component22Node39_sound

private noncomputable def component22Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component22Node41_sound : Sound component22Node41Box :=
  sound_of_literal_split component22Node41Box component22Node25Box component22Node40Box
    .chi (1/32) (by rfl) (by rfl)
    component22Node25_sound component22Node40_sound

noncomputable def component22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
theorem component22_sound : Sound component22Box :=
  sound_of_literal_split component22Box component22Node19Box component22Node41Box
    .k (11/4) (by rfl) (by rfl)
    component22Node19_sound component22Node41_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
