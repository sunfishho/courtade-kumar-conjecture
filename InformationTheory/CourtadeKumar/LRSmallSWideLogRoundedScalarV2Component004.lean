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

private noncomputable def leaf163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (0), chiHi := (1/32) }

private noncomputable def leaf163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777243/16777216) }, vSqrt := { lower := (16383/16384), upper := (4194320/4194291) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (16744423/8388608) }, upper := { exponent := 0, mantissa := (269/256) } }, logOuter := sk31LogOuterCertificate, logK := sk31LogKCertificate, logChi := chi29LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388611/8388582) } }, logDArg := sk31LogDArgCertificate }

private noncomputable def leaf163InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf163LocalValidity :
    LeafFacts leaf163Box leaf163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194320/4194291) }) = true
      norm_num [leaf163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf163CertificateValid :
    WideCertificateValid leaf163Box leaf163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk31ValidityFacts chi29ValidityFacts
    leaf163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf163CoverageChecked :
    coverageCheck (innerAD leaf163Box) leaf163InnerLog = true := by
  rfl'

private theorem leaf163InnerLogValid :
    leaf163InnerLog.Valid 8 (innerAD leaf163Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf163CoverageChecked

private noncomputable def leaf163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629139/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf163InputLogOnePlusV_eq :
    leaf163InputLogOnePlusV = outerEnclosure 24
      (leaf163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf163RoundedFacts : LeafRoundedFacts 8
    leaf163Certificate.logOnePlusV leaf163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf163InputLogOnePlusV_eq }

private noncomputable def leaf163Inputs : Inputs :=
  inputsOfCaches globalInput sk31RoundedInputs
    chi29InputQChi innerPair1Input
    leaf163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf163LowerChecked :
    lowerCheck 24 leaf163Box leaf163Inputs = true := by
  rfl'

private theorem leaf163CoversExact : CoversExact 8
    leaf163Box leaf163Certificate leaf163InnerLog leaf163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk31RoundedFacts chi29RoundedFacts
    innerPair1RoundedFacts leaf163RoundedFacts (by rfl)

private theorem leaf163FlatSound : Sound leaf163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf163CertificateValid
    leaf163InnerLogValid leaf163CoversExact leaf163LowerChecked

private noncomputable def leaf164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (0), chiHi := (1/32) }

private noncomputable def leaf164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777245/16777216) }, vSqrt := { lower := (16383/16384), upper := (419432/419429) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (16744421/8388608) }, upper := { exponent := 0, mantissa := (135/128) } }, logOuter := sk32LogOuterCertificate, logK := sk32LogKCertificate, logChi := chi29LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (838861/838858) } }, logDArg := sk32LogDArgCertificate }

private noncomputable def leaf164InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf164LocalValidity :
    LeafFacts leaf164Box leaf164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (419432/419429) }) = true
      norm_num [leaf164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf164CertificateValid :
    WideCertificateValid leaf164Box leaf164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk32ValidityFacts chi29ValidityFacts
    leaf164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf164CoverageChecked :
    coverageCheck (innerAD leaf164Box) leaf164InnerLog = true := by
  rfl'

private theorem leaf164InnerLogValid :
    leaf164InnerLog.Valid 8 (innerAD leaf164Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf164CoverageChecked

private noncomputable def leaf164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629141/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf164InputLogOnePlusV_eq :
    leaf164InputLogOnePlusV = outerEnclosure 24
      (leaf164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf164RoundedFacts : LeafRoundedFacts 8
    leaf164Certificate.logOnePlusV leaf164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf164InputLogOnePlusV_eq }

private noncomputable def leaf164Inputs : Inputs :=
  inputsOfCaches globalInput sk32RoundedInputs
    chi29InputQChi innerPair1Input
    leaf164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf164LowerChecked :
    lowerCheck 24 leaf164Box leaf164Inputs = true := by
  rfl'

private theorem leaf164CoversExact : CoversExact 8
    leaf164Box leaf164Certificate leaf164InnerLog leaf164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk32RoundedFacts chi29RoundedFacts
    innerPair1RoundedFacts leaf164RoundedFacts (by rfl)

private theorem leaf164FlatSound : Sound leaf164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf164CertificateValid
    leaf164InnerLogValid leaf164CoversExact leaf164LowerChecked

private noncomputable def leaf165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/32), chiHi := (3/64) }

private noncomputable def leaf165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554463/33554432) }, vSqrt := { lower := (16383/16384), upper := (8388640/8388569) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35094403/33554432) }, upper := { exponent := 0, mantissa := (551/512) } }, logOuter := sk31LogOuterCertificate, logK := sk31LogKCertificate, logChi := chi30LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777209/16777138) } }, logDArg := sk31LogDArgCertificate }

private noncomputable def leaf165InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf165LocalValidity :
    LeafFacts leaf165Box leaf165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388640/8388569) }) = true
      norm_num [leaf165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf165CertificateValid :
    WideCertificateValid leaf165Box leaf165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk31ValidityFacts chi30ValidityFacts
    leaf165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf165CoverageChecked :
    coverageCheck (innerAD leaf165Box) leaf165InnerLog = true := by
  rfl'

private theorem leaf165InnerLogValid :
    leaf165InnerLog.Valid 8 (innerAD leaf165Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf165CoverageChecked

private noncomputable def leaf165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (363411/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf165InputLogOnePlusV_eq :
    leaf165InputLogOnePlusV = outerEnclosure 24
      (leaf165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf165RoundedFacts : LeafRoundedFacts 8
    leaf165Certificate.logOnePlusV leaf165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf165InputLogOnePlusV_eq }

private noncomputable def leaf165Inputs : Inputs :=
  inputsOfCaches globalInput sk31RoundedInputs
    chi30InputQChi innerPair9Input
    leaf165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf165LowerChecked :
    lowerCheck 24 leaf165Box leaf165Inputs = true := by
  rfl'

private theorem leaf165CoversExact : CoversExact 8
    leaf165Box leaf165Certificate leaf165InnerLog leaf165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk31RoundedFacts chi30RoundedFacts
    innerPair9RoundedFacts leaf165RoundedFacts (by rfl)

private theorem leaf165FlatSound : Sound leaf165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf165CertificateValid
    leaf165InnerLogValid leaf165CoversExact leaf165LowerChecked

private noncomputable def leaf166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554465/33554432) }, vSqrt := { lower := (16383/16384), upper := (2097160/2097139) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35880785/33554432) }, upper := { exponent := 0, mantissa := (141/128) } }, logOuter := sk31LogOuterCertificate, logK := sk31LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194299/4194278) } }, logDArg := sk31LogDArgCertificate }

private noncomputable def leaf166InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf166LocalValidity :
    LeafFacts leaf166Box leaf166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097160/2097139) }) = true
      norm_num [leaf166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf166CertificateValid :
    WideCertificateValid leaf166Box leaf166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk31ValidityFacts chi31ValidityFacts
    leaf166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf166CoverageChecked :
    coverageCheck (innerAD leaf166Box) leaf166InnerLog = true := by
  rfl'

private theorem leaf166InnerLogValid :
    leaf166InnerLog.Valid 8 (innerAD leaf166Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf166CoverageChecked

private noncomputable def leaf166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf166InputLogOnePlusV_eq :
    leaf166InputLogOnePlusV = outerEnclosure 24
      (leaf166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf166RoundedFacts : LeafRoundedFacts 8
    leaf166Certificate.logOnePlusV leaf166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf166InputLogOnePlusV_eq }

private noncomputable def leaf166Inputs : Inputs :=
  inputsOfCaches globalInput sk31RoundedInputs
    chi31InputQChi innerPair5Input
    leaf166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf166LowerChecked :
    lowerCheck 24 leaf166Box leaf166Inputs = true := by
  rfl'

private theorem leaf166CoversExact : CoversExact 8
    leaf166Box leaf166Certificate leaf166InnerLog leaf166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk31RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf166RoundedFacts (by rfl)

private theorem leaf166FlatSound : Sound leaf166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf166CertificateValid
    leaf166InnerLogValid leaf166CoversExact leaf166LowerChecked

private noncomputable def leaf167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/32), chiHi := (3/64) }

private noncomputable def leaf167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554465/33554432) }, vSqrt := { lower := (16383/16384), upper := (113360/113359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35225465/33554432) }, upper := { exponent := 0, mantissa := (277/256) } }, logOuter := sk32LogOuterCertificate, logK := sk32LogKCertificate, logChi := chi30LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (226719/226718) } }, logDArg := sk32LogDArgCertificate }

private noncomputable def leaf167InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf167LocalValidity :
    LeafFacts leaf167Box leaf167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (113360/113359) }) = true
      norm_num [leaf167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf167CertificateValid :
    WideCertificateValid leaf167Box leaf167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk32ValidityFacts chi30ValidityFacts
    leaf167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf167CoverageChecked :
    coverageCheck (innerAD leaf167Box) leaf167InnerLog = true := by
  rfl'

private theorem leaf167InnerLogValid :
    leaf167InnerLog.Valid 8 (innerAD leaf167Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf167CoverageChecked

private noncomputable def leaf167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf167InputLogOnePlusV_eq :
    leaf167InputLogOnePlusV = outerEnclosure 24
      (leaf167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf167RoundedFacts : LeafRoundedFacts 8
    leaf167Certificate.logOnePlusV leaf167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf167InputLogOnePlusV_eq }

private noncomputable def leaf167Inputs : Inputs :=
  inputsOfCaches globalInput sk32RoundedInputs
    chi30InputQChi innerPair9Input
    leaf167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf167LowerChecked :
    lowerCheck 24 leaf167Box leaf167Inputs = true := by
  rfl'

private theorem leaf167CoversExact : CoversExact 8
    leaf167Box leaf167Certificate leaf167InnerLog leaf167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk32RoundedFacts chi30RoundedFacts
    innerPair9RoundedFacts leaf167RoundedFacts (by rfl)

private theorem leaf167FlatSound : Sound leaf167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf167CertificateValid
    leaf167InnerLogValid leaf167CoversExact leaf167LowerChecked

private noncomputable def leaf168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108925/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194277) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72187533/67108864) }, upper := { exponent := 0, mantissa := (283/256) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388589/8388554) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf168InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf168LocalValidity :
    LeafFacts leaf168Box leaf168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194277) }) = true
      norm_num [leaf168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf168CertificateValid :
    WideCertificateValid leaf168Box leaf168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi31ValidityFacts
    leaf168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf168CoverageChecked :
    coverageCheck (innerAD leaf168Box) leaf168InnerLog = true := by
  rfl'

private theorem leaf168InnerLogValid :
    leaf168InnerLog.Valid 8 (innerAD leaf168Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf168CoverageChecked

private noncomputable def leaf168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629151/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf168InputLogOnePlusV_eq :
    leaf168InputLogOnePlusV = outerEnclosure 24
      (leaf168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf168RoundedFacts : LeafRoundedFacts 8
    leaf168Certificate.logOnePlusV leaf168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf168InputLogOnePlusV_eq }

private noncomputable def leaf168Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi31InputQChi innerPair5Input
    leaf168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf168LowerChecked :
    lowerCheck 24 leaf168Box leaf168Inputs = true := by
  rfl'

private theorem leaf168CoversExact : CoversExact 8
    leaf168Box leaf168Certificate leaf168InnerLog leaf168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf168RoundedFacts (by rfl)

private theorem leaf168FlatSound : Sound leaf168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf168CertificateValid
    leaf168InnerLogValid leaf168CoversExact leaf168LowerChecked

private noncomputable def leaf169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108927/67108864) }, vSqrt := { lower := (16383/16384), upper := (349526/349523) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72384127/67108864) }, upper := { exponent := 0, mantissa := (71/64) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (699049/699046) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf169InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf169LocalValidity :
    LeafFacts leaf169Box leaf169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (349526/349523) }) = true
      norm_num [leaf169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf169CertificateValid :
    WideCertificateValid leaf169Box leaf169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi31ValidityFacts
    leaf169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf169CoverageChecked :
    coverageCheck (innerAD leaf169Box) leaf169InnerLog = true := by
  rfl'

private theorem leaf169InnerLogValid :
    leaf169InnerLog.Valid 8 (innerAD leaf169Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf169CoverageChecked

private noncomputable def leaf169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf169InputLogOnePlusV_eq :
    leaf169InputLogOnePlusV = outerEnclosure 24
      (leaf169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf169RoundedFacts : LeafRoundedFacts 8
    leaf169Certificate.logOnePlusV leaf169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf169InputLogOnePlusV_eq }

private noncomputable def leaf169Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi31InputQChi innerPair5Input
    leaf169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf169LowerChecked :
    lowerCheck 24 leaf169Box leaf169Inputs = true := by
  rfl'

private theorem leaf169CoversExact : CoversExact 8
    leaf169Box leaf169Certificate leaf169InnerLog leaf169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf169RoundedFacts (by rfl)

private theorem leaf169FlatSound : Sound leaf169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf169CertificateValid
    leaf169InnerLogValid leaf169CoversExact leaf169LowerChecked

private noncomputable def leaf170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108923/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16777091) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (73367111/67108864) }, upper := { exponent := 0, mantissa := (1149/1024) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554339/33554182) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf170InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf170LocalValidity :
    LeafFacts leaf170Box leaf170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16777091) }) = true
      norm_num [leaf170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf170CertificateValid :
    WideCertificateValid leaf170Box leaf170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi32ValidityFacts
    leaf170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf170CoverageChecked :
    coverageCheck (innerAD leaf170Box) leaf170InnerLog = true := by
  rfl'

private theorem leaf170InnerLogValid :
    leaf170InnerLog.Valid 8 (innerAD leaf170Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf170CoverageChecked

private noncomputable def leaf170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629159/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf170InputLogOnePlusV_eq :
    leaf170InputLogOnePlusV = outerEnclosure 24
      (leaf170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf170RoundedFacts : LeafRoundedFacts 8
    leaf170Certificate.logOnePlusV leaf170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf170InputLogOnePlusV_eq }

private noncomputable def leaf170Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi32InputQChi innerPair5Input
    leaf170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf170LowerChecked :
    lowerCheck 24 leaf170Box leaf170Inputs = true := by
  rfl'

private theorem leaf170CoversExact : CoversExact 8
    leaf170Box leaf170Certificate leaf170InnerLog leaf170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi32RoundedFacts
    innerPair5RoundedFacts leaf170RoundedFacts (by rfl)

private theorem leaf170FlatSound : Sound leaf170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf170CertificateValid
    leaf170InnerLogValid leaf170CoversExact leaf170LowerChecked

private noncomputable def leaf171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108925/67108864) }, vSqrt := { lower := (16383/16384), upper := (2796208/2796181) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (73629237/67108864) }, upper := { exponent := 0, mantissa := (577/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (5592389/5592362) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf171InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf171LocalValidity :
    LeafFacts leaf171Box leaf171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2796208/2796181) }) = true
      norm_num [leaf171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf171CertificateValid :
    WideCertificateValid leaf171Box leaf171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi32ValidityFacts
    leaf171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf171CoverageChecked :
    coverageCheck (innerAD leaf171Box) leaf171InnerLog = true := by
  rfl'

private theorem leaf171InnerLogValid :
    leaf171InnerLog.Valid 8 (innerAD leaf171Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf171CoverageChecked

private noncomputable def leaf171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814581/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf171InputLogOnePlusV_eq :
    leaf171InputLogOnePlusV = outerEnclosure 24
      (leaf171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf171RoundedFacts : LeafRoundedFacts 8
    leaf171Certificate.logOnePlusV leaf171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf171InputLogOnePlusV_eq }

private noncomputable def leaf171Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi32InputQChi innerPair6Input
    leaf171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf171LowerChecked :
    lowerCheck 24 leaf171Box leaf171Inputs = true := by
  rfl'

private theorem leaf171CoversExact : CoversExact 8
    leaf171Box leaf171Certificate leaf171InnerLog leaf171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf171RoundedFacts (by rfl)

private theorem leaf171FlatSound : Sound leaf171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf171CertificateValid
    leaf171InnerLogValid leaf171CoversExact leaf171LowerChecked

private noncomputable def leaf172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108925/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388533) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (74939877/67108864) }, upper := { exponent := 0, mantissa := (587/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777157/16777066) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf172InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf172LocalValidity :
    LeafFacts leaf172Box leaf172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388533) }) = true
      norm_num [leaf172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf172CertificateValid :
    WideCertificateValid leaf172Box leaf172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi33ValidityFacts
    leaf172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf172CoverageChecked :
    coverageCheck (innerAD leaf172Box) leaf172InnerLog = true := by
  rfl'

private theorem leaf172InnerLogValid :
    leaf172InnerLog.Valid 8 (innerAD leaf172Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf172CoverageChecked

private noncomputable def leaf172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907293/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf172InputLogOnePlusV_eq :
    leaf172InputLogOnePlusV = outerEnclosure 24
      (leaf172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf172RoundedFacts : LeafRoundedFacts 8
    leaf172Certificate.logOnePlusV leaf172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf172InputLogOnePlusV_eq }

private noncomputable def leaf172Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi33InputQChi innerPair6Input
    leaf172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf172LowerChecked :
    lowerCheck 24 leaf172Box leaf172Inputs = true := by
  rfl'

private theorem leaf172CoversExact : CoversExact 8
    leaf172Box leaf172Certificate leaf172InnerLog leaf172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi33RoundedFacts
    innerPair6RoundedFacts leaf172RoundedFacts (by rfl)

private theorem leaf172FlatSound : Sound leaf172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf172CertificateValid
    leaf172InnerLogValid leaf172CoversExact leaf172LowerChecked

private noncomputable def leaf173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108927/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194265) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (75267535/67108864) }, upper := { exponent := 0, mantissa := (295/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388577/8388530) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf173InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf173LocalValidity :
    LeafFacts leaf173Box leaf173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194265) }) = true
      norm_num [leaf173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf173CertificateValid :
    WideCertificateValid leaf173Box leaf173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi33ValidityFacts
    leaf173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf173CoverageChecked :
    coverageCheck (innerAD leaf173Box) leaf173InnerLog = true := by
  rfl'

private theorem leaf173InnerLogValid :
    leaf173InnerLog.Valid 8 (innerAD leaf173Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf173CoverageChecked

private noncomputable def leaf173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629175/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf173InputLogOnePlusV_eq :
    leaf173InputLogOnePlusV = outerEnclosure 24
      (leaf173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf173RoundedFacts : LeafRoundedFacts 8
    leaf173Certificate.logOnePlusV leaf173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf173InputLogOnePlusV_eq }

private noncomputable def leaf173Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi33InputQChi innerPair6Input
    leaf173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf173LowerChecked :
    lowerCheck 24 leaf173Box leaf173Inputs = true := by
  rfl'

private theorem leaf173CoversExact : CoversExact 8
    leaf173Box leaf173Certificate leaf173InnerLog leaf173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi33RoundedFacts
    innerPair6RoundedFacts leaf173RoundedFacts (by rfl)

private theorem leaf173FlatSound : Sound leaf173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf173CertificateValid
    leaf173InnerLogValid leaf173CoversExact leaf173LowerChecked

private noncomputable def leaf174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554489/33554432) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097127) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (38239913/33554432) }, upper := { exponent := 0, mantissa := (153/128) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194283/4194254) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf174InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf174LocalValidity :
    LeafFacts leaf174Box leaf174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097127) }) = true
      norm_num [leaf174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf174CertificateValid :
    WideCertificateValid leaf174Box leaf174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi14ValidityFacts
    leaf174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf174CoverageChecked :
    coverageCheck (innerAD leaf174Box) leaf174InnerLog = true := by
  rfl'

private theorem leaf174InnerLogValid :
    leaf174InnerLog.Valid 8 (innerAD leaf174Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf174CoverageChecked

private noncomputable def leaf174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629197/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf174InputLogOnePlusV_eq :
    leaf174InputLogOnePlusV = outerEnclosure 24
      (leaf174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf174RoundedFacts : LeafRoundedFacts 8
    leaf174Certificate.logOnePlusV leaf174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf174InputLogOnePlusV_eq }

private noncomputable def leaf174Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi14InputQChi innerPair3Input
    leaf174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf174LowerChecked :
    lowerCheck 24 leaf174Box leaf174Inputs = true := by
  rfl'

private theorem leaf174CoversExact : CoversExact 8
    leaf174Box leaf174Certificate leaf174InnerLog leaf174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi14RoundedFacts
    innerPair3RoundedFacts leaf174RoundedFacts (by rfl)

private theorem leaf174FlatSound : Sound leaf174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf174CertificateValid
    leaf174InnerLogValid leaf174CoversExact leaf174LowerChecked

private noncomputable def leaf175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (3/32), chiHi := (1/8) }

private noncomputable def leaf175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (16383/16384), upper := (349526/349521) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (38436507/33554432) }, upper := { exponent := 0, mantissa := (77/64) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi14LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (699047/699042) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf175InnerLog : WideLogData :=
  innerPair135Data

set_option maxRecDepth 1000000 in
private theorem leaf175LocalValidity :
    LeafFacts leaf175Box leaf175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (349526/349521) }) = true
      norm_num [leaf175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf175CertificateValid :
    WideCertificateValid leaf175Box leaf175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi14ValidityFacts
    leaf175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf175CoverageChecked :
    coverageCheck (innerAD leaf175Box) leaf175InnerLog = true := by
  rfl'

private theorem leaf175InnerLogValid :
    leaf175InnerLog.Valid 8 (innerAD leaf175Box) :=
  wideLogDataValid_of_cachedCheck endpoint31PositiveFacts
    endpoint26PositiveFacts.valid leaf175CoverageChecked

private noncomputable def leaf175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629201/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf175InputLogOnePlusV_eq :
    leaf175InputLogOnePlusV = outerEnclosure 24
      (leaf175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf175RoundedFacts : LeafRoundedFacts 8
    leaf175Certificate.logOnePlusV leaf175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf175InputLogOnePlusV_eq }

private noncomputable def leaf175Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi14InputQChi innerPair135Input
    leaf175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf175LowerChecked :
    lowerCheck 24 leaf175Box leaf175Inputs = true := by
  rfl'

private theorem leaf175CoversExact : CoversExact 8
    leaf175Box leaf175Certificate leaf175InnerLog leaf175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi14RoundedFacts
    innerPair135RoundedFacts leaf175RoundedFacts (by rfl)

private theorem leaf175FlatSound : Sound leaf175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf175CertificateValid
    leaf175InnerLogValid leaf175CoversExact leaf175LowerChecked

private noncomputable def leaf176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108927/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16777081) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (73891363/67108864) }, upper := { exponent := 0, mantissa := (1159/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554329/33554162) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf176InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf176LocalValidity :
    LeafFacts leaf176Box leaf176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16777081) }) = true
      norm_num [leaf176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf176CertificateValid :
    WideCertificateValid leaf176Box leaf176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi32ValidityFacts
    leaf176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf176CoverageChecked :
    coverageCheck (innerAD leaf176Box) leaf176InnerLog = true := by
  rfl'

private theorem leaf176InnerLogValid :
    leaf176InnerLog.Valid 8 (innerAD leaf176Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf176CoverageChecked

private noncomputable def leaf176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907291/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf176InputLogOnePlusV_eq :
    leaf176InputLogOnePlusV = outerEnclosure 24
      (leaf176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf176RoundedFacts : LeafRoundedFacts 8
    leaf176Certificate.logOnePlusV leaf176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf176InputLogOnePlusV_eq }

private noncomputable def leaf176Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi32InputQChi innerPair6Input
    leaf176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf176LowerChecked :
    lowerCheck 24 leaf176Box leaf176Inputs = true := by
  rfl'

private theorem leaf176CoversExact : CoversExact 8
    leaf176Box leaf176Certificate leaf176InnerLog leaf176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf176RoundedFacts (by rfl)

private theorem leaf176FlatSound : Sound leaf176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf176CertificateValid
    leaf176InnerLogValid leaf176CoversExact leaf176LowerChecked

private noncomputable def leaf177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108929/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194269) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (74153489/67108864) }, upper := { exponent := 0, mantissa := (291/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388581/8388538) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf177InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf177LocalValidity :
    LeafFacts leaf177Box leaf177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194269) }) = true
      norm_num [leaf177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf177CertificateValid :
    WideCertificateValid leaf177Box leaf177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi32ValidityFacts
    leaf177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf177CoverageChecked :
    coverageCheck (innerAD leaf177Box) leaf177InnerLog = true := by
  rfl'

private theorem leaf177InnerLogValid :
    leaf177InnerLog.Valid 8 (innerAD leaf177Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf177CoverageChecked

private noncomputable def leaf177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629167/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf177InputLogOnePlusV_eq :
    leaf177InputLogOnePlusV = outerEnclosure 24
      (leaf177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf177RoundedFacts : LeafRoundedFacts 8
    leaf177Certificate.logOnePlusV leaf177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf177InputLogOnePlusV_eq }

private noncomputable def leaf177Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi32InputQChi innerPair6Input
    leaf177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf177LowerChecked :
    lowerCheck 24 leaf177Box leaf177Inputs = true := by
  rfl'

private theorem leaf177CoversExact : CoversExact 8
    leaf177Box leaf177Certificate leaf177InnerLog leaf177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf177RoundedFacts (by rfl)

private theorem leaf177FlatSound : Sound leaf177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf177CertificateValid
    leaf177InnerLogValid leaf177CoversExact leaf177LowerChecked

private noncomputable def leaf178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108929/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388527) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (75595193/67108864) }, upper := { exponent := 0, mantissa := (593/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777151/16777054) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf178InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf178LocalValidity :
    LeafFacts leaf178Box leaf178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388527) }) = true
      norm_num [leaf178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf178CertificateValid :
    WideCertificateValid leaf178Box leaf178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi33ValidityFacts
    leaf178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf178CoverageChecked :
    coverageCheck (innerAD leaf178Box) leaf178InnerLog = true := by
  rfl'

private theorem leaf178InnerLogValid :
    leaf178InnerLog.Valid 8 (innerAD leaf178Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf178CoverageChecked

private noncomputable def leaf178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814589/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf178InputLogOnePlusV_eq :
    leaf178InputLogOnePlusV = outerEnclosure 24
      (leaf178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf178RoundedFacts : LeafRoundedFacts 8
    leaf178Certificate.logOnePlusV leaf178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf178InputLogOnePlusV_eq }

private noncomputable def leaf178Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi33InputQChi innerPair2Input
    leaf178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf178LowerChecked :
    lowerCheck 24 leaf178Box leaf178Inputs = true := by
  rfl'

private theorem leaf178CoversExact : CoversExact 8
    leaf178Box leaf178Certificate leaf178InnerLog leaf178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi33RoundedFacts
    innerPair2RoundedFacts leaf178RoundedFacts (by rfl)

private theorem leaf178FlatSound : Sound leaf178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf178CertificateValid
    leaf178InnerLogValid leaf178CoversExact leaf178LowerChecked

private noncomputable def leaf179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108931/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (75922851/67108864) }, upper := { exponent := 0, mantissa := (149/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194287/4194262) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf179InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf179LocalValidity :
    LeafFacts leaf179Box leaf179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097131) }) = true
      norm_num [leaf179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf179CertificateValid :
    WideCertificateValid leaf179Box leaf179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi33ValidityFacts
    leaf179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf179CoverageChecked :
    coverageCheck (innerAD leaf179Box) leaf179InnerLog = true := by
  rfl'

private theorem leaf179InnerLogValid :
    leaf179InnerLog.Valid 8 (innerAD leaf179Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf179CoverageChecked

private noncomputable def leaf179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629181/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf179InputLogOnePlusV_eq :
    leaf179InputLogOnePlusV = outerEnclosure 24
      (leaf179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf179RoundedFacts : LeafRoundedFacts 8
    leaf179Certificate.logOnePlusV leaf179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf179InputLogOnePlusV_eq }

private noncomputable def leaf179Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi33InputQChi innerPair2Input
    leaf179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf179LowerChecked :
    lowerCheck 24 leaf179Box leaf179Inputs = true := by
  rfl'

private theorem leaf179CoversExact : CoversExact 8
    leaf179Box leaf179Certificate leaf179InnerLog leaf179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi33RoundedFacts
    innerPair2RoundedFacts leaf179RoundedFacts (by rfl)

private theorem leaf179FlatSound : Sound leaf179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf179CertificateValid
    leaf179InnerLogValid leaf179CoversExact leaf179LowerChecked

private noncomputable def leaf180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108931/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16777027) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (77299023/67108864) }, upper := { exponent := 0, mantissa := (1213/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554275/33554054) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf180InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf180LocalValidity :
    LeafFacts leaf180Box leaf180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16777027) }) = true
      norm_num [leaf180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf180CertificateValid :
    WideCertificateValid leaf180Box leaf180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi36ValidityFacts
    leaf180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf180CoverageChecked :
    coverageCheck (innerAD leaf180Box) leaf180InnerLog = true := by
  rfl'

private theorem leaf180InnerLogValid :
    leaf180InnerLog.Valid 8 (innerAD leaf180Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf180CoverageChecked

private noncomputable def leaf180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629191/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf180InputLogOnePlusV_eq :
    leaf180InputLogOnePlusV = outerEnclosure 24
      (leaf180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf180RoundedFacts : LeafRoundedFacts 8
    leaf180Certificate.logOnePlusV leaf180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf180InputLogOnePlusV_eq }

private noncomputable def leaf180Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi36InputQChi innerPair2Input
    leaf180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf180LowerChecked :
    lowerCheck 24 leaf180Box leaf180Inputs = true := by
  rfl'

private theorem leaf180CoversExact : CoversExact 8
    leaf180Box leaf180Certificate leaf180InnerLog leaf180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi36RoundedFacts
    innerPair2RoundedFacts leaf180RoundedFacts (by rfl)

private theorem leaf180FlatSound : Sound leaf180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf180CertificateValid
    leaf180InnerLogValid leaf180CoversExact leaf180LowerChecked

private noncomputable def leaf181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108933/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097125) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (79002853/67108864) }, upper := { exponent := 0, mantissa := (155/128) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194281/4194250) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf181InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf181LocalValidity :
    LeafFacts leaf181Box leaf181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097125) }) = true
      norm_num [leaf181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf181CertificateValid :
    WideCertificateValid leaf181Box leaf181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi37ValidityFacts
    leaf181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf181CoverageChecked :
    coverageCheck (innerAD leaf181Box) leaf181InnerLog = true := by
  rfl'

private theorem leaf181InnerLogValid :
    leaf181InnerLog.Valid 8 (innerAD leaf181Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf181CoverageChecked

private noncomputable def leaf181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf181InputLogOnePlusV_eq :
    leaf181InputLogOnePlusV = outerEnclosure 24
      (leaf181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf181RoundedFacts : LeafRoundedFacts 8
    leaf181Certificate.logOnePlusV leaf181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf181InputLogOnePlusV_eq }

private noncomputable def leaf181Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi37InputQChi innerPair3Input
    leaf181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf181LowerChecked :
    lowerCheck 24 leaf181Box leaf181Inputs = true := by
  rfl'

private theorem leaf181CoversExact : CoversExact 8
    leaf181Box leaf181Certificate leaf181InnerLog leaf181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi37RoundedFacts
    innerPair3RoundedFacts leaf181RoundedFacts (by rfl)

private theorem leaf181FlatSound : Sound leaf181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf181CertificateValid
    leaf181InnerLogValid leaf181CoversExact leaf181LowerChecked

private noncomputable def leaf182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108933/67108864) }, vSqrt := { lower := (16383/16384), upper := (1398104/1398085) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (77692213/67108864) }, upper := { exponent := 0, mantissa := (305/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2796189/2796170) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf182InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf182LocalValidity :
    LeafFacts leaf182Box leaf182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1398104/1398085) }) = true
      norm_num [leaf182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf182CertificateValid :
    WideCertificateValid leaf182Box leaf182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi36ValidityFacts
    leaf182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf182CoverageChecked :
    coverageCheck (innerAD leaf182Box) leaf182InnerLog = true := by
  rfl'

private theorem leaf182InnerLogValid :
    leaf182InnerLog.Valid 8 (innerAD leaf182Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf182CoverageChecked

private noncomputable def leaf182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629195/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf182InputLogOnePlusV_eq :
    leaf182InputLogOnePlusV = outerEnclosure 24
      (leaf182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf182RoundedFacts : LeafRoundedFacts 8
    leaf182Certificate.logOnePlusV leaf182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf182InputLogOnePlusV_eq }

private noncomputable def leaf182Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi36InputQChi innerPair3Input
    leaf182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf182LowerChecked :
    lowerCheck 24 leaf182Box leaf182Inputs = true := by
  rfl'

private theorem leaf182CoversExact : CoversExact 8
    leaf182Box leaf182Certificate leaf182InnerLog leaf182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi36RoundedFacts
    innerPair3RoundedFacts leaf182RoundedFacts (by rfl)

private theorem leaf182FlatSound : Sound leaf182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf182CertificateValid
    leaf182InnerLogValid leaf182CoversExact leaf182LowerChecked

private noncomputable def leaf183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (16383/16384), upper := (524289/524281) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (79461575/67108864) }, upper := { exponent := 0, mantissa := (39/32) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (524285/524281) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf183InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf183LocalValidity :
    LeafFacts leaf183Box leaf183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (524289/524281) }) = true
      norm_num [leaf183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf183CertificateValid :
    WideCertificateValid leaf183Box leaf183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi37ValidityFacts
    leaf183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf183CoverageChecked :
    coverageCheck (innerAD leaf183Box) leaf183InnerLog = true := by
  rfl'

private theorem leaf183InnerLogValid :
    leaf183InnerLog.Valid 8 (innerAD leaf183Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf183CoverageChecked

private noncomputable def leaf183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf183InputLogOnePlusV_eq :
    leaf183InputLogOnePlusV = outerEnclosure 24
      (leaf183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf183RoundedFacts : LeafRoundedFacts 8
    leaf183Certificate.logOnePlusV leaf183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf183InputLogOnePlusV_eq }

private noncomputable def leaf183Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi37InputQChi innerPair3Input
    leaf183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf183LowerChecked :
    lowerCheck 24 leaf183Box leaf183Inputs = true := by
  rfl'

private theorem leaf183CoversExact : CoversExact 8
    leaf183Box leaf183Certificate leaf183InnerLog leaf183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi37RoundedFacts
    innerPair3RoundedFacts leaf183RoundedFacts (by rfl)

private theorem leaf183FlatSound : Sound leaf183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf183CertificateValid
    leaf183InnerLogValid leaf183CoversExact leaf183LowerChecked

private noncomputable def leaf184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (0), chiHi := (1/32) }

private noncomputable def leaf184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777247/16777216) }, vSqrt := { lower := (16383/16384), upper := (4194320/4194289) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (16744419/8388608) }, upper := { exponent := 0, mantissa := (271/256) } }, logOuter := sk37LogOuterCertificate, logK := sk37LogKCertificate, logChi := chi29LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388609/8388578) } }, logDArg := sk37LogDArgCertificate }

private noncomputable def leaf184InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf184LocalValidity :
    LeafFacts leaf184Box leaf184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194320/4194289) }) = true
      norm_num [leaf184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf184CertificateValid :
    WideCertificateValid leaf184Box leaf184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk37ValidityFacts chi29ValidityFacts
    leaf184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf184CoverageChecked :
    coverageCheck (innerAD leaf184Box) leaf184InnerLog = true := by
  rfl'

private theorem leaf184InnerLogValid :
    leaf184InnerLog.Valid 8 (innerAD leaf184Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf184CoverageChecked

private noncomputable def leaf184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629143/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf184InputLogOnePlusV_eq :
    leaf184InputLogOnePlusV = outerEnclosure 24
      (leaf184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf184RoundedFacts : LeafRoundedFacts 8
    leaf184Certificate.logOnePlusV leaf184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf184InputLogOnePlusV_eq }

private noncomputable def leaf184Inputs : Inputs :=
  inputsOfCaches globalInput sk37RoundedInputs
    chi29InputQChi innerPair1Input
    leaf184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf184LowerChecked :
    lowerCheck 24 leaf184Box leaf184Inputs = true := by
  rfl'

private theorem leaf184CoversExact : CoversExact 8
    leaf184Box leaf184Certificate leaf184InnerLog leaf184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk37RoundedFacts chi29RoundedFacts
    innerPair1RoundedFacts leaf184RoundedFacts (by rfl)

private theorem leaf184FlatSound : Sound leaf184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf184CertificateValid
    leaf184InnerLogValid leaf184CoversExact leaf184LowerChecked

private noncomputable def leaf185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (0), chiHi := (1/32) }

private noncomputable def leaf185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777249/16777216) }, vSqrt := { lower := (65531/65536), upper := (262145/262143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (16744417/8388608) }, upper := { exponent := 0, mantissa := (17/16) } }, logOuter := sk38LogOuterCertificate, logK := sk38LogKCertificate, logChi := chi29LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (262144/262143) } }, logDArg := sk38LogDArgCertificate }

private noncomputable def leaf185InnerLog : WideLogData :=
  innerPair1Data

set_option maxRecDepth 1000000 in
private theorem leaf185LocalValidity :
    LeafFacts leaf185Box leaf185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (262145/262143) }) = true
      norm_num [leaf185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf185CertificateValid :
    WideCertificateValid leaf185Box leaf185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk38ValidityFacts chi29ValidityFacts
    leaf185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf185CoverageChecked :
    coverageCheck (innerAD leaf185Box) leaf185InnerLog = true := by
  rfl'

private theorem leaf185InnerLogValid :
    leaf185InnerLog.Valid 8 (innerAD leaf185Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint2PositiveFacts.valid leaf185CoverageChecked

private noncomputable def leaf185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629145/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf185InputLogOnePlusV_eq :
    leaf185InputLogOnePlusV = outerEnclosure 24
      (leaf185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf185RoundedFacts : LeafRoundedFacts 8
    leaf185Certificate.logOnePlusV leaf185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf185InputLogOnePlusV_eq }

private noncomputable def leaf185Inputs : Inputs :=
  inputsOfCaches globalInput sk38RoundedInputs
    chi29InputQChi innerPair1Input
    leaf185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf185LowerChecked :
    lowerCheck 24 leaf185Box leaf185Inputs = true := by
  rfl'

private theorem leaf185CoversExact : CoversExact 8
    leaf185Box leaf185Certificate leaf185InnerLog leaf185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk38RoundedFacts chi29RoundedFacts
    innerPair1RoundedFacts leaf185RoundedFacts (by rfl)

private theorem leaf185FlatSound : Sound leaf185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf185CertificateValid
    leaf185InnerLogValid leaf185CoversExact leaf185LowerChecked

private noncomputable def leaf186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/32), chiHi := (3/64) }

private noncomputable def leaf186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554467/33554432) }, vSqrt := { lower := (16383/16384), upper := (8388640/8388563) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (35356527/33554432) }, upper := { exponent := 0, mantissa := (557/512) } }, logOuter := sk37LogOuterCertificate, logK := sk37LogKCertificate, logChi := chi30LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777203/16777126) } }, logDArg := sk37LogDArgCertificate }

private noncomputable def leaf186InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf186LocalValidity :
    LeafFacts leaf186Box leaf186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388640/8388563) }) = true
      norm_num [leaf186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf186CertificateValid :
    WideCertificateValid leaf186Box leaf186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk37ValidityFacts chi30ValidityFacts
    leaf186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf186CoverageChecked :
    coverageCheck (innerAD leaf186Box) leaf186InnerLog = true := by
  rfl'

private theorem leaf186InnerLogValid :
    leaf186InnerLog.Valid 8 (innerAD leaf186Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf186CoverageChecked

private noncomputable def leaf186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf186InputLogOnePlusV_eq :
    leaf186InputLogOnePlusV = outerEnclosure 24
      (leaf186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf186RoundedFacts : LeafRoundedFacts 8
    leaf186Certificate.logOnePlusV leaf186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf186InputLogOnePlusV_eq }

private noncomputable def leaf186Inputs : Inputs :=
  inputsOfCaches globalInput sk37RoundedInputs
    chi30InputQChi innerPair9Input
    leaf186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf186LowerChecked :
    lowerCheck 24 leaf186Box leaf186Inputs = true := by
  rfl'

private theorem leaf186CoversExact : CoversExact 8
    leaf186Box leaf186Certificate leaf186InnerLog leaf186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk37RoundedFacts chi30RoundedFacts
    innerPair9RoundedFacts leaf186RoundedFacts (by rfl)

private theorem leaf186FlatSound : Sound leaf186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf186CertificateValid
    leaf186InnerLogValid leaf186CoversExact leaf186LowerChecked

private noncomputable def leaf187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108929/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194275) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72580721/67108864) }, upper := { exponent := 0, mantissa := (285/256) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388587/8388550) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf187InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf187LocalValidity :
    LeafFacts leaf187Box leaf187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194275) }) = true
      norm_num [leaf187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf187CertificateValid :
    WideCertificateValid leaf187Box leaf187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi31ValidityFacts
    leaf187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf187CoverageChecked :
    coverageCheck (innerAD leaf187Box) leaf187InnerLog = true := by
  rfl'

private theorem leaf187InnerLogValid :
    leaf187InnerLog.Valid 8 (innerAD leaf187Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf187CoverageChecked

private noncomputable def leaf187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf187InputLogOnePlusV_eq :
    leaf187InputLogOnePlusV = outerEnclosure 24
      (leaf187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf187RoundedFacts : LeafRoundedFacts 8
    leaf187Certificate.logOnePlusV leaf187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf187InputLogOnePlusV_eq }

private noncomputable def leaf187Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi31InputQChi innerPair5Input
    leaf187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf187LowerChecked :
    lowerCheck 24 leaf187Box leaf187Inputs = true := by
  rfl'

private theorem leaf187CoversExact : CoversExact 8
    leaf187Box leaf187Certificate leaf187InnerLog leaf187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf187RoundedFacts (by rfl)

private theorem leaf187FlatSound : Sound leaf187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf187CertificateValid
    leaf187InnerLogValid leaf187CoversExact leaf187LowerChecked

private noncomputable def leaf188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108931/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097137) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72777315/67108864) }, upper := { exponent := 0, mantissa := (143/128) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194293/4194274) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf188InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf188LocalValidity :
    LeafFacts leaf188Box leaf188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097137) }) = true
      norm_num [leaf188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf188CertificateValid :
    WideCertificateValid leaf188Box leaf188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi31ValidityFacts
    leaf188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf188CoverageChecked :
    coverageCheck (innerAD leaf188Box) leaf188InnerLog = true := by
  rfl'

private theorem leaf188InnerLogValid :
    leaf188InnerLog.Valid 8 (innerAD leaf188Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf188CoverageChecked

private noncomputable def leaf188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629157/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf188InputLogOnePlusV_eq :
    leaf188InputLogOnePlusV = outerEnclosure 24
      (leaf188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf188RoundedFacts : LeafRoundedFacts 8
    leaf188Certificate.logOnePlusV leaf188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf188InputLogOnePlusV_eq }

private noncomputable def leaf188Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi31InputQChi innerPair5Input
    leaf188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf188LowerChecked :
    lowerCheck 24 leaf188Box leaf188Inputs = true := by
  rfl'

private theorem leaf188CoversExact : CoversExact 8
    leaf188Box leaf188Certificate leaf188InnerLog leaf188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf188RoundedFacts (by rfl)

private theorem leaf188FlatSound : Sound leaf188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf188CertificateValid
    leaf188InnerLogValid leaf188CoversExact leaf188LowerChecked

private noncomputable def leaf189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108905/67108864) }, vSqrt := { lower := (65531/65536), upper := (1048580/1048571) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71007977/67108864) }, upper := { exponent := 0, mantissa := (69/64) } }, logOuter := sk38LogOuterCertificate, logK := sk38LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097151/2097142) } }, logDArg := sk38LogDArgCertificate }

private noncomputable def leaf189InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf189LocalValidity :
    LeafFacts leaf189Box leaf189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048580/1048571) }) = true
      norm_num [leaf189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf189CertificateValid :
    WideCertificateValid leaf189Box leaf189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk38ValidityFacts chi38ValidityFacts
    leaf189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf189CoverageChecked :
    coverageCheck (innerAD leaf189Box) leaf189InnerLog = true := by
  rfl'

private theorem leaf189InnerLogValid :
    leaf189InnerLog.Valid 8 (innerAD leaf189Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf189CoverageChecked

private noncomputable def leaf189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf189InputLogOnePlusV_eq :
    leaf189InputLogOnePlusV = outerEnclosure 24
      (leaf189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf189RoundedFacts : LeafRoundedFacts 8
    leaf189Certificate.logOnePlusV leaf189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf189InputLogOnePlusV_eq }

private noncomputable def leaf189Inputs : Inputs :=
  inputsOfCaches globalInput sk38RoundedInputs
    chi38InputQChi innerPair9Input
    leaf189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf189LowerChecked :
    lowerCheck 24 leaf189Box leaf189Inputs = true := by
  rfl'

private theorem leaf189CoversExact : CoversExact 8
    leaf189Box leaf189Certificate leaf189InnerLog leaf189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk38RoundedFacts chi38RoundedFacts
    innerPair9RoundedFacts leaf189RoundedFacts (by rfl)

private theorem leaf189FlatSound : Sound leaf189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf189CertificateValid
    leaf189InnerLogValid leaf189CoversExact leaf189LowerChecked

private noncomputable def leaf190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108907/67108864) }, vSqrt := { lower := (65531/65536), upper := (104858/104857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71990955/67108864) }, upper := { exponent := 0, mantissa := (35/32) } }, logOuter := sk38LogOuterCertificate, logK := sk38LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (209715/209714) } }, logDArg := sk38LogDArgCertificate }

private noncomputable def leaf190InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf190LocalValidity :
    LeafFacts leaf190Box leaf190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (104858/104857) }) = true
      norm_num [leaf190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf190CertificateValid :
    WideCertificateValid leaf190Box leaf190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk38ValidityFacts chi39ValidityFacts
    leaf190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf190CoverageChecked :
    coverageCheck (innerAD leaf190Box) leaf190InnerLog = true := by
  rfl'

private theorem leaf190InnerLogValid :
    leaf190InnerLog.Valid 8 (innerAD leaf190Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf190CoverageChecked

private noncomputable def leaf190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf190InputLogOnePlusV_eq :
    leaf190InputLogOnePlusV = outerEnclosure 24
      (leaf190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf190RoundedFacts : LeafRoundedFacts 8
    leaf190Certificate.logOnePlusV leaf190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf190InputLogOnePlusV_eq }

private noncomputable def leaf190Inputs : Inputs :=
  inputsOfCaches globalInput sk38RoundedInputs
    chi39InputQChi innerPair5Input
    leaf190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf190LowerChecked :
    lowerCheck 24 leaf190Box leaf190Inputs = true := by
  rfl'

private theorem leaf190CoversExact : CoversExact 8
    leaf190Box leaf190Certificate leaf190InnerLog leaf190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk38RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf190RoundedFacts (by rfl)

private theorem leaf190FlatSound : Sound leaf190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf190CertificateValid
    leaf190InnerLogValid leaf190CoversExact leaf190LowerChecked

private noncomputable def leaf191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108933/67108864) }, vSqrt := { lower := (16383/16384), upper := (1398104/1398091) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72973909/67108864) }, upper := { exponent := 0, mantissa := (287/256) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2796195/2796182) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf191InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf191LocalValidity :
    LeafFacts leaf191Box leaf191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1398104/1398091) }) = true
      norm_num [leaf191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf191CertificateValid :
    WideCertificateValid leaf191Box leaf191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi31ValidityFacts
    leaf191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf191CoverageChecked :
    coverageCheck (innerAD leaf191Box) leaf191InnerLog = true := by
  rfl'

private theorem leaf191InnerLogValid :
    leaf191InnerLog.Valid 8 (innerAD leaf191Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf191CoverageChecked

private noncomputable def leaf191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629159/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf191InputLogOnePlusV_eq :
    leaf191InputLogOnePlusV = outerEnclosure 24
      (leaf191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf191RoundedFacts : LeafRoundedFacts 8
    leaf191Certificate.logOnePlusV leaf191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf191InputLogOnePlusV_eq }

private noncomputable def leaf191Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi31InputQChi innerPair5Input
    leaf191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf191LowerChecked :
    lowerCheck 24 leaf191Box leaf191Inputs = true := by
  rfl'

private theorem leaf191CoversExact : CoversExact 8
    leaf191Box leaf191Certificate leaf191InnerLog leaf191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf191RoundedFacts (by rfl)

private theorem leaf191FlatSound : Sound leaf191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf191CertificateValid
    leaf191InnerLogValid leaf191CoversExact leaf191LowerChecked

private noncomputable def leaf192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (65531/65536), upper := (524289/524284) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (73170503/67108864) }, upper := { exponent := 0, mantissa := (9/8) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1048573/1048568) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf192InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf192LocalValidity :
    LeafFacts leaf192Box leaf192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (524289/524284) }) = true
      norm_num [leaf192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf192CertificateValid :
    WideCertificateValid leaf192Box leaf192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi31ValidityFacts
    leaf192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf192CoverageChecked :
    coverageCheck (innerAD leaf192Box) leaf192InnerLog = true := by
  rfl'

private theorem leaf192InnerLogValid :
    leaf192InnerLog.Valid 8 (innerAD leaf192Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf192CoverageChecked

private noncomputable def leaf192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629161/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf192InputLogOnePlusV_eq :
    leaf192InputLogOnePlusV = outerEnclosure 24
      (leaf192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf192RoundedFacts : LeafRoundedFacts 8
    leaf192Certificate.logOnePlusV leaf192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf192InputLogOnePlusV_eq }

private noncomputable def leaf192Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi31InputQChi innerPair5Input
    leaf192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf192LowerChecked :
    lowerCheck 24 leaf192Box leaf192Inputs = true := by
  rfl'

private theorem leaf192CoversExact : CoversExact 8
    leaf192Box leaf192Certificate leaf192InnerLog leaf192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi31RoundedFacts
    innerPair5RoundedFacts leaf192RoundedFacts (by rfl)

private theorem leaf192FlatSound : Sound leaf192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf192CertificateValid
    leaf192InnerLogValid leaf192CoversExact leaf192LowerChecked

private noncomputable def leaf193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108931/67108864) }, vSqrt := { lower := (16383/16384), upper := (5592416/5592357) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (74415615/67108864) }, upper := { exponent := 0, mantissa := (1169/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11184773/11184714) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf193InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf193LocalValidity :
    LeafFacts leaf193Box leaf193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5592416/5592357) }) = true
      norm_num [leaf193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf193CertificateValid :
    WideCertificateValid leaf193Box leaf193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi32ValidityFacts
    leaf193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf193CoverageChecked :
    coverageCheck (innerAD leaf193Box) leaf193InnerLog = true := by
  rfl'

private theorem leaf193InnerLogValid :
    leaf193InnerLog.Valid 8 (innerAD leaf193Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf193CoverageChecked

private noncomputable def leaf193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf193InputLogOnePlusV_eq :
    leaf193InputLogOnePlusV = outerEnclosure 24
      (leaf193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf193RoundedFacts : LeafRoundedFacts 8
    leaf193Certificate.logOnePlusV leaf193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf193InputLogOnePlusV_eq }

private noncomputable def leaf193Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi32InputQChi innerPair6Input
    leaf193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf193LowerChecked :
    lowerCheck 24 leaf193Box leaf193Inputs = true := by
  rfl'

private theorem leaf193CoversExact : CoversExact 8
    leaf193Box leaf193Certificate leaf193InnerLog leaf193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf193RoundedFacts (by rfl)

private theorem leaf193FlatSound : Sound leaf193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf193CertificateValid
    leaf193InnerLogValid leaf193CoversExact leaf193LowerChecked

private noncomputable def leaf194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108933/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388533) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (74677741/67108864) }, upper := { exponent := 0, mantissa := (587/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777157/16777066) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf194InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf194LocalValidity :
    LeafFacts leaf194Box leaf194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388533) }) = true
      norm_num [leaf194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf194CertificateValid :
    WideCertificateValid leaf194Box leaf194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi32ValidityFacts
    leaf194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf194CoverageChecked :
    coverageCheck (innerAD leaf194Box) leaf194InnerLog = true := by
  rfl'

private theorem leaf194InnerLogValid :
    leaf194InnerLog.Valid 8 (innerAD leaf194Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf194CoverageChecked

private noncomputable def leaf194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (2907293/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf194InputLogOnePlusV_eq :
    leaf194InputLogOnePlusV = outerEnclosure 24
      (leaf194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf194RoundedFacts : LeafRoundedFacts 8
    leaf194Certificate.logOnePlusV leaf194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf194InputLogOnePlusV_eq }

private noncomputable def leaf194Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi32InputQChi innerPair6Input
    leaf194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf194LowerChecked :
    lowerCheck 24 leaf194Box leaf194Inputs = true := by
  rfl'

private theorem leaf194CoversExact : CoversExact 8
    leaf194Box leaf194Certificate leaf194InnerLog leaf194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf194RoundedFacts (by rfl)

private theorem leaf194FlatSound : Sound leaf194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf194CertificateValid
    leaf194InnerLogValid leaf194CoversExact leaf194LowerChecked

private noncomputable def leaf195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108933/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388521) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (76250509/67108864) }, upper := { exponent := 0, mantissa := (599/512) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777145/16777042) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf195InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf195LocalValidity :
    LeafFacts leaf195Box leaf195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388521) }) = true
      norm_num [leaf195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf195CertificateValid :
    WideCertificateValid leaf195Box leaf195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi33ValidityFacts
    leaf195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf195CoverageChecked :
    coverageCheck (innerAD leaf195Box) leaf195InnerLog = true := by
  rfl'

private theorem leaf195InnerLogValid :
    leaf195InnerLog.Valid 8 (innerAD leaf195Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf195CoverageChecked

private noncomputable def leaf195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (90853/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf195InputLogOnePlusV_eq :
    leaf195InputLogOnePlusV = outerEnclosure 24
      (leaf195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf195RoundedFacts : LeafRoundedFacts 8
    leaf195Certificate.logOnePlusV leaf195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf195InputLogOnePlusV_eq }

private noncomputable def leaf195Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi33InputQChi innerPair2Input
    leaf195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf195LowerChecked :
    lowerCheck 24 leaf195Box leaf195Inputs = true := by
  rfl'

private theorem leaf195CoversExact : CoversExact 8
    leaf195Box leaf195Certificate leaf195InnerLog leaf195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi33RoundedFacts
    innerPair2RoundedFacts leaf195RoundedFacts (by rfl)

private theorem leaf195FlatSound : Sound leaf195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf195CertificateValid
    leaf195InnerLogValid leaf195CoversExact leaf195LowerChecked

private noncomputable def leaf196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (76578167/67108864) }, upper := { exponent := 0, mantissa := (301/256) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388571/8388518) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf196InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf196LocalValidity :
    LeafFacts leaf196Box leaf196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194259) }) = true
      norm_num [leaf196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf196CertificateValid :
    WideCertificateValid leaf196Box leaf196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi33ValidityFacts
    leaf196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf196CoverageChecked :
    coverageCheck (innerAD leaf196Box) leaf196InnerLog = true := by
  rfl'

private theorem leaf196InnerLogValid :
    leaf196InnerLog.Valid 8 (innerAD leaf196Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf196CoverageChecked

private noncomputable def leaf196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629187/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf196InputLogOnePlusV_eq :
    leaf196InputLogOnePlusV = outerEnclosure 24
      (leaf196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf196RoundedFacts : LeafRoundedFacts 8
    leaf196Certificate.logOnePlusV leaf196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf196InputLogOnePlusV_eq }

private noncomputable def leaf196Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi33InputQChi innerPair2Input
    leaf196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf196LowerChecked :
    lowerCheck 24 leaf196Box leaf196Inputs = true := by
  rfl'

private theorem leaf196CoversExact : CoversExact 8
    leaf196Box leaf196Certificate leaf196InnerLog leaf196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi33RoundedFacts
    innerPair2RoundedFacts leaf196RoundedFacts (by rfl)

private theorem leaf196FlatSound : Sound leaf196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf196CertificateValid
    leaf196InnerLogValid leaf196CoversExact leaf196LowerChecked

private noncomputable def leaf197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16777061) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (74939867/67108864) }, upper := { exponent := 0, mantissa := (1179/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554309/33554122) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf197InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf197LocalValidity :
    LeafFacts leaf197Box leaf197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16777061) }) = true
      norm_num [leaf197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf197CertificateValid :
    WideCertificateValid leaf197Box leaf197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi32ValidityFacts
    leaf197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf197CoverageChecked :
    coverageCheck (innerAD leaf197Box) leaf197InnerLog = true := by
  rfl'

private theorem leaf197InnerLogValid :
    leaf197InnerLog.Valid 8 (innerAD leaf197Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf197CoverageChecked

private noncomputable def leaf197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814587/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf197InputLogOnePlusV_eq :
    leaf197InputLogOnePlusV = outerEnclosure 24
      (leaf197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf197RoundedFacts : LeafRoundedFacts 8
    leaf197Certificate.logOnePlusV leaf197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf197InputLogOnePlusV_eq }

private noncomputable def leaf197Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi32InputQChi innerPair6Input
    leaf197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf197LowerChecked :
    lowerCheck 24 leaf197Box leaf197Inputs = true := by
  rfl'

private theorem leaf197CoversExact : CoversExact 8
    leaf197Box leaf197Certificate leaf197InnerLog leaf197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf197RoundedFacts (by rfl)

private theorem leaf197FlatSound : Sound leaf197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf197CertificateValid
    leaf197InnerLogValid leaf197CoversExact leaf197LowerChecked

private noncomputable def leaf198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (65531/65536), upper := (174763/174761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (75201993/67108864) }, upper := { exponent := 0, mantissa := (37/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (174762/174761) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf198InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf198LocalValidity :
    LeafFacts leaf198Box leaf198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (174763/174761) }) = true
      norm_num [leaf198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf198CertificateValid :
    WideCertificateValid leaf198Box leaf198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi32ValidityFacts
    leaf198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf198CoverageChecked :
    coverageCheck (innerAD leaf198Box) leaf198InnerLog = true := by
  rfl'

private theorem leaf198InnerLogValid :
    leaf198InnerLog.Valid 8 (innerAD leaf198Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf198CoverageChecked

private noncomputable def leaf198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629177/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf198InputLogOnePlusV_eq :
    leaf198InputLogOnePlusV = outerEnclosure 24
      (leaf198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf198RoundedFacts : LeafRoundedFacts 8
    leaf198Certificate.logOnePlusV leaf198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf198InputLogOnePlusV_eq }

private noncomputable def leaf198Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi32InputQChi innerPair6Input
    leaf198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf198LowerChecked :
    lowerCheck 24 leaf198Box leaf198Inputs = true := by
  rfl'

private theorem leaf198CoversExact : CoversExact 8
    leaf198Box leaf198Certificate leaf198InnerLog leaf198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf198RoundedFacts (by rfl)

private theorem leaf198FlatSound : Sound leaf198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf198CertificateValid
    leaf198InnerLogValid leaf198CoversExact leaf198LowerChecked

private noncomputable def leaf199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388515) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (76905825/67108864) }, upper := { exponent := 0, mantissa := (605/512) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777139/16777030) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf199InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf199LocalValidity :
    LeafFacts leaf199Box leaf199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388515) }) = true
      norm_num [leaf199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf199CertificateValid :
    WideCertificateValid leaf199Box leaf199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi33ValidityFacts
    leaf199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf199CoverageChecked :
    coverageCheck (innerAD leaf199Box) leaf199InnerLog = true := by
  rfl'

private theorem leaf199InnerLogValid :
    leaf199InnerLog.Valid 8 (innerAD leaf199Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf199CoverageChecked

private noncomputable def leaf199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814595/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf199InputLogOnePlusV_eq :
    leaf199InputLogOnePlusV = outerEnclosure 24
      (leaf199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf199RoundedFacts : LeafRoundedFacts 8
    leaf199Certificate.logOnePlusV leaf199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf199InputLogOnePlusV_eq }

private noncomputable def leaf199Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi33InputQChi innerPair2Input
    leaf199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf199LowerChecked :
    lowerCheck 24 leaf199Box leaf199Inputs = true := by
  rfl'

private theorem leaf199CoversExact : CoversExact 8
    leaf199Box leaf199Certificate leaf199InnerLog leaf199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi33RoundedFacts
    innerPair2RoundedFacts leaf199RoundedFacts (by rfl)

private theorem leaf199FlatSound : Sound leaf199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf199CertificateValid
    leaf199InnerLogValid leaf199CoversExact leaf199LowerChecked

private noncomputable def leaf200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (65531/65536), upper := (524289/524282) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (77233483/67108864) }, upper := { exponent := 0, mantissa := (19/16) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1048571/1048564) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf200InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf200LocalValidity :
    LeafFacts leaf200Box leaf200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (524289/524282) }) = true
      norm_num [leaf200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf200CertificateValid :
    WideCertificateValid leaf200Box leaf200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi33ValidityFacts
    leaf200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf200CoverageChecked :
    coverageCheck (innerAD leaf200Box) leaf200InnerLog = true := by
  rfl'

private theorem leaf200InnerLogValid :
    leaf200InnerLog.Valid 8 (innerAD leaf200Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf200CoverageChecked

private noncomputable def leaf200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629193/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf200InputLogOnePlusV_eq :
    leaf200InputLogOnePlusV = outerEnclosure 24
      (leaf200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf200RoundedFacts : LeafRoundedFacts 8
    leaf200Certificate.logOnePlusV leaf200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf200InputLogOnePlusV_eq }

private noncomputable def leaf200Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi33InputQChi innerPair2Input
    leaf200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf200LowerChecked :
    lowerCheck 24 leaf200Box leaf200Inputs = true := by
  rfl'

private theorem leaf200CoversExact : CoversExact 8
    leaf200Box leaf200Certificate leaf200InnerLog leaf200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi33RoundedFacts
    innerPair2RoundedFacts leaf200RoundedFacts (by rfl)

private theorem leaf200FlatSound : Sound leaf200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf200CertificateValid
    leaf200InnerLogValid leaf200CoversExact leaf200LowerChecked

private noncomputable def leaf201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16777013) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (78085403/67108864) }, upper := { exponent := 0, mantissa := (1227/1024) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554261/33554026) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf201InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf201LocalValidity :
    LeafFacts leaf201Box leaf201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16777013) }) = true
      norm_num [leaf201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf201CertificateValid :
    WideCertificateValid leaf201Box leaf201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi36ValidityFacts
    leaf201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf201CoverageChecked :
    coverageCheck (innerAD leaf201Box) leaf201InnerLog = true := by
  rfl'

private theorem leaf201InnerLogValid :
    leaf201InnerLog.Valid 8 (innerAD leaf201Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf201CoverageChecked

private noncomputable def leaf201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814599/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf201InputLogOnePlusV_eq :
    leaf201InputLogOnePlusV = outerEnclosure 24
      (leaf201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf201RoundedFacts : LeafRoundedFacts 8
    leaf201Certificate.logOnePlusV leaf201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf201InputLogOnePlusV_eq }

private noncomputable def leaf201Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi36InputQChi innerPair3Input
    leaf201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf201LowerChecked :
    lowerCheck 24 leaf201Box leaf201Inputs = true := by
  rfl'

private theorem leaf201CoversExact : CoversExact 8
    leaf201Box leaf201Certificate leaf201InnerLog leaf201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi36RoundedFacts
    innerPair3RoundedFacts leaf201RoundedFacts (by rfl)

private theorem leaf201FlatSound : Sound leaf201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf201CertificateValid
    leaf201InnerLogValid leaf201CoversExact leaf201LowerChecked

private noncomputable def leaf202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388503) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (78478593/67108864) }, upper := { exponent := 0, mantissa := (617/512) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777127/16777006) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf202InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf202LocalValidity :
    LeafFacts leaf202Box leaf202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388503) }) = true
      norm_num [leaf202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf202CertificateValid :
    WideCertificateValid leaf202Box leaf202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi36ValidityFacts
    leaf202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf202CoverageChecked :
    coverageCheck (innerAD leaf202Box) leaf202InnerLog = true := by
  rfl'

private theorem leaf202InnerLogValid :
    leaf202InnerLog.Valid 8 (innerAD leaf202Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf202CoverageChecked

private noncomputable def leaf202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814601/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf202InputLogOnePlusV_eq :
    leaf202InputLogOnePlusV = outerEnclosure 24
      (leaf202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf202RoundedFacts : LeafRoundedFacts 8
    leaf202Certificate.logOnePlusV leaf202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf202InputLogOnePlusV_eq }

private noncomputable def leaf202Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi36InputQChi innerPair3Input
    leaf202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf202LowerChecked :
    lowerCheck 24 leaf202Box leaf202Inputs = true := by
  rfl'

private theorem leaf202CoversExact : CoversExact 8
    leaf202Box leaf202Certificate leaf202InnerLog leaf202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi36RoundedFacts
    innerPair3RoundedFacts leaf202RoundedFacts (by rfl)

private theorem leaf202FlatSound : Sound leaf202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf202CertificateValid
    leaf202InnerLogValid leaf202CoversExact leaf202LowerChecked

private noncomputable def leaf203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (29/16), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (699052/699041) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (79920297/67108864) }, upper := { exponent := 0, mantissa := (157/128) } }, logOuter := sk39LogOuterCertificate, logK := sk39LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1398093/1398082) } }, logDArg := sk39LogDArgCertificate }

private noncomputable def leaf203InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf203LocalValidity :
    LeafFacts leaf203Box leaf203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (699052/699041) }) = true
      norm_num [leaf203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf203CertificateValid :
    WideCertificateValid leaf203Box leaf203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk39ValidityFacts chi37ValidityFacts
    leaf203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf203CoverageChecked :
    coverageCheck (innerAD leaf203Box) leaf203InnerLog = true := by
  rfl'

private theorem leaf203InnerLogValid :
    leaf203InnerLog.Valid 8 (innerAD leaf203Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf203CoverageChecked

private noncomputable def leaf203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf203InputLogOnePlusV_eq :
    leaf203InputLogOnePlusV = outerEnclosure 24
      (leaf203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf203RoundedFacts : LeafRoundedFacts 8
    leaf203Certificate.logOnePlusV leaf203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf203InputLogOnePlusV_eq }

private noncomputable def leaf203Inputs : Inputs :=
  inputsOfCaches globalInput sk39RoundedInputs
    chi37InputQChi innerPair12Input
    leaf203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf203LowerChecked :
    lowerCheck 24 leaf203Box leaf203Inputs = true := by
  rfl'

private theorem leaf203CoversExact : CoversExact 8
    leaf203Box leaf203Certificate leaf203InnerLog leaf203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk39RoundedFacts chi37RoundedFacts
    innerPair12RoundedFacts leaf203RoundedFacts (by rfl)

private theorem leaf203FlatSound : Sound leaf203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf203CertificateValid
    leaf203InnerLogValid leaf203CoversExact leaf203LowerChecked

private noncomputable def leaf204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/16), kHi := (15/8), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (80379019/67108864) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk40LogOuterCertificate, logK := sk40LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk40LogDArgCertificate }

private noncomputable def leaf204InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf204LocalValidity :
    LeafFacts leaf204Box leaf204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048578/1048561) }) = true
      norm_num [leaf204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf204CertificateValid :
    WideCertificateValid leaf204Box leaf204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk40ValidityFacts chi37ValidityFacts
    leaf204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf204CoverageChecked :
    coverageCheck (innerAD leaf204Box) leaf204InnerLog = true := by
  rfl'

private theorem leaf204InnerLogValid :
    leaf204InnerLog.Valid 8 (innerAD leaf204Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf204CoverageChecked

private noncomputable def leaf204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf204InputLogOnePlusV_eq :
    leaf204InputLogOnePlusV = outerEnclosure 24
      (leaf204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf204RoundedFacts : LeafRoundedFacts 8
    leaf204Certificate.logOnePlusV leaf204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf204InputLogOnePlusV_eq }

private noncomputable def leaf204Inputs : Inputs :=
  inputsOfCaches globalInput sk40RoundedInputs
    chi37InputQChi innerPair12Input
    leaf204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf204LowerChecked :
    lowerCheck 24 leaf204Box leaf204Inputs = true := by
  rfl'

private theorem leaf204CoversExact : CoversExact 8
    leaf204Box leaf204Certificate leaf204InnerLog leaf204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk40RoundedFacts chi37RoundedFacts
    innerPair12RoundedFacts leaf204RoundedFacts (by rfl)

private theorem leaf204FlatSound : Sound leaf204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf204CertificateValid
    leaf204InnerLogValid leaf204CoversExact leaf204LowerChecked

private noncomputable def leaf205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (5592416/5592333) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (78871783/67108864) }, upper := { exponent := 0, mantissa := (1241/1024) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11184749/11184666) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf205InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf205LocalValidity :
    LeafFacts leaf205Box leaf205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5592416/5592333) }) = true
      norm_num [leaf205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf205CertificateValid :
    WideCertificateValid leaf205Box leaf205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi36ValidityFacts
    leaf205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf205CoverageChecked :
    coverageCheck (innerAD leaf205Box) leaf205InnerLog = true := by
  rfl'

private theorem leaf205InnerLogValid :
    leaf205InnerLog.Valid 8 (innerAD leaf205Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf205CoverageChecked

private noncomputable def leaf205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf205InputLogOnePlusV_eq :
    leaf205InputLogOnePlusV = outerEnclosure 24
      (leaf205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf205RoundedFacts : LeafRoundedFacts 8
    leaf205Certificate.logOnePlusV leaf205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf205InputLogOnePlusV_eq }

private noncomputable def leaf205Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi36InputQChi innerPair3Input
    leaf205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf205LowerChecked :
    lowerCheck 24 leaf205Box leaf205Inputs = true := by
  rfl'

private theorem leaf205CoversExact : CoversExact 8
    leaf205Box leaf205Certificate leaf205InnerLog leaf205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi36RoundedFacts
    innerPair3RoundedFacts leaf205RoundedFacts (by rfl)

private theorem leaf205FlatSound : Sound leaf205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf205CertificateValid
    leaf205InnerLogValid leaf205CoversExact leaf205LowerChecked

private noncomputable def leaf206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (65531/65536), upper := (524289/524281) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (79264973/67108864) }, upper := { exponent := 0, mantissa := (39/32) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (524285/524281) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf206InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf206LocalValidity :
    LeafFacts leaf206Box leaf206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (524289/524281) }) = true
      norm_num [leaf206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf206CertificateValid :
    WideCertificateValid leaf206Box leaf206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi36ValidityFacts
    leaf206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf206CoverageChecked :
    coverageCheck (innerAD leaf206Box) leaf206InnerLog = true := by
  rfl'

private theorem leaf206InnerLogValid :
    leaf206InnerLog.Valid 8 (innerAD leaf206Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf206CoverageChecked

private noncomputable def leaf206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf206InputLogOnePlusV_eq :
    leaf206InputLogOnePlusV = outerEnclosure 24
      (leaf206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf206RoundedFacts : LeafRoundedFacts 8
    leaf206Certificate.logOnePlusV leaf206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf206InputLogOnePlusV_eq }

private noncomputable def leaf206Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi36InputQChi innerPair3Input
    leaf206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf206LowerChecked :
    lowerCheck 24 leaf206Box leaf206Inputs = true := by
  rfl'

private theorem leaf206CoversExact : CoversExact 8
    leaf206Box leaf206Certificate leaf206InnerLog leaf206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi36RoundedFacts
    innerPair3RoundedFacts leaf206RoundedFacts (by rfl)

private theorem leaf206FlatSound : Sound leaf206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf206CertificateValid
    leaf206InnerLogValid leaf206CoversExact leaf206LowerChecked

private noncomputable def leaf207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (31/16), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097121) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (80837741/67108864) }, upper := { exponent := 0, mantissa := (159/128) } }, logOuter := sk41LogOuterCertificate, logK := sk41LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194277/4194242) } }, logDArg := sk41LogDArgCertificate }

private noncomputable def leaf207InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf207LocalValidity :
    LeafFacts leaf207Box leaf207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097121) }) = true
      norm_num [leaf207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf207CertificateValid :
    WideCertificateValid leaf207Box leaf207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk41ValidityFacts chi37ValidityFacts
    leaf207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf207CoverageChecked :
    coverageCheck (innerAD leaf207Box) leaf207InnerLog = true := by
  rfl'

private theorem leaf207InnerLogValid :
    leaf207InnerLog.Valid 8 (innerAD leaf207Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf207CoverageChecked

private noncomputable def leaf207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629221/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf207InputLogOnePlusV_eq :
    leaf207InputLogOnePlusV = outerEnclosure 24
      (leaf207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf207RoundedFacts : LeafRoundedFacts 8
    leaf207Certificate.logOnePlusV leaf207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf207InputLogOnePlusV_eq }

private noncomputable def leaf207Inputs : Inputs :=
  inputsOfCaches globalInput sk41RoundedInputs
    chi37InputQChi innerPair12Input
    leaf207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf207LowerChecked :
    lowerCheck 24 leaf207Box leaf207Inputs = true := by
  rfl'

private theorem leaf207CoversExact : CoversExact 8
    leaf207Box leaf207Certificate leaf207InnerLog leaf207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk41RoundedFacts chi37RoundedFacts
    innerPair12RoundedFacts leaf207RoundedFacts (by rfl)

private theorem leaf207FlatSound : Sound leaf207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf207CertificateValid
    leaf207InnerLogValid leaf207CoversExact leaf207LowerChecked

private noncomputable def leaf208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/16), kHi := (2), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (65531/65536), upper := (174763/174760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (81296463/67108864) }, upper := { exponent := 0, mantissa := (5/4) } }, logOuter := sk42LogOuterCertificate, logK := sk42LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (349523/349520) } }, logDArg := sk42LogDArgCertificate }

private noncomputable def leaf208InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf208LocalValidity :
    LeafFacts leaf208Box leaf208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (174763/174760) }) = true
      norm_num [leaf208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf208CertificateValid :
    WideCertificateValid leaf208Box leaf208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk42ValidityFacts chi37ValidityFacts
    leaf208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf208CoverageChecked :
    coverageCheck (innerAD leaf208Box) leaf208InnerLog = true := by
  rfl'

private theorem leaf208InnerLogValid :
    leaf208InnerLog.Valid 8 (innerAD leaf208Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf208CoverageChecked

private noncomputable def leaf208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf208InputLogOnePlusV_eq :
    leaf208InputLogOnePlusV = outerEnclosure 24
      (leaf208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf208RoundedFacts : LeafRoundedFacts 8
    leaf208Certificate.logOnePlusV leaf208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf208InputLogOnePlusV_eq }

private noncomputable def leaf208Inputs : Inputs :=
  inputsOfCaches globalInput sk42RoundedInputs
    chi37InputQChi innerPair12Input
    leaf208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf208LowerChecked :
    lowerCheck 24 leaf208Box leaf208Inputs = true := by
  rfl'

private theorem leaf208CoversExact : CoversExact 8
    leaf208Box leaf208Certificate leaf208InnerLog leaf208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk42RoundedFacts chi37RoundedFacts
    innerPair12RoundedFacts leaf208RoundedFacts (by rfl)

private theorem leaf208FlatSound : Sound leaf208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf208CertificateValid
    leaf208InnerLogValid leaf208CoversExact leaf208LowerChecked

private noncomputable def component4Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node0_sound : Sound component4Node0Box :=
  sound_of_literal_split component4Node0Box leaf163Box leaf164Box
    .k (13/8) (by rfl) (by rfl)
    leaf163FlatSound leaf164FlatSound

private noncomputable def component4Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node1_sound : Sound component4Node1Box :=
  sound_of_literal_split component4Node1Box leaf165Box leaf166Box
    .chi (3/64) (by rfl) (by rfl)
    leaf165FlatSound leaf166FlatSound

private noncomputable def component4Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node2_sound : Sound component4Node2Box :=
  sound_of_literal_split component4Node2Box leaf168Box leaf169Box
    .k (27/16) (by rfl) (by rfl)
    leaf168FlatSound leaf169FlatSound

private noncomputable def component4Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node3_sound : Sound component4Node3Box :=
  sound_of_literal_split component4Node3Box leaf167Box component4Node2Box
    .chi (3/64) (by rfl) (by rfl)
    leaf167FlatSound component4Node2_sound

private noncomputable def component4Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node4_sound : Sound component4Node4Box :=
  sound_of_literal_split component4Node4Box component4Node1Box component4Node3Box
    .k (13/8) (by rfl) (by rfl)
    component4Node1_sound component4Node3_sound

private noncomputable def component4Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node5_sound : Sound component4Node5Box :=
  sound_of_literal_split component4Node5Box component4Node0Box component4Node4Box
    .chi (1/32) (by rfl) (by rfl)
    component4Node0_sound component4Node4_sound

private noncomputable def component4Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component4Node6_sound : Sound component4Node6Box :=
  sound_of_literal_split component4Node6Box leaf170Box leaf171Box
    .k (25/16) (by rfl) (by rfl)
    leaf170FlatSound leaf171FlatSound

private noncomputable def component4Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node7_sound : Sound component4Node7Box :=
  sound_of_literal_split component4Node7Box leaf172Box leaf173Box
    .k (25/16) (by rfl) (by rfl)
    leaf172FlatSound leaf173FlatSound

private noncomputable def component4Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node8_sound : Sound component4Node8Box :=
  sound_of_literal_split component4Node8Box component4Node6Box component4Node7Box
    .chi (5/64) (by rfl) (by rfl)
    component4Node6_sound component4Node7_sound

private noncomputable def component4Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node9_sound : Sound component4Node9Box :=
  sound_of_literal_split component4Node9Box leaf174Box leaf175Box
    .k (25/16) (by rfl) (by rfl)
    leaf174FlatSound leaf175FlatSound

private noncomputable def component4Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node10_sound : Sound component4Node10Box :=
  sound_of_literal_split component4Node10Box component4Node8Box component4Node9Box
    .chi (3/32) (by rfl) (by rfl)
    component4Node8_sound component4Node9_sound

private noncomputable def component4Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component4Node11_sound : Sound component4Node11Box :=
  sound_of_literal_split component4Node11Box leaf176Box leaf177Box
    .k (27/16) (by rfl) (by rfl)
    leaf176FlatSound leaf177FlatSound

private noncomputable def component4Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node12_sound : Sound component4Node12Box :=
  sound_of_literal_split component4Node12Box leaf178Box leaf179Box
    .k (27/16) (by rfl) (by rfl)
    leaf178FlatSound leaf179FlatSound

private noncomputable def component4Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node13_sound : Sound component4Node13Box :=
  sound_of_literal_split component4Node13Box component4Node11Box component4Node12Box
    .chi (5/64) (by rfl) (by rfl)
    component4Node11_sound component4Node12_sound

private noncomputable def component4Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node14_sound : Sound component4Node14Box :=
  sound_of_literal_split component4Node14Box leaf180Box leaf181Box
    .chi (7/64) (by rfl) (by rfl)
    leaf180FlatSound leaf181FlatSound

private noncomputable def component4Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node15_sound : Sound component4Node15Box :=
  sound_of_literal_split component4Node15Box leaf182Box leaf183Box
    .chi (7/64) (by rfl) (by rfl)
    leaf182FlatSound leaf183FlatSound

private noncomputable def component4Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node16_sound : Sound component4Node16Box :=
  sound_of_literal_split component4Node16Box component4Node14Box component4Node15Box
    .k (27/16) (by rfl) (by rfl)
    component4Node14_sound component4Node15_sound

private noncomputable def component4Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node17_sound : Sound component4Node17Box :=
  sound_of_literal_split component4Node17Box component4Node13Box component4Node16Box
    .chi (3/32) (by rfl) (by rfl)
    component4Node13_sound component4Node16_sound

private noncomputable def component4Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node18_sound : Sound component4Node18Box :=
  sound_of_literal_split component4Node18Box component4Node10Box component4Node17Box
    .k (13/8) (by rfl) (by rfl)
    component4Node10_sound component4Node17_sound

private noncomputable def component4Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node19_sound : Sound component4Node19Box :=
  sound_of_literal_split component4Node19Box component4Node5Box component4Node18Box
    .chi (1/16) (by rfl) (by rfl)
    component4Node5_sound component4Node18_sound

private noncomputable def component4Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node20_sound : Sound component4Node20Box :=
  sound_of_literal_split component4Node20Box leaf184Box leaf185Box
    .k (15/8) (by rfl) (by rfl)
    leaf184FlatSound leaf185FlatSound

private noncomputable def component4Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node21_sound : Sound component4Node21Box :=
  sound_of_literal_split component4Node21Box leaf187Box leaf188Box
    .k (29/16) (by rfl) (by rfl)
    leaf187FlatSound leaf188FlatSound

private noncomputable def component4Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node22_sound : Sound component4Node22Box :=
  sound_of_literal_split component4Node22Box leaf186Box component4Node21Box
    .chi (3/64) (by rfl) (by rfl)
    leaf186FlatSound component4Node21_sound

private noncomputable def component4Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component4Node23_sound : Sound component4Node23Box :=
  sound_of_literal_split component4Node23Box leaf189Box leaf190Box
    .chi (5/128) (by rfl) (by rfl)
    leaf189FlatSound leaf190FlatSound

private noncomputable def component4Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node24_sound : Sound component4Node24Box :=
  sound_of_literal_split component4Node24Box leaf191Box leaf192Box
    .k (31/16) (by rfl) (by rfl)
    leaf191FlatSound leaf192FlatSound

private noncomputable def component4Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node25_sound : Sound component4Node25Box :=
  sound_of_literal_split component4Node25Box component4Node23Box component4Node24Box
    .chi (3/64) (by rfl) (by rfl)
    component4Node23_sound component4Node24_sound

private noncomputable def component4Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node26_sound : Sound component4Node26Box :=
  sound_of_literal_split component4Node26Box component4Node22Box component4Node25Box
    .k (15/8) (by rfl) (by rfl)
    component4Node22_sound component4Node25_sound

private noncomputable def component4Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component4Node27_sound : Sound component4Node27Box :=
  sound_of_literal_split component4Node27Box component4Node20Box component4Node26Box
    .chi (1/32) (by rfl) (by rfl)
    component4Node20_sound component4Node26_sound

private noncomputable def component4Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component4Node28_sound : Sound component4Node28Box :=
  sound_of_literal_split component4Node28Box leaf193Box leaf194Box
    .k (29/16) (by rfl) (by rfl)
    leaf193FlatSound leaf194FlatSound

private noncomputable def component4Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node29_sound : Sound component4Node29Box :=
  sound_of_literal_split component4Node29Box leaf195Box leaf196Box
    .k (29/16) (by rfl) (by rfl)
    leaf195FlatSound leaf196FlatSound

private noncomputable def component4Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node30_sound : Sound component4Node30Box :=
  sound_of_literal_split component4Node30Box component4Node28Box component4Node29Box
    .chi (5/64) (by rfl) (by rfl)
    component4Node28_sound component4Node29_sound

private noncomputable def component4Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component4Node31_sound : Sound component4Node31Box :=
  sound_of_literal_split component4Node31Box leaf197Box leaf198Box
    .k (31/16) (by rfl) (by rfl)
    leaf197FlatSound leaf198FlatSound

private noncomputable def component4Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node32_sound : Sound component4Node32Box :=
  sound_of_literal_split component4Node32Box leaf199Box leaf200Box
    .k (31/16) (by rfl) (by rfl)
    leaf199FlatSound leaf200FlatSound

private noncomputable def component4Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node33_sound : Sound component4Node33Box :=
  sound_of_literal_split component4Node33Box component4Node31Box component4Node32Box
    .chi (5/64) (by rfl) (by rfl)
    component4Node31_sound component4Node32_sound

private noncomputable def component4Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component4Node34_sound : Sound component4Node34Box :=
  sound_of_literal_split component4Node34Box component4Node30Box component4Node33Box
    .k (15/8) (by rfl) (by rfl)
    component4Node30_sound component4Node33_sound

private noncomputable def component4Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component4Node35_sound : Sound component4Node35Box :=
  sound_of_literal_split component4Node35Box leaf201Box leaf202Box
    .k (29/16) (by rfl) (by rfl)
    leaf201FlatSound leaf202FlatSound

private noncomputable def component4Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node36_sound : Sound component4Node36Box :=
  sound_of_literal_split component4Node36Box leaf203Box leaf204Box
    .k (29/16) (by rfl) (by rfl)
    leaf203FlatSound leaf204FlatSound

private noncomputable def component4Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (15/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node37_sound : Sound component4Node37Box :=
  sound_of_literal_split component4Node37Box component4Node35Box component4Node36Box
    .chi (7/64) (by rfl) (by rfl)
    component4Node35_sound component4Node36_sound

private noncomputable def component4Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component4Node38_sound : Sound component4Node38Box :=
  sound_of_literal_split component4Node38Box leaf205Box leaf206Box
    .k (31/16) (by rfl) (by rfl)
    leaf205FlatSound leaf206FlatSound

private noncomputable def component4Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node39_sound : Sound component4Node39Box :=
  sound_of_literal_split component4Node39Box leaf207Box leaf208Box
    .k (31/16) (by rfl) (by rfl)
    leaf207FlatSound leaf208FlatSound

private noncomputable def component4Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/8), kHi := (2), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node40_sound : Sound component4Node40Box :=
  sound_of_literal_split component4Node40Box component4Node38Box component4Node39Box
    .chi (7/64) (by rfl) (by rfl)
    component4Node38_sound component4Node39_sound

private noncomputable def component4Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node41_sound : Sound component4Node41Box :=
  sound_of_literal_split component4Node41Box component4Node37Box component4Node40Box
    .k (15/8) (by rfl) (by rfl)
    component4Node37_sound component4Node40_sound

private noncomputable def component4Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node42_sound : Sound component4Node42Box :=
  sound_of_literal_split component4Node42Box component4Node34Box component4Node41Box
    .chi (3/32) (by rfl) (by rfl)
    component4Node34_sound component4Node41_sound

private noncomputable def component4Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/4), kHi := (2), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component4Node43_sound : Sound component4Node43Box :=
  sound_of_literal_split component4Node43Box component4Node27Box component4Node42Box
    .chi (1/16) (by rfl) (by rfl)
    component4Node27_sound component4Node42_sound

noncomputable def component4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component4_sound : Sound component4Box :=
  sound_of_literal_split component4Box component4Node19Box component4Node43Box
    .k (7/4) (by rfl) (by rfl)
    component4Node19_sound component4Node43_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
