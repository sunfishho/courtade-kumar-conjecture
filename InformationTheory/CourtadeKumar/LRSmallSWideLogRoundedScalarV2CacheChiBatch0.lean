import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore

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

noncomputable def chi0Slice : ChiSlice :=
  { lo := (0), hi := (1/4) }

noncomputable def chi0LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (1) } }

private noncomputable def chi0QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2154488386050), upper := (0) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi0QChiValue_eq :
    chi0QChiValue =
      (chi0Slice.qChiAD 8 chi0LogChiCertificate).value := by
  norm_num [chi0QChiValue, chi0LogChiCertificate, chi0Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi0LogChi_valid :
    (if chi0Slice.lo = 0 then
      if chi0Slice.hi = 0 then true
      else decide (chi0Slice.hi ≤ 1 / 4) &&
        chi0LogChiCertificate.check
          (IntervalAD.const chi0Slice.hi).value
    else chi0LogChiCertificate.check
      chi0Slice.chiAD.value) = true := by
  norm_num [chi0Slice, chi0LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi0ValidityFacts :
    ChiFacts chi0Slice chi0LogChiCertificate :=
  { domain := by norm_num [chi0Slice]
    onePlusPositive := by
      norm_num [chi0Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi0LogChi_valid }

noncomputable def chi0InputQChi : RationalEnclosure :=
  { lower := (-4651633/16777216), upper := (0) }

set_option maxRecDepth 1000000 in
private theorem chi0InputQChi_eq :
    chi0InputQChi = outerEnclosure 24 chi0QChiValue := by
  rfl'

theorem chi0RoundedFacts :
    ChiRoundedFacts 8 chi0Slice chi0LogChiCertificate
      chi0InputQChi :=
  { coversQChi := by
      rw [chi0InputQChi_eq, chi0QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi1Slice : ChiSlice :=
  { lo := (0), hi := (1/8) }

noncomputable def chi1LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -3, mantissa := (1) } }

private noncomputable def chi1QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2585386063260), upper := (0) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi1QChiValue_eq :
    chi1QChiValue =
      (chi1Slice.qChiAD 8 chi1LogChiCertificate).value := by
  norm_num [chi1QChiValue, chi1LogChiCertificate, chi1Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi1LogChi_valid :
    (if chi1Slice.lo = 0 then
      if chi1Slice.hi = 0 then true
      else decide (chi1Slice.hi ≤ 1 / 4) &&
        chi1LogChiCertificate.check
          (IntervalAD.const chi1Slice.hi).value
    else chi1LogChiCertificate.check
      chi1Slice.chiAD.value) = true := by
  norm_num [chi1Slice, chi1LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi1ValidityFacts :
    ChiFacts chi1Slice chi1LogChiCertificate :=
  { domain := by norm_num [chi1Slice]
    onePlusPositive := by
      norm_num [chi1Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi1LogChi_valid }

noncomputable def chi1InputQChi : RationalEnclosure :=
  { lower := (-3876361/16777216), upper := (0) }

set_option maxRecDepth 1000000 in
private theorem chi1InputQChi_eq :
    chi1InputQChi = outerEnclosure 24 chi1QChiValue := by
  rfl'

theorem chi1RoundedFacts :
    ChiRoundedFacts 8 chi1Slice chi1LogChiCertificate
      chi1InputQChi :=
  { coversQChi := by
      rw [chi1InputQChi_eq, chi1QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi2Slice : ChiSlice :=
  { lo := (1/8), hi := (1/4) }

noncomputable def chi2LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -2, mantissa := (1) } }

private noncomputable def chi2QChiValue : RationalEnclosure :=
  { lower := (-597351034279/1292693031630), upper := (-199116998747/2298120945120) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi2QChiValue_eq :
    chi2QChiValue =
      (chi2Slice.qChiAD 8 chi2LogChiCertificate).value := by
  norm_num [chi2QChiValue, chi2LogChiCertificate, chi2Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi2LogChi_valid :
    (if chi2Slice.lo = 0 then
      if chi2Slice.hi = 0 then true
      else decide (chi2Slice.hi ≤ 1 / 4) &&
        chi2LogChiCertificate.check
          (IntervalAD.const chi2Slice.hi).value
    else chi2LogChiCertificate.check
      chi2Slice.chiAD.value) = true := by
  norm_num [chi2Slice, chi2LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi2ValidityFacts :
    ChiFacts chi2Slice chi2LogChiCertificate :=
  { domain := by norm_num [chi2Slice]
    onePlusPositive := by
      norm_num [chi2Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi2LogChi_valid }

noncomputable def chi2InputQChi : RationalEnclosure :=
  { lower := (-7752721/16777216), upper := (-726817/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi2InputQChi_eq :
    chi2InputQChi = outerEnclosure 24 chi2QChiValue := by
  rfl'

theorem chi2RoundedFacts :
    ChiRoundedFacts 8 chi2Slice chi2LogChiCertificate
      chi2InputQChi :=
  { coversQChi := by
      rw [chi2InputQChi_eq, chi2QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi3Slice : ChiSlice :=
  { lo := (1/4), hi := (1/2) }

noncomputable def chi3LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -1, mantissa := (1) } }

private noncomputable def chi3QChiValue : RationalEnclosure :=
  { lower := (-597351034279/1077244193025), upper := (-298675434557/17235907088400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi3QChiValue_eq :
    chi3QChiValue =
      (chi3Slice.qChiAD 8 chi3LogChiCertificate).value := by
  norm_num [chi3QChiValue, chi3LogChiCertificate, chi3Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi3LogChi_valid :
    (if chi3Slice.lo = 0 then
      if chi3Slice.hi = 0 then true
      else decide (chi3Slice.hi ≤ 1 / 4) &&
        chi3LogChiCertificate.check
          (IntervalAD.const chi3Slice.hi).value
    else chi3LogChiCertificate.check
      chi3Slice.chiAD.value) = true := by
  norm_num [chi3Slice, chi3LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi3ValidityFacts :
    ChiFacts chi3Slice chi3LogChiCertificate :=
  { domain := by norm_num [chi3Slice]
    onePlusPositive := by
      norm_num [chi3Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi3LogChi_valid }

noncomputable def chi3InputQChi : RationalEnclosure :=
  { lower := (-9303265/16777216), upper := (-145363/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi3InputQChi_eq :
    chi3InputQChi = outerEnclosure 24 chi3QChiValue := by
  rfl'

theorem chi3RoundedFacts :
    ChiRoundedFacts 8 chi3Slice chi3LogChiCertificate
      chi3InputQChi :=
  { coversQChi := by
      rw [chi3InputQChi_eq, chi3QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi4Slice : ChiSlice :=
  { lo := (1/4), hi := (3/8) }

noncomputable def chi4LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (3/2) } }

private noncomputable def chi4QChiValue : RationalEnclosure :=
  { lower := (-597351034279/1436325590700), upper := (-114943082289030696824713/771463940317382812500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi4QChiValue_eq :
    chi4QChiValue =
      (chi4Slice.qChiAD 8 chi4LogChiCertificate).value := by
  norm_num [chi4QChiValue, chi4LogChiCertificate, chi4Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi4LogChi_valid :
    (if chi4Slice.lo = 0 then
      if chi4Slice.hi = 0 then true
      else decide (chi4Slice.hi ≤ 1 / 4) &&
        chi4LogChiCertificate.check
          (IntervalAD.const chi4Slice.hi).value
    else chi4LogChiCertificate.check
      chi4Slice.chiAD.value) = true := by
  norm_num [chi4Slice, chi4LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi4ValidityFacts :
    ChiFacts chi4Slice chi4LogChiCertificate :=
  { domain := by norm_num [chi4Slice]
    onePlusPositive := by
      norm_num [chi4Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi4LogChi_valid }

noncomputable def chi4InputQChi : RationalEnclosure :=
  { lower := (-6977449/16777216), upper := (-2499695/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi4InputQChi_eq :
    chi4InputQChi = outerEnclosure 24 chi4QChiValue := by
  rfl'

theorem chi4RoundedFacts :
    ChiRoundedFacts 8 chi4Slice chi4LogChiCertificate
      chi4InputQChi :=
  { coversQChi := by
      rw [chi4InputQChi_eq, chi4QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi5Slice : ChiSlice :=
  { lo := (3/8), hi := (1/2) }

noncomputable def chi5LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (1) } }

private noncomputable def chi5QChiValue : RationalEnclosure :=
  { lower := (-3685102722216442375642/10332106343536376953125), upper := (-50840843795892131059183/330627402993164062500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi5QChiValue_eq :
    chi5QChiValue =
      (chi5Slice.qChiAD 8 chi5LogChiCertificate).value := by
  norm_num [chi5QChiValue, chi5LogChiCertificate, chi5Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi5LogChi_valid :
    (if chi5Slice.lo = 0 then
      if chi5Slice.hi = 0 then true
      else decide (chi5Slice.hi ≤ 1 / 4) &&
        chi5LogChiCertificate.check
          (IntervalAD.const chi5Slice.hi).value
    else chi5LogChiCertificate.check
      chi5Slice.chiAD.value) = true := by
  norm_num [chi5Slice, chi5LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi5ValidityFacts :
    ChiFacts chi5Slice chi5LogChiCertificate :=
  { domain := by norm_num [chi5Slice]
    onePlusPositive := by
      norm_num [chi5Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi5LogChi_valid }

noncomputable def chi5InputQChi : RationalEnclosure :=
  { lower := (-2991925/8388608), upper := (-1289923/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi5InputQChi_eq :
    chi5InputQChi = outerEnclosure 24 chi5QChiValue := by
  rfl'

theorem chi5RoundedFacts :
    ChiRoundedFacts 8 chi5Slice chi5LogChiCertificate
      chi5InputQChi :=
  { coversQChi := by
      rw [chi5InputQChi_eq, chi5QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi6Slice : ChiSlice :=
  { lo := (1/2), hi := (3/4) }

noncomputable def chi6LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (3/2) } }

private noncomputable def chi6QChiValue : RationalEnclosure :=
  { lower := (-597351034279/1723590708840), upper := (-259689880107266654041/7889972116882324218750) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi6QChiValue_eq :
    chi6QChiValue =
      (chi6Slice.qChiAD 8 chi6LogChiCertificate).value := by
  norm_num [chi6QChiValue, chi6LogChiCertificate, chi6Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi6LogChi_valid :
    (if chi6Slice.lo = 0 then
      if chi6Slice.hi = 0 then true
      else decide (chi6Slice.hi ≤ 1 / 4) &&
        chi6LogChiCertificate.check
          (IntervalAD.const chi6Slice.hi).value
    else chi6LogChiCertificate.check
      chi6Slice.chiAD.value) = true := by
  norm_num [chi6Slice, chi6LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi6ValidityFacts :
    ChiFacts chi6Slice chi6LogChiCertificate :=
  { domain := by norm_num [chi6Slice]
    onePlusPositive := by
      norm_num [chi6Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi6LogChi_valid }

noncomputable def chi6InputQChi : RationalEnclosure :=
  { lower := (-5814541/16777216), upper := (-552203/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi6InputQChi_eq :
    chi6InputQChi = outerEnclosure 24 chi6QChiValue := by
  rfl'

theorem chi6RoundedFacts :
    ChiRoundedFacts 8 chi6Slice chi6LogChiCertificate
      chi6InputQChi :=
  { coversQChi := by
      rw [chi6InputQChi_eq, chi6QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi7Slice : ChiSlice :=
  { lo := (3/4), hi := (1) }

noncomputable def chi7LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (3/2) }, upper := { exponent := 0, mantissa := (1) } }

private noncomputable def chi7QChiValue : RationalEnclosure :=
  { lower := (-7566012198856161082619/46024837348480224609375), upper := (174018280573691704900237/5891179180605468750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi7QChiValue_eq :
    chi7QChiValue =
      (chi7Slice.qChiAD 8 chi7LogChiCertificate).value := by
  norm_num [chi7QChiValue, chi7LogChiCertificate, chi7Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi7LogChi_valid :
    (if chi7Slice.lo = 0 then
      if chi7Slice.hi = 0 then true
      else decide (chi7Slice.hi ≤ 1 / 4) &&
        chi7LogChiCertificate.check
          (IntervalAD.const chi7Slice.hi).value
    else chi7LogChiCertificate.check
      chi7Slice.chiAD.value) = true := by
  norm_num [chi7Slice, chi7LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi7ValidityFacts :
    ChiFacts chi7Slice chi7LogChiCertificate :=
  { domain := by norm_num [chi7Slice]
    onePlusPositive := by
      norm_num [chi7Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi7LogChi_valid }

noncomputable def chi7InputQChi : RationalEnclosure :=
  { lower := (-2758003/16777216), upper := (495579/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi7InputQChi_eq :
    chi7InputQChi = outerEnclosure 24 chi7QChiValue := by
  rfl'

theorem chi7RoundedFacts :
    ChiRoundedFacts 8 chi7Slice chi7LogChiCertificate
      chi7InputQChi :=
  { coversQChi := by
      rw [chi7InputQChi_eq, chi7QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi8Slice : ChiSlice :=
  { lo := (1/2), hi := (5/8) }

noncomputable def chi8LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (5/4) } }

private noncomputable def chi8QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2068308850608), upper := (-44786622308534605907/342945446649301431936) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi8QChiValue_eq :
    chi8QChiValue =
      (chi8Slice.qChiAD 8 chi8LogChiCertificate).value := by
  norm_num [chi8QChiValue, chi8LogChiCertificate, chi8Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi8LogChi_valid :
    (if chi8Slice.lo = 0 then
      if chi8Slice.hi = 0 then true
      else decide (chi8Slice.hi ≤ 1 / 4) &&
        chi8LogChiCertificate.check
          (IntervalAD.const chi8Slice.hi).value
    else chi8LogChiCertificate.check
      chi8Slice.chiAD.value) = true := by
  norm_num [chi8Slice, chi8LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi8ValidityFacts :
    ChiFacts chi8Slice chi8LogChiCertificate :=
  { domain := by norm_num [chi8Slice]
    onePlusPositive := by
      norm_num [chi8Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi8LogChi_valid }

noncomputable def chi8InputQChi : RationalEnclosure :=
  { lower := (-4845451/16777216), upper := (-2191003/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi8InputQChi_eq :
    chi8InputQChi = outerEnclosure 24 chi8QChiValue := by
  rfl'

theorem chi8RoundedFacts :
    ChiRoundedFacts 8 chi8Slice chi8LogChiCertificate
      chi8InputQChi :=
  { coversQChi := by
      rw [chi8InputQChi_eq, chi8QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi9Slice : ChiSlice :=
  { lo := (5/8), hi := (3/4) }

noncomputable def chi9LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (5/4) }, upper := { exponent := -1, mantissa := (3/2) } }

private noncomputable def chi9QChiValue : RationalEnclosure :=
  { lower := (-5811981136537018061/26792613019476674370), upper := (-2110514308664863578976770884903/22894078507853603587646484375000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi9QChiValue_eq :
    chi9QChiValue =
      (chi9Slice.qChiAD 8 chi9LogChiCertificate).value := by
  norm_num [chi9QChiValue, chi9LogChiCertificate, chi9Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi9LogChi_valid :
    (if chi9Slice.lo = 0 then
      if chi9Slice.hi = 0 then true
      else decide (chi9Slice.hi ≤ 1 / 4) &&
        chi9LogChiCertificate.check
          (IntervalAD.const chi9Slice.hi).value
    else chi9LogChiCertificate.check
      chi9Slice.chiAD.value) = true := by
  norm_num [chi9Slice, chi9LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi9ValidityFacts :
    ChiFacts chi9Slice chi9LogChiCertificate :=
  { domain := by norm_num [chi9Slice]
    onePlusPositive := by
      norm_num [chi9Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi9LogChi_valid }

noncomputable def chi9InputQChi : RationalEnclosure :=
  { lower := (-1819697/8388608), upper := (-1546625/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi9InputQChi_eq :
    chi9InputQChi = outerEnclosure 24 chi9QChiValue := by
  rfl'

theorem chi9RoundedFacts :
    ChiRoundedFacts 8 chi9Slice chi9LogChiCertificate
      chi9InputQChi :=
  { coversQChi := by
      rw [chi9InputQChi_eq, chi9QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi10Slice : ChiSlice :=
  { lo := (1/8), hi := (3/16) }

noncomputable def chi10LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -3, mantissa := (3/2) } }

private noncomputable def chi10QChiValue : RationalEnclosure :=
  { lower := (-597351034279/1723590708840), upper := (-27586054071033383461199/171325108823730468750000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi10QChiValue_eq :
    chi10QChiValue =
      (chi10Slice.qChiAD 8 chi10LogChiCertificate).value := by
  norm_num [chi10QChiValue, chi10LogChiCertificate, chi10Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi10LogChi_valid :
    (if chi10Slice.lo = 0 then
      if chi10Slice.hi = 0 then true
      else decide (chi10Slice.hi ≤ 1 / 4) &&
        chi10LogChiCertificate.check
          (IntervalAD.const chi10Slice.hi).value
    else chi10LogChiCertificate.check
      chi10Slice.chiAD.value) = true := by
  norm_num [chi10Slice, chi10LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi10ValidityFacts :
    ChiFacts chi10Slice chi10LogChiCertificate :=
  { domain := by norm_num [chi10Slice]
    onePlusPositive := by
      norm_num [chi10Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi10LogChi_valid }

noncomputable def chi10InputQChi : RationalEnclosure :=
  { lower := (-5814541/16777216), upper := (-2701397/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi10InputQChi_eq :
    chi10InputQChi = outerEnclosure 24 chi10QChiValue := by
  rfl'

theorem chi10RoundedFacts :
    ChiRoundedFacts 8 chi10Slice chi10LogChiCertificate
      chi10InputQChi :=
  { coversQChi := by
      rw [chi10InputQChi_eq, chi10QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi11Slice : ChiSlice :=
  { lo := (3/16), hi := (1/4) }

noncomputable def chi11LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (3/2) }, upper := { exponent := -2, mantissa := (1) } }

private noncomputable def chi11QChiValue : RationalEnclosure :=
  { lower := (-772375893196035652217/2191658921356201171875), upper := (-876024963963855054190073/4441762080615234375000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi11QChiValue_eq :
    chi11QChiValue =
      (chi11Slice.qChiAD 8 chi11LogChiCertificate).value := by
  norm_num [chi11QChiValue, chi11LogChiCertificate, chi11Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi11LogChi_valid :
    (if chi11Slice.lo = 0 then
      if chi11Slice.hi = 0 then true
      else decide (chi11Slice.hi ≤ 1 / 4) &&
        chi11LogChiCertificate.check
          (IntervalAD.const chi11Slice.hi).value
    else chi11LogChiCertificate.check
      chi11Slice.chiAD.value) = true := by
  norm_num [chi11Slice, chi11LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi11ValidityFacts :
    ChiFacts chi11Slice chi11LogChiCertificate :=
  { domain := by norm_num [chi11Slice]
    onePlusPositive := by
      norm_num [chi11Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi11LogChi_valid }

noncomputable def chi11InputQChi : RationalEnclosure :=
  { lower := (-2956281/8388608), upper := (-206805/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi11InputQChi_eq :
    chi11InputQChi = outerEnclosure 24 chi11QChiValue := by
  rfl'

theorem chi11RoundedFacts :
    ChiRoundedFacts 8 chi11Slice chi11LogChiCertificate
      chi11InputQChi :=
  { coversQChi := by
      rw [chi11InputQChi_eq, chi11QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi12Slice : ChiSlice :=
  { lo := (0), hi := (1/16) }

noncomputable def chi12LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (1) }, upper := { exponent := -4, mantissa := (1) } }

private noncomputable def chi12QChiValue : RationalEnclosure :=
  { lower := (-597351034279/3662630256285), upper := (0) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi12QChiValue_eq :
    chi12QChiValue =
      (chi12Slice.qChiAD 8 chi12LogChiCertificate).value := by
  norm_num [chi12QChiValue, chi12LogChiCertificate, chi12Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi12LogChi_valid :
    (if chi12Slice.lo = 0 then
      if chi12Slice.hi = 0 then true
      else decide (chi12Slice.hi ≤ 1 / 4) &&
        chi12LogChiCertificate.check
          (IntervalAD.const chi12Slice.hi).value
    else chi12LogChiCertificate.check
      chi12Slice.chiAD.value) = true := by
  norm_num [chi12Slice, chi12LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi12ValidityFacts :
    ChiFacts chi12Slice chi12LogChiCertificate :=
  { domain := by norm_num [chi12Slice]
    onePlusPositive := by
      norm_num [chi12Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi12LogChi_valid }

noncomputable def chi12InputQChi : RationalEnclosure :=
  { lower := (-2736255/16777216), upper := (0) }

set_option maxRecDepth 1000000 in
private theorem chi12InputQChi_eq :
    chi12InputQChi = outerEnclosure 24 chi12QChiValue := by
  rfl'

theorem chi12RoundedFacts :
    ChiRoundedFacts 8 chi12Slice chi12LogChiCertificate
      chi12InputQChi :=
  { coversQChi := by
      rw [chi12InputQChi_eq, chi12QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi13Slice : ChiSlice :=
  { lo := (1/16), hi := (3/32) }

noncomputable def chi13LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (1) }, upper := { exponent := -4, mantissa := (3/2) } }

private noncomputable def chi13QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2441753504190), upper := (-355757958130651900651769/2781945724174804687500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi13QChiValue_eq :
    chi13QChiValue =
      (chi13Slice.qChiAD 8 chi13LogChiCertificate).value := by
  norm_num [chi13QChiValue, chi13LogChiCertificate, chi13Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi13LogChi_valid :
    (if chi13Slice.lo = 0 then
      if chi13Slice.hi = 0 then true
      else decide (chi13Slice.hi ≤ 1 / 4) &&
        chi13LogChiCertificate.check
          (IntervalAD.const chi13Slice.hi).value
    else chi13LogChiCertificate.check
      chi13Slice.chiAD.value) = true := by
  norm_num [chi13Slice, chi13LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi13ValidityFacts :
    ChiFacts chi13Slice chi13LogChiCertificate :=
  { domain := by norm_num [chi13Slice]
    onePlusPositive := by
      norm_num [chi13Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi13LogChi_valid }

noncomputable def chi13InputQChi : RationalEnclosure :=
  { lower := (-2052191/8388608), upper := (-1072743/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi13InputQChi_eq :
    chi13InputQChi = outerEnclosure 24 chi13QChiValue := by
  rfl'

theorem chi13RoundedFacts :
    ChiRoundedFacts 8 chi13Slice chi13LogChiCertificate
      chi13InputQChi :=
  { coversQChi := by
      rw [chi13InputQChi_eq, chi13QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi14Slice : ChiSlice :=
  { lo := (3/32), hi := (1/8) }

noncomputable def chi14LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (3/2) }, upper := { exponent := -3, mantissa := (1) } }

private noncomputable def chi14QChiValue : RationalEnclosure :=
  { lower := (-62255132768832967723244/230124186742401123046875), upper := (-5565584187833127012465931/33137882890905761718750000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi14QChiValue_eq :
    chi14QChiValue =
      (chi14Slice.qChiAD 8 chi14LogChiCertificate).value := by
  norm_num [chi14QChiValue, chi14LogChiCertificate, chi14Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi14LogChi_valid :
    (if chi14Slice.lo = 0 then
      if chi14Slice.hi = 0 then true
      else decide (chi14Slice.hi ≤ 1 / 4) &&
        chi14LogChiCertificate.check
          (IntervalAD.const chi14Slice.hi).value
    else chi14LogChiCertificate.check
      chi14Slice.chiAD.value) = true := by
  norm_num [chi14Slice, chi14LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi14ValidityFacts :
    ChiFacts chi14Slice chi14LogChiCertificate :=
  { domain := by norm_num [chi14Slice]
    onePlusPositive := by
      norm_num [chi14Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi14LogChi_valid }

noncomputable def chi14InputQChi : RationalEnclosure :=
  { lower := (-2269357/8388608), upper := (-704443/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi14InputQChi_eq :
    chi14InputQChi = outerEnclosure 24 chi14QChiValue := by
  rfl'

theorem chi14RoundedFacts :
    ChiRoundedFacts 8 chi14Slice chi14LogChiCertificate
      chi14InputQChi :=
  { coversQChi := by
      rw [chi14InputQChi_eq, chi14QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi15Slice : ChiSlice :=
  { lo := (1/4), hi := (5/16) }

noncomputable def chi15LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (5/4) } }

private noncomputable def chi15QChiValue : RationalEnclosure :=
  { lower := (-597351034279/1723590708840), upper := (-985148261137668021137/4616573320279057737600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi15QChiValue_eq :
    chi15QChiValue =
      (chi15Slice.qChiAD 8 chi15LogChiCertificate).value := by
  norm_num [chi15QChiValue, chi15LogChiCertificate, chi15Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi15LogChi_valid :
    (if chi15Slice.lo = 0 then
      if chi15Slice.hi = 0 then true
      else decide (chi15Slice.hi ≤ 1 / 4) &&
        chi15LogChiCertificate.check
          (IntervalAD.const chi15Slice.hi).value
    else chi15LogChiCertificate.check
      chi15Slice.chiAD.value) = true := by
  norm_num [chi15Slice, chi15LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi15ValidityFacts :
    ChiFacts chi15Slice chi15LogChiCertificate :=
  { domain := by norm_num [chi15Slice]
    onePlusPositive := by
      norm_num [chi15Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi15LogChi_valid }

noncomputable def chi15InputQChi : RationalEnclosure :=
  { lower := (-5814541/16777216), upper := (-1790077/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi15InputQChi_eq :
    chi15InputQChi = outerEnclosure 24 chi15QChiValue := by
  rfl'

theorem chi15RoundedFacts :
    ChiRoundedFacts 8 chi15Slice chi15LogChiCertificate
      chi15InputQChi :=
  { coversQChi := by
      rw [chi15InputQChi_eq, chi15QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi16Slice : ChiSlice :=
  { lo := (5/16), hi := (3/8) }

noncomputable def chi16LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (5/4) }, upper := { exponent := -2, mantissa := (3/2) } }

private noncomputable def chi16QChiValue : RationalEnclosure :=
  { lower := (-7191657786880100557/21640187438808083145), upper := (-13721315721119606963748095726959/63398986637133056088867187500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi16QChiValue_eq :
    chi16QChiValue =
      (chi16Slice.qChiAD 8 chi16LogChiCertificate).value := by
  norm_num [chi16QChiValue, chi16LogChiCertificate, chi16Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi16LogChi_valid :
    (if chi16Slice.lo = 0 then
      if chi16Slice.hi = 0 then true
      else decide (chi16Slice.hi ≤ 1 / 4) &&
        chi16LogChiCertificate.check
          (IntervalAD.const chi16Slice.hi).value
    else chi16LogChiCertificate.check
      chi16Slice.chiAD.value) = true := by
  norm_num [chi16Slice, chi16LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi16ValidityFacts :
    ChiFacts chi16Slice chi16LogChiCertificate :=
  { domain := by norm_num [chi16Slice]
    onePlusPositive := by
      norm_num [chi16Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi16LogChi_valid }

noncomputable def chi16InputQChi : RationalEnclosure :=
  { lower := (-5575553/16777216), upper := (-3631059/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi16InputQChi_eq :
    chi16InputQChi = outerEnclosure 24 chi16QChiValue := by
  rfl'

theorem chi16RoundedFacts :
    ChiRoundedFacts 8 chi16Slice chi16LogChiCertificate
      chi16InputQChi :=
  { coversQChi := by
      rw [chi16InputQChi_eq, chi16QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi17Slice : ChiSlice :=
  { lo := (3/8), hi := (7/16) }

noncomputable def chi17LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -2, mantissa := (7/4) } }

private noncomputable def chi17QChiValue : RationalEnclosure :=
  { lower := (-12897859527757548314747/41328425374145507812500), upper := (-8504019627747958997058872051824929604253/40428935807237653628086245439453125000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi17QChiValue_eq :
    chi17QChiValue =
      (chi17Slice.qChiAD 8 chi17LogChiCertificate).value := by
  norm_num [chi17QChiValue, chi17LogChiCertificate, chi17Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi17LogChi_valid :
    (if chi17Slice.lo = 0 then
      if chi17Slice.hi = 0 then true
      else decide (chi17Slice.hi ≤ 1 / 4) &&
        chi17LogChiCertificate.check
          (IntervalAD.const chi17Slice.hi).value
    else chi17LogChiCertificate.check
      chi17Slice.chiAD.value) = true := by
  norm_num [chi17Slice, chi17LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi17ValidityFacts :
    ChiFacts chi17Slice chi17LogChiCertificate :=
  { domain := by norm_num [chi17Slice]
    onePlusPositive := by
      norm_num [chi17Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi17LogChi_valid }

noncomputable def chi17InputQChi : RationalEnclosure :=
  { lower := (-1308967/4194304), upper := (-3529001/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi17InputQChi_eq :
    chi17InputQChi = outerEnclosure 24 chi17QChiValue := by
  rfl'

theorem chi17RoundedFacts :
    ChiRoundedFacts 8 chi17Slice chi17LogChiCertificate
      chi17InputQChi :=
  { coversQChi := by
      rw [chi17InputQChi_eq, chi17QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi18Slice : ChiSlice :=
  { lo := (7/16), hi := (1/2) }

noncomputable def chi18LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (7/4) }, upper := { exponent := -1, mantissa := (1) } }

private noncomputable def chi18QChiValue : RationalEnclosure :=
  { lower := (-41622204886463903719705708/144752553379759990612448655), upper := (-23813448659862136747910253749/120434124411960312189557280960) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi18QChiValue_eq :
    chi18QChiValue =
      (chi18Slice.qChiAD 8 chi18LogChiCertificate).value := by
  norm_num [chi18QChiValue, chi18LogChiCertificate, chi18Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi18LogChi_valid :
    (if chi18Slice.lo = 0 then
      if chi18Slice.hi = 0 then true
      else decide (chi18Slice.hi ≤ 1 / 4) &&
        chi18LogChiCertificate.check
          (IntervalAD.const chi18Slice.hi).value
    else chi18LogChiCertificate.check
      chi18Slice.chiAD.value) = true := by
  norm_num [chi18Slice, chi18LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi18ValidityFacts :
    ChiFacts chi18Slice chi18LogChiCertificate :=
  { domain := by norm_num [chi18Slice]
    onePlusPositive := by
      norm_num [chi18Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi18LogChi_valid }

noncomputable def chi18InputQChi : RationalEnclosure :=
  { lower := (-75377/262144), upper := (-207335/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi18InputQChi_eq :
    chi18InputQChi = outerEnclosure 24 chi18QChiValue := by
  rfl'

theorem chi18RoundedFacts :
    ChiRoundedFacts 8 chi18Slice chi18LogChiCertificate
      chi18InputQChi :=
  { coversQChi := by
      rw [chi18InputQChi_eq, chi18QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi19Slice : ChiSlice :=
  { lo := (3/4), hi := (7/8) }

noncomputable def chi19LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (7/4) } }

private noncomputable def chi19QChiValue : RationalEnclosure :=
  { lower := (-7566012198856161082619/52599814112548828125000), upper := (-758462108871534503574404842200622357231/16778807350829856248810497119140625000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi19QChiValue_eq :
    chi19QChiValue =
      (chi19Slice.qChiAD 8 chi19LogChiCertificate).value := by
  norm_num [chi19QChiValue, chi19LogChiCertificate, chi19Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi19LogChi_valid :
    (if chi19Slice.lo = 0 then
      if chi19Slice.hi = 0 then true
      else decide (chi19Slice.hi ≤ 1 / 4) &&
        chi19LogChiCertificate.check
          (IntervalAD.const chi19Slice.hi).value
    else chi19LogChiCertificate.check
      chi19Slice.chiAD.value) = true := by
  norm_num [chi19Slice, chi19LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi19ValidityFacts :
    ChiFacts chi19Slice chi19LogChiCertificate :=
  { domain := by norm_num [chi19Slice]
    onePlusPositive := by
      norm_num [chi19Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi19LogChi_valid }

noncomputable def chi19InputQChi : RationalEnclosure :=
  { lower := (-2413253/16777216), upper := (-379195/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi19InputQChi_eq :
    chi19InputQChi = outerEnclosure 24 chi19QChiValue := by
  rfl'

theorem chi19RoundedFacts :
    ChiRoundedFacts 8 chi19Slice chi19LogChiCertificate
      chi19InputQChi :=
  { coversQChi := by
      rw [chi19InputQChi_eq, chi19QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi20Slice : ChiSlice :=
  { lo := (7/8), hi := (1) }

noncomputable def chi20LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (7/4) }, upper := { exponent := 0, mantissa := (1) } }

private noncomputable def chi20QChiValue : RationalEnclosure :=
  { lower := (-87400751807576468374337726/1227249909089269485627282075), upper := (2053917667478047006796936561/314175976726852988320584211200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi20QChiValue_eq :
    chi20QChiValue =
      (chi20Slice.qChiAD 8 chi20LogChiCertificate).value := by
  norm_num [chi20QChiValue, chi20LogChiCertificate, chi20Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi20LogChi_valid :
    (if chi20Slice.lo = 0 then
      if chi20Slice.hi = 0 then true
      else decide (chi20Slice.hi ≤ 1 / 4) &&
        chi20LogChiCertificate.check
          (IntervalAD.const chi20Slice.hi).value
    else chi20LogChiCertificate.check
      chi20Slice.chiAD.value) = true := by
  norm_num [chi20Slice, chi20LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi20ValidityFacts :
    ChiFacts chi20Slice chi20LogChiCertificate :=
  { domain := by norm_num [chi20Slice]
    onePlusPositive := by
      norm_num [chi20Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi20LogChi_valid }

noncomputable def chi20InputQChi : RationalEnclosure :=
  { lower := (-1194819/16777216), upper := (109681/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi20InputQChi_eq :
    chi20InputQChi = outerEnclosure 24 chi20QChiValue := by
  rfl'

theorem chi20RoundedFacts :
    ChiRoundedFacts 8 chi20Slice chi20LogChiCertificate
      chi20InputQChi :=
  { coversQChi := by
      rw [chi20InputQChi_eq, chi20QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi21Slice : ChiSlice :=
  { lo := (1/2), hi := (9/16) }

noncomputable def chi21LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (9/8) } }

private noncomputable def chi21QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2298120945120), upper := (-251231382830443014771269982906391/1393029395675790842788149659328000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi21QChiValue_eq :
    chi21QChiValue =
      (chi21Slice.qChiAD 8 chi21LogChiCertificate).value := by
  norm_num [chi21QChiValue, chi21LogChiCertificate, chi21Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi21LogChi_valid :
    (if chi21Slice.lo = 0 then
      if chi21Slice.hi = 0 then true
      else decide (chi21Slice.hi ≤ 1 / 4) &&
        chi21LogChiCertificate.check
          (IntervalAD.const chi21Slice.hi).value
    else chi21LogChiCertificate.check
      chi21Slice.chiAD.value) = true := by
  norm_num [chi21Slice, chi21LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi21ValidityFacts :
    ChiFacts chi21Slice chi21LogChiCertificate :=
  { domain := by norm_num [chi21Slice]
    onePlusPositive := by
      norm_num [chi21Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi21LogChi_valid }

noncomputable def chi21InputQChi : RationalEnclosure :=
  { lower := (-2180453/8388608), upper := (-3025753/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi21InputQChi_eq :
    chi21InputQChi = outerEnclosure 24 chi21QChiValue := by
  rfl'

theorem chi21RoundedFacts :
    ChiRoundedFacts 8 chi21Slice chi21LogChiCertificate
      chi21InputQChi :=
  { coversQChi := by
      rw [chi21InputQChi_eq, chi21QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi22Slice : ChiSlice :=
  { lo := (9/16), hi := (5/8) }

noncomputable def chi22LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (9/8) }, upper := { exponent := -1, mantissa := (5/4) } }

private noncomputable def chi22QChiValue : RationalEnclosure :=
  { lower := (-202760211738205330322430200657/881008174348528434799052983950), upper := (-889373080114517561045826164675370955559/5577584953973239412841856586105041848000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi22QChiValue_eq :
    chi22QChiValue =
      (chi22Slice.qChiAD 8 chi22LogChiCertificate).value := by
  norm_num [chi22QChiValue, chi22LogChiCertificate, chi22Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi22LogChi_valid :
    (if chi22Slice.lo = 0 then
      if chi22Slice.hi = 0 then true
      else decide (chi22Slice.hi ≤ 1 / 4) &&
        chi22LogChiCertificate.check
          (IntervalAD.const chi22Slice.hi).value
    else chi22LogChiCertificate.check
      chi22Slice.chiAD.value) = true := by
  norm_num [chi22Slice, chi22LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi22ValidityFacts :
    ChiFacts chi22Slice chi22LogChiCertificate :=
  { domain := by norm_num [chi22Slice]
    onePlusPositive := by
      norm_num [chi22Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi22LogChi_valid }

noncomputable def chi22InputQChi : RationalEnclosure :=
  { lower := (-965301/4194304), upper := (-334401/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi22InputQChi_eq :
    chi22InputQChi = outerEnclosure 24 chi22QChiValue := by
  rfl'

theorem chi22RoundedFacts :
    ChiRoundedFacts 8 chi22Slice chi22LogChiCertificate
      chi22InputQChi :=
  { coversQChi := by
      rw [chi22InputQChi_eq, chi22QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi23Slice : ChiSlice :=
  { lo := (5/8), hi := (11/16) }

noncomputable def chi23LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (5/4) }, upper := { exponent := -1, mantissa := (11/8) } }

private noncomputable def chi23QChiValue : RationalEnclosure :=
  { lower := (-5811981136537018061/29228305112156372040), upper := (-19112298095040083859914397037077102266099/140570056527305279734186673589176681075328) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi23QChiValue_eq :
    chi23QChiValue =
      (chi23Slice.qChiAD 8 chi23LogChiCertificate).value := by
  norm_num [chi23QChiValue, chi23LogChiCertificate, chi23Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi23LogChi_valid :
    (if chi23Slice.lo = 0 then
      if chi23Slice.hi = 0 then true
      else decide (chi23Slice.hi ≤ 1 / 4) &&
        chi23LogChiCertificate.check
          (IntervalAD.const chi23Slice.hi).value
    else chi23LogChiCertificate.check
      chi23Slice.chiAD.value) = true := by
  norm_num [chi23Slice, chi23LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi23ValidityFacts :
    ChiFacts chi23Slice chi23LogChiCertificate :=
  { domain := by norm_num [chi23Slice]
    onePlusPositive := by
      norm_num [chi23Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi23LogChi_valid }

noncomputable def chi23InputQChi : RationalEnclosure :=
  { lower := (-3336111/16777216), upper := (-2281077/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi23InputQChi_eq :
    chi23InputQChi = outerEnclosure 24 chi23QChiValue := by
  rfl'

theorem chi23RoundedFacts :
    ChiRoundedFacts 8 chi23Slice chi23LogChiCertificate
      chi23InputQChi :=
  { coversQChi := by
      rw [chi23InputQChi_eq, chi23QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi24Slice : ChiSlice :=
  { lo := (11/16), hi := (3/4) }

noncomputable def chi24LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (11/8) }, upper := { exponent := -1, mantissa := (3/2) } }

private noncomputable def chi24QChiValue : RationalEnclosure :=
  { lower := (-980424777423170378037251695097/5887361137142697177740723159211), upper := (-6674008275566588033372307439908037570747837/60368449160154609732692962081753417968750000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi24QChiValue_eq :
    chi24QChiValue =
      (chi24Slice.qChiAD 8 chi24LogChiCertificate).value := by
  norm_num [chi24QChiValue, chi24LogChiCertificate, chi24Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi24LogChi_valid :
    (if chi24Slice.lo = 0 then
      if chi24Slice.hi = 0 then true
      else decide (chi24Slice.hi ≤ 1 / 4) &&
        chi24LogChiCertificate.check
          (IntervalAD.const chi24Slice.hi).value
    else chi24LogChiCertificate.check
      chi24Slice.chiAD.value) = true := by
  norm_num [chi24Slice, chi24LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi24ValidityFacts :
    ChiFacts chi24Slice chi24LogChiCertificate :=
  { domain := by norm_num [chi24Slice]
    onePlusPositive := by
      norm_num [chi24Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi24LogChi_valid }

noncomputable def chi24InputQChi : RationalEnclosure :=
  { lower := (-2793917/16777216), upper := (-1854797/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi24InputQChi_eq :
    chi24InputQChi = outerEnclosure 24 chi24QChiValue := by
  rfl'

theorem chi24RoundedFacts :
    ChiRoundedFacts 8 chi24Slice chi24LogChiCertificate
      chi24InputQChi :=
  { coversQChi := by
      rw [chi24InputQChi_eq, chi24QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi25Slice : ChiSlice :=
  { lo := (1/8), hi := (5/32) }

noncomputable def chi25LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -3, mantissa := (5/4) } }

private noncomputable def chi25QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2068308850608), upper := (-2877098301710633097907/14641132530027868824960) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi25QChiValue_eq :
    chi25QChiValue =
      (chi25Slice.qChiAD 8 chi25LogChiCertificate).value := by
  norm_num [chi25QChiValue, chi25LogChiCertificate, chi25Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi25LogChi_valid :
    (if chi25Slice.lo = 0 then
      if chi25Slice.hi = 0 then true
      else decide (chi25Slice.hi ≤ 1 / 4) &&
        chi25LogChiCertificate.check
          (IntervalAD.const chi25Slice.hi).value
    else chi25LogChiCertificate.check
      chi25Slice.chiAD.value) = true := by
  norm_num [chi25Slice, chi25LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi25ValidityFacts :
    ChiFacts chi25Slice chi25LogChiCertificate :=
  { domain := by norm_num [chi25Slice]
    onePlusPositive := by
      norm_num [chi25Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi25LogChi_valid }

noncomputable def chi25InputQChi : RationalEnclosure :=
  { lower := (-4845451/16777216), upper := (-3296855/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi25InputQChi_eq :
    chi25InputQChi = outerEnclosure 24 chi25QChiValue := by
  rfl'

theorem chi25RoundedFacts :
    ChiRoundedFacts 8 chi25Slice chi25LogChiCertificate
      chi25InputQChi :=
  { coversQChi := by
      rw [chi25InputQChi_eq, chi25QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi26Slice : ChiSlice :=
  { lo := (5/32), hi := (3/16) }

noncomputable def chi26LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (5/4) }, upper := { exponent := -3, mantissa := (3/2) } }

private noncomputable def chi26QChiValue : RationalEnclosure :=
  { lower := (-22954650010983384167/76255898593895150130), upper := (-3068140184253194010106681507409/14149043684414139184277343750000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi26QChiValue_eq :
    chi26QChiValue =
      (chi26Slice.qChiAD 8 chi26LogChiCertificate).value := by
  norm_num [chi26QChiValue, chi26LogChiCertificate, chi26Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi26LogChi_valid :
    (if chi26Slice.lo = 0 then
      if chi26Slice.hi = 0 then true
      else decide (chi26Slice.hi ≤ 1 / 4) &&
        chi26LogChiCertificate.check
          (IntervalAD.const chi26Slice.hi).value
    else chi26LogChiCertificate.check
      chi26Slice.chiAD.value) = true := by
  norm_num [chi26Slice, chi26LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi26ValidityFacts :
    ChiFacts chi26Slice chi26LogChiCertificate :=
  { domain := by norm_num [chi26Slice]
    onePlusPositive := by
      norm_num [chi26Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi26LogChi_valid }

noncomputable def chi26InputQChi : RationalEnclosure :=
  { lower := (-1262575/4194304), upper := (-909511/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi26InputQChi_eq :
    chi26InputQChi = outerEnclosure 24 chi26QChiValue := by
  rfl'

theorem chi26RoundedFacts :
    ChiRoundedFacts 8 chi26Slice chi26LogChiCertificate
      chi26InputQChi :=
  { coversQChi := by
      rw [chi26InputQChi_eq, chi26QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi27Slice : ChiSlice :=
  { lo := (3/16), hi := (7/32) }

noncomputable def chi27LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (3/2) }, upper := { exponent := -3, mantissa := (7/4) } }

private noncomputable def chi27QChiValue : RationalEnclosure :=
  { lower := (-772375893196035652217/2504753052978515625000), upper := (-9106138861725759984822712731504110849/39430716099661999842597333984375000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi27QChiValue_eq :
    chi27QChiValue =
      (chi27Slice.qChiAD 8 chi27LogChiCertificate).value := by
  norm_num [chi27QChiValue, chi27LogChiCertificate, chi27Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi27LogChi_valid :
    (if chi27Slice.lo = 0 then
      if chi27Slice.hi = 0 then true
      else decide (chi27Slice.hi ≤ 1 / 4) &&
        chi27LogChiCertificate.check
          (IntervalAD.const chi27Slice.hi).value
    else chi27LogChiCertificate.check
      chi27Slice.chiAD.value) = true := by
  norm_num [chi27Slice, chi27LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi27ValidityFacts :
    ChiFacts chi27Slice chi27LogChiCertificate :=
  { domain := by norm_num [chi27Slice]
    onePlusPositive := by
      norm_num [chi27Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi27LogChi_valid }

noncomputable def chi27InputQChi : RationalEnclosure :=
  { lower := (-5173491/16777216), upper := (-1937267/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi27InputQChi_eq :
    chi27InputQChi = outerEnclosure 24 chi27QChiValue := by
  rfl'

theorem chi27RoundedFacts :
    ChiRoundedFacts 8 chi27Slice chi27LogChiCertificate
      chi27InputQChi :=
  { coversQChi := by
      rw [chi27InputQChi_eq, chi27QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi28Slice : ChiSlice :=
  { lo := (7/32), hi := (1/4) }

noncomputable def chi28LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (7/4) }, upper := { exponent := -2, mantissa := (1) } }

private noncomputable def chi28QChiValue : RationalEnclosure :=
  { lower := (-331592191746828342779336894/1063616587877366887543644465), upper := (-2514709100238300474175994623/10472532557561766277352807040) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi28QChiValue_eq :
    chi28QChiValue =
      (chi28Slice.qChiAD 8 chi28LogChiCertificate).value := by
  norm_num [chi28QChiValue, chi28LogChiCertificate, chi28Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi28LogChi_valid :
    (if chi28Slice.lo = 0 then
      if chi28Slice.hi = 0 then true
      else decide (chi28Slice.hi ≤ 1 / 4) &&
        chi28LogChiCertificate.check
          (IntervalAD.const chi28Slice.hi).value
    else chi28LogChiCertificate.check
      chi28Slice.chiAD.value) = true := by
  norm_num [chi28Slice, chi28LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi28ValidityFacts :
    ChiFacts chi28Slice chi28LogChiCertificate :=
  { domain := by norm_num [chi28Slice]
    onePlusPositive := by
      norm_num [chi28Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi28LogChi_valid }

noncomputable def chi28InputQChi : RationalEnclosure :=
  { lower := (-5230451/16777216), upper := (-503577/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi28InputQChi_eq :
    chi28InputQChi = outerEnclosure 24 chi28QChiValue := by
  rfl'

theorem chi28RoundedFacts :
    ChiRoundedFacts 8 chi28Slice chi28LogChiCertificate
      chi28InputQChi :=
  { coversQChi := by
      rw [chi28InputQChi_eq, chi28QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi29Slice : ChiSlice :=
  { lo := (0), hi := (1/32) }

noncomputable def chi29LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (1) }, upper := { exponent := -5, mantissa := (1) } }

private noncomputable def chi29QChiValue : RationalEnclosure :=
  { lower := (-597351034279/5687849339172), upper := (0) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi29QChiValue_eq :
    chi29QChiValue =
      (chi29Slice.qChiAD 8 chi29LogChiCertificate).value := by
  norm_num [chi29QChiValue, chi29LogChiCertificate, chi29Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi29LogChi_valid :
    (if chi29Slice.lo = 0 then
      if chi29Slice.hi = 0 then true
      else decide (chi29Slice.hi ≤ 1 / 4) &&
        chi29LogChiCertificate.check
          (IntervalAD.const chi29Slice.hi).value
    else chi29LogChiCertificate.check
      chi29Slice.chiAD.value) = true := by
  norm_num [chi29Slice, chi29LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi29ValidityFacts :
    ChiFacts chi29Slice chi29LogChiCertificate :=
  { domain := by norm_num [chi29Slice]
    onePlusPositive := by
      norm_num [chi29Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi29LogChi_valid }

noncomputable def chi29InputQChi : RationalEnclosure :=
  { lower := (-880991/8388608), upper := (0) }

set_option maxRecDepth 1000000 in
private theorem chi29InputQChi_eq :
    chi29InputQChi = outerEnclosure 24 chi29QChiValue := by
  rfl'

theorem chi29RoundedFacts :
    ChiRoundedFacts 8 chi29Slice chi29LogChiCertificate
      chi29InputQChi :=
  { coversQChi := by
      rw [chi29InputQChi_eq, chi29QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi30Slice : ChiSlice :=
  { lo := (1/32), hi := (3/64) }

noncomputable def chi30LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (1) }, upper := { exponent := -5, mantissa := (3/2) } }

private noncomputable def chi30QChiValue : RationalEnclosure :=
  { lower := (-597351034279/3791899559448), upper := (-2042638528097006222515043/23259637800569091796875000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi30QChiValue_eq :
    chi30QChiValue =
      (chi30Slice.qChiAD 8 chi30LogChiCertificate).value := by
  norm_num [chi30QChiValue, chi30LogChiCertificate, chi30Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi30LogChi_valid :
    (if chi30Slice.lo = 0 then
      if chi30Slice.hi = 0 then true
      else decide (chi30Slice.hi ≤ 1 / 4) &&
        chi30LogChiCertificate.check
          (IntervalAD.const chi30Slice.hi).value
    else chi30LogChiCertificate.check
      chi30Slice.chiAD.value) = true := by
  norm_num [chi30Slice, chi30LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi30ValidityFacts :
    ChiFacts chi30Slice chi30LogChiCertificate :=
  { domain := by norm_num [chi30Slice]
    onePlusPositive := by
      norm_num [chi30Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi30LogChi_valid }

noncomputable def chi30InputQChi : RationalEnclosure :=
  { lower := (-2642973/16777216), upper := (-736679/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi30InputQChi_eq :
    chi30InputQChi = outerEnclosure 24 chi30QChiValue := by
  rfl'

theorem chi30RoundedFacts :
    ChiRoundedFacts 8 chi30Slice chi30LogChiCertificate
      chi30InputQChi :=
  { coversQChi := by
      rw [chi30InputQChi_eq, chi30QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi31Slice : ChiSlice :=
  { lo := (3/64), hi := (1/16) }

noncomputable def chi31LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (3/2) }, upper := { exponent := -4, mantissa := (1) } }

private noncomputable def chi31QChiValue : RationalEnclosure :=
  { lower := (-7316803602317445751829/40047585744781494140625), upper := (-57398958119648407832372983/479289506193544921875000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi31QChiValue_eq :
    chi31QChiValue =
      (chi31Slice.qChiAD 8 chi31LogChiCertificate).value := by
  norm_num [chi31QChiValue, chi31LogChiCertificate, chi31Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi31LogChi_valid :
    (if chi31Slice.lo = 0 then
      if chi31Slice.hi = 0 then true
      else decide (chi31Slice.hi ≤ 1 / 4) &&
        chi31LogChiCertificate.check
          (IntervalAD.const chi31Slice.hi).value
    else chi31LogChiCertificate.check
      chi31Slice.chiAD.value) = true := by
  norm_num [chi31Slice, chi31LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi31ValidityFacts :
    ChiFacts chi31Slice chi31LogChiCertificate :=
  { domain := by norm_num [chi31Slice]
    onePlusPositive := by
      norm_num [chi31Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi31LogChi_valid }

noncomputable def chi31InputQChi : RationalEnclosure :=
  { lower := (-766311/4194304), upper := (-2009213/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi31InputQChi_eq :
    chi31InputQChi = outerEnclosure 24 chi31QChiValue := by
  rfl'

theorem chi31RoundedFacts :
    ChiRoundedFacts 8 chi31Slice chi31LogChiCertificate
      chi31InputQChi :=
  { coversQChi := by
      rw [chi31InputQChi_eq, chi31QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi32Slice : ChiSlice :=
  { lo := (1/16), hi := (5/64) }

noncomputable def chi32LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (1) }, upper := { exponent := -4, mantissa := (5/4) } }

private noncomputable def chi32QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2930104205028), upper := (-7518131802879509310197/51573719092260330725760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi32QChiValue_eq :
    chi32QChiValue =
      (chi32Slice.qChiAD 8 chi32LogChiCertificate).value := by
  norm_num [chi32QChiValue, chi32LogChiCertificate, chi32Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi32LogChi_valid :
    (if chi32Slice.lo = 0 then
      if chi32Slice.hi = 0 then true
      else decide (chi32Slice.hi ≤ 1 / 4) &&
        chi32LogChiCertificate.check
          (IntervalAD.const chi32Slice.hi).value
    else chi32LogChiCertificate.check
      chi32Slice.chiAD.value) = true := by
  norm_num [chi32Slice, chi32LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi32ValidityFacts :
    ChiFacts chi32Slice chi32LogChiCertificate :=
  { domain := by norm_num [chi32Slice]
    onePlusPositive := by
      norm_num [chi32Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi32LogChi_valid }

noncomputable def chi32InputQChi : RationalEnclosure :=
  { lower := (-1710159/8388608), upper := (-2445689/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi32InputQChi_eq :
    chi32InputQChi = outerEnclosure 24 chi32QChiValue := by
  rfl'

theorem chi32RoundedFacts :
    ChiRoundedFacts 8 chi32Slice chi32LogChiCertificate
      chi32InputQChi :=
  { coversQChi := by
      rw [chi32InputQChi_eq, chi32QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi33Slice : ChiSlice :=
  { lo := (5/64), hi := (3/32) }

noncomputable def chi33LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (5/4) }, upper := { exponent := -4, mantissa := (3/2) } }

private noncomputable def chi33QChiValue : RationalEnclosure :=
  { lower := (-286599858620059702/1292790418422301071), upper := (-4824381521136010177877908411859/28817721198696843676757812500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi33QChiValue_eq :
    chi33QChiValue =
      (chi33Slice.qChiAD 8 chi33LogChiCertificate).value := by
  norm_num [chi33QChiValue, chi33LogChiCertificate, chi33Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi33LogChi_valid :
    (if chi33Slice.lo = 0 then
      if chi33Slice.hi = 0 then true
      else decide (chi33Slice.hi ≤ 1 / 4) &&
        chi33LogChiCertificate.check
          (IntervalAD.const chi33Slice.hi).value
    else chi33LogChiCertificate.check
      chi33Slice.chiAD.value) = true := by
  norm_num [chi33Slice, chi33LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi33ValidityFacts :
    ChiFacts chi33Slice chi33LogChiCertificate :=
  { domain := by norm_num [chi33Slice]
    onePlusPositive := by
      norm_num [chi33Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi33LogChi_valid }

noncomputable def chi33InputQChi : RationalEnclosure :=
  { lower := (-929839/4194304), upper := (-2808677/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi33InputQChi_eq :
    chi33InputQChi = outerEnclosure 24 chi33QChiValue := by
  rfl'

theorem chi33RoundedFacts :
    ChiRoundedFacts 8 chi33Slice chi33LogChiCertificate
      chi33InputQChi :=
  { coversQChi := by
      rw [chi33InputQChi_eq, chi33QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi34Slice : ChiSlice :=
  { lo := (3/16), hi := (13/64) }

noncomputable def chi34LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (3/2) }, upper := { exponent := -3, mantissa := (13/8) } }

private noncomputable def chi34QChiValue : RationalEnclosure :=
  { lower := (-772375893196035652217/2697426364746093750000), upper := (-19696196135705047684399304803166081699/79530145917526442536327617187500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi34QChiValue_eq :
    chi34QChiValue =
      (chi34Slice.qChiAD 8 chi34LogChiCertificate).value := by
  norm_num [chi34QChiValue, chi34LogChiCertificate, chi34Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi34LogChi_valid :
    (if chi34Slice.lo = 0 then
      if chi34Slice.hi = 0 then true
      else decide (chi34Slice.hi ≤ 1 / 4) &&
        chi34LogChiCertificate.check
          (IntervalAD.const chi34Slice.hi).value
    else chi34LogChiCertificate.check
      chi34Slice.chiAD.value) = true := by
  norm_num [chi34Slice, chi34LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi34ValidityFacts :
    ChiFacts chi34Slice chi34LogChiCertificate :=
  { domain := by norm_num [chi34Slice]
    onePlusPositive := by
      norm_num [chi34Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi34LogChi_valid }

noncomputable def chi34InputQChi : RationalEnclosure :=
  { lower := (-1200989/4194304), upper := (-2077497/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi34InputQChi_eq :
    chi34InputQChi = outerEnclosure 24 chi34QChiValue := by
  rfl'

theorem chi34RoundedFacts :
    ChiRoundedFacts 8 chi34Slice chi34LogChiCertificate
      chi34InputQChi :=
  { coversQChi := by
      rw [chi34InputQChi_eq, chi34QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi35Slice : ChiSlice :=
  { lo := (13/64), hi := (7/32) }

noncomputable def chi35LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (13/8) }, upper := { exponent := -3, mantissa := (7/4) } }

private noncomputable def chi35QChiValue : RationalEnclosure :=
  { lower := (-931637544808289956327813/3214692213929489887784190), upper := (-898016878365087131549183451008746994931109/3554907962456219416918953276176262308508480) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi35QChiValue_eq :
    chi35QChiValue =
      (chi35Slice.qChiAD 8 chi35LogChiCertificate).value := by
  norm_num [chi35QChiValue, chi35LogChiCertificate, chi35Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi35LogChi_valid :
    (if chi35Slice.lo = 0 then
      if chi35Slice.hi = 0 then true
      else decide (chi35Slice.hi ≤ 1 / 4) &&
        chi35LogChiCertificate.check
          (IntervalAD.const chi35Slice.hi).value
    else chi35LogChiCertificate.check
      chi35Slice.chiAD.value) = true := by
  norm_num [chi35Slice, chi35LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi35ValidityFacts :
    ChiFacts chi35Slice chi35LogChiCertificate :=
  { domain := by norm_num [chi35Slice]
    onePlusPositive := by
      norm_num [chi35Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi35LogChi_valid }

noncomputable def chi35InputQChi : RationalEnclosure :=
  { lower := (-4862141/16777216), upper := (-4238147/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi35InputQChi_eq :
    chi35InputQChi = outerEnclosure 24 chi35QChiValue := by
  rfl'

theorem chi35RoundedFacts :
    ChiRoundedFacts 8 chi35Slice chi35LogChiCertificate
      chi35InputQChi :=
  { coversQChi := by
      rw [chi35InputQChi_eq, chi35QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi36Slice : ChiSlice :=
  { lo := (3/32), hi := (7/64) }

noncomputable def chi36LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (3/2) }, upper := { exponent := -4, mantissa := (7/4) } }

private noncomputable def chi36QChiValue : RationalEnclosure :=
  { lower := (-15563783192208241930811/65749767640686035156250), upper := (-14739284231340877198787995214111420242277/79419688127261319577703019697265625000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi36QChiValue_eq :
    chi36QChiValue =
      (chi36Slice.qChiAD 8 chi36LogChiCertificate).value := by
  norm_num [chi36QChiValue, chi36LogChiCertificate, chi36Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi36LogChi_valid :
    (if chi36Slice.lo = 0 then
      if chi36Slice.hi = 0 then true
      else decide (chi36Slice.hi ≤ 1 / 4) &&
        chi36LogChiCertificate.check
          (IntervalAD.const chi36Slice.hi).value
    else chi36LogChiCertificate.check
      chi36Slice.chiAD.value) = true := by
  norm_num [chi36Slice, chi36LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi36ValidityFacts :
    ChiFacts chi36Slice chi36LogChiCertificate :=
  { domain := by norm_num [chi36Slice]
    onePlusPositive := by
      norm_num [chi36Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi36LogChi_valid }

noncomputable def chi36InputQChi : RationalEnclosure :=
  { lower := (-3971375/16777216), upper := (-3113637/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi36InputQChi_eq :
    chi36InputQChi = outerEnclosure 24 chi36QChiValue := by
  rfl'

theorem chi36RoundedFacts :
    ChiRoundedFacts 8 chi36Slice chi36LogChiCertificate
      chi36InputQChi :=
  { coversQChi := by
      rw [chi36InputQChi_eq, chi36QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi37Slice : ChiSlice :=
  { lo := (7/64), hi := (1/8) }

noncomputable def chi37LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (7/4) }, upper := { exponent := -3, mantissa := (1) } }

private noncomputable def chi37QChiValue : RationalEnclosure :=
  { lower := (-41384699627341123094852776/165970940086358349484832433), upper := (-22409798209043448858686185937/111532471738032810853807394976) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi37QChiValue_eq :
    chi37QChiValue =
      (chi37Slice.qChiAD 8 chi37LogChiCertificate).value := by
  norm_num [chi37QChiValue, chi37LogChiCertificate, chi37Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi37LogChi_valid :
    (if chi37Slice.lo = 0 then
      if chi37Slice.hi = 0 then true
      else decide (chi37Slice.hi ≤ 1 / 4) &&
        chi37LogChiCertificate.check
          (IntervalAD.const chi37Slice.hi).value
    else chi37LogChiCertificate.check
      chi37Slice.chiAD.value) = true := by
  norm_num [chi37Slice, chi37LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi37ValidityFacts :
    ChiFacts chi37Slice chi37LogChiCertificate :=
  { domain := by norm_num [chi37Slice]
    onePlusPositive := by
      norm_num [chi37Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi37LogChi_valid }

noncomputable def chi37InputQChi : RationalEnclosure :=
  { lower := (-522923/2097152), upper := (-1685491/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi37InputQChi_eq :
    chi37InputQChi = outerEnclosure 24 chi37QChiValue := by
  rfl'

theorem chi37RoundedFacts :
    ChiRoundedFacts 8 chi37Slice chi37LogChiCertificate
      chi37InputQChi :=
  { coversQChi := by
      rw [chi37InputQChi_eq, chi37QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi38Slice : ChiSlice :=
  { lo := (1/32), hi := (5/128) }

noncomputable def chi38LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (1) }, upper := { exponent := -5, mantissa := (5/4) } }

private noncomputable def chi38QChiValue : RationalEnclosure :=
  { lower := (-2986755171395/22751397356688), upper := (-3726511916504029944779/38594552957532922686336) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi38QChiValue_eq :
    chi38QChiValue =
      (chi38Slice.qChiAD 8 chi38LogChiCertificate).value := by
  norm_num [chi38QChiValue, chi38LogChiCertificate, chi38Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi38LogChi_valid :
    (if chi38Slice.lo = 0 then
      if chi38Slice.hi = 0 then true
      else decide (chi38Slice.hi ≤ 1 / 4) &&
        chi38LogChiCertificate.check
          (IntervalAD.const chi38Slice.hi).value
    else chi38LogChiCertificate.check
      chi38Slice.chiAD.value) = true := by
  norm_num [chi38Slice, chi38LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi38ValidityFacts :
    ChiFacts chi38Slice chi38LogChiCertificate :=
  { domain := by norm_num [chi38Slice]
    onePlusPositive := by
      norm_num [chi38Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi38LogChi_valid }

noncomputable def chi38InputQChi : RationalEnclosure :=
  { lower := (-1101239/8388608), upper := (-809965/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi38InputQChi_eq :
    chi38InputQChi = outerEnclosure 24 chi38QChiValue := by
  rfl'

theorem chi38RoundedFacts :
    ChiRoundedFacts 8 chi38Slice chi38LogChiCertificate
      chi38InputQChi :=
  { coversQChi := by
      rw [chi38InputQChi_eq, chi38QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi39Slice : ChiSlice :=
  { lo := (5/128), hi := (3/64) }

noncomputable def chi39LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (5/4) }, upper := { exponent := -5, mantissa := (3/2) } }

private noncomputable def chi39QChiValue : RationalEnclosure :=
  { lower := (-5728188412204250039/39158434413081293310), upper := (-42367316363369580524090273100523/373643101801251761116333007812500) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi39QChiValue_eq :
    chi39QChiValue =
      (chi39Slice.qChiAD 8 chi39LogChiCertificate).value := by
  norm_num [chi39QChiValue, chi39LogChiCertificate, chi39Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi39LogChi_valid :
    (if chi39Slice.lo = 0 then
      if chi39Slice.hi = 0 then true
      else decide (chi39Slice.hi ≤ 1 / 4) &&
        chi39LogChiCertificate.check
          (IntervalAD.const chi39Slice.hi).value
    else chi39LogChiCertificate.check
      chi39Slice.chiAD.value) = true := by
  norm_num [chi39Slice, chi39LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi39ValidityFacts :
    ChiFacts chi39Slice chi39LogChiCertificate :=
  { domain := by norm_num [chi39Slice]
    onePlusPositive := by
      norm_num [chi39Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi39LogChi_valid }

noncomputable def chi39InputQChi : RationalEnclosure :=
  { lower := (-2454211/16777216), upper := (-1902365/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi39InputQChi_eq :
    chi39InputQChi = outerEnclosure 24 chi39QChiValue := by
  rfl'

theorem chi39RoundedFacts :
    ChiRoundedFacts 8 chi39Slice chi39LogChiCertificate
      chi39InputQChi :=
  { coversQChi := by
      rw [chi39InputQChi_eq, chi39QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi40Slice : ChiSlice :=
  { lo := (1/8), hi := (9/64) }

noncomputable def chi40LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -3, mantissa := (9/8) } }

private noncomputable def chi40QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2298120945120), upper := (-869973795411370797448155408455173/4067645835373309260941397005237760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi40QChiValue_eq :
    chi40QChiValue =
      (chi40Slice.qChiAD 8 chi40LogChiCertificate).value := by
  norm_num [chi40QChiValue, chi40LogChiCertificate, chi40Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi40LogChi_valid :
    (if chi40Slice.lo = 0 then
      if chi40Slice.hi = 0 then true
      else decide (chi40Slice.hi ≤ 1 / 4) &&
        chi40LogChiCertificate.check
          (IntervalAD.const chi40Slice.hi).value
    else chi40LogChiCertificate.check
      chi40Slice.chiAD.value) = true := by
  norm_num [chi40Slice, chi40LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi40ValidityFacts :
    ChiFacts chi40Slice chi40LogChiCertificate :=
  { domain := by norm_num [chi40Slice]
    onePlusPositive := by
      norm_num [chi40Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi40LogChi_valid }

noncomputable def chi40InputQChi : RationalEnclosure :=
  { lower := (-2180453/8388608), upper := (-3588251/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi40InputQChi_eq :
    chi40InputQChi = outerEnclosure 24 chi40QChiValue := by
  rfl'

theorem chi40RoundedFacts :
    ChiRoundedFacts 8 chi40Slice chi40LogChiCertificate
      chi40InputQChi :=
  { coversQChi := by
      rw [chi40InputQChi_eq, chi40QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi41Slice : ChiSlice :=
  { lo := (9/64), hi := (5/32) }

noncomputable def chi41LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (9/8) }, upper := { exponent := -3, mantissa := (5/4) } }

private noncomputable def chi41QChiValue : RationalEnclosure :=
  { lower := (-22096183666184095092217573247/82227429605862653914578278502), upper := (-22922791379435300358032577555741955834261/101978847118460871504581169864471937443648) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi41QChiValue_eq :
    chi41QChiValue =
      (chi41Slice.qChiAD 8 chi41LogChiCertificate).value := by
  norm_num [chi41QChiValue, chi41LogChiCertificate, chi41Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi41LogChi_valid :
    (if chi41Slice.lo = 0 then
      if chi41Slice.hi = 0 then true
      else decide (chi41Slice.hi ≤ 1 / 4) &&
        chi41LogChiCertificate.check
          (IntervalAD.const chi41Slice.hi).value
    else chi41LogChiCertificate.check
      chi41Slice.chiAD.value) = true := by
  norm_num [chi41Slice, chi41LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi41ValidityFacts :
    ChiFacts chi41Slice chi41LogChiCertificate :=
  { domain := by norm_num [chi41Slice]
    onePlusPositive := by
      norm_num [chi41Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi41LogChi_valid }

noncomputable def chi41InputQChi : RationalEnclosure :=
  { lower := (-1127095/4194304), upper := (-942795/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi41InputQChi_eq :
    chi41InputQChi = outerEnclosure 24 chi41QChiValue := by
  rfl'

theorem chi41RoundedFacts :
    ChiRoundedFacts 8 chi41Slice chi41LogChiCertificate
      chi41InputQChi :=
  { coversQChi := by
      rw [chi41InputQChi_eq, chi41QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi42Slice : ChiSlice :=
  { lo := (5/32), hi := (11/64) }

noncomputable def chi42LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (5/4) }, upper := { exponent := -3, mantissa := (11/8) } }

private noncomputable def chi42QChiValue : RationalEnclosure :=
  { lower := (-22954650010983384167/83188253011521981960), upper := (-39386313921311961972241731455716846472903/168385524848170660132248993874628891472000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi42QChiValue_eq :
    chi42QChiValue =
      (chi42Slice.qChiAD 8 chi42LogChiCertificate).value := by
  norm_num [chi42QChiValue, chi42LogChiCertificate, chi42Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi42LogChi_valid :
    (if chi42Slice.lo = 0 then
      if chi42Slice.hi = 0 then true
      else decide (chi42Slice.hi ≤ 1 / 4) &&
        chi42LogChiCertificate.check
          (IntervalAD.const chi42Slice.hi).value
    else chi42LogChiCertificate.check
      chi42Slice.chiAD.value) = true := by
  norm_num [chi42Slice, chi42LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi42ValidityFacts :
    ChiFacts chi42Slice chi42LogChiCertificate :=
  { domain := by norm_num [chi42Slice]
    onePlusPositive := by
      norm_num [chi42Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi42LogChi_valid }

noncomputable def chi42InputQChi : RationalEnclosure :=
  { lower := (-2314721/8388608), upper := (-981071/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi42InputQChi_eq :
    chi42InputQChi = outerEnclosure 24 chi42QChiValue := by
  rfl'

theorem chi42RoundedFacts :
    ChiRoundedFacts 8 chi42Slice chi42LogChiCertificate
      chi42InputQChi :=
  { coversQChi := by
      rw [chi42InputQChi_eq, chi42QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi43Slice : ChiSlice :=
  { lo := (11/64), hi := (3/16) }

noncomputable def chi43LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (11/8) }, upper := { exponent := -3, mantissa := (3/2) } }

private noncomputable def chi43QChiValue : RationalEnclosure :=
  { lower := (-7679682584249680027251526086109/27256301560845820267318162774125), upper := (-366359513154575051071200737276640100361879353/1517196473601769292223764920044067382812500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi43QChiValue_eq :
    chi43QChiValue =
      (chi43Slice.qChiAD 8 chi43LogChiCertificate).value := by
  norm_num [chi43QChiValue, chi43LogChiCertificate, chi43Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi43LogChi_valid :
    (if chi43Slice.lo = 0 then
      if chi43Slice.hi = 0 then true
      else decide (chi43Slice.hi ≤ 1 / 4) &&
        chi43LogChiCertificate.check
          (IntervalAD.const chi43Slice.hi).value
    else chi43LogChiCertificate.check
      chi43Slice.chiAD.value) = true := by
  norm_num [chi43Slice, chi43LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi43ValidityFacts :
    ChiFacts chi43Slice chi43LogChiCertificate :=
  { domain := by norm_num [chi43Slice]
    onePlusPositive := by
      norm_num [chi43Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi43LogChi_valid }

noncomputable def chi43InputQChi : RationalEnclosure :=
  { lower := (-1181779/4194304), upper := (-4051217/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi43InputQChi_eq :
    chi43InputQChi = outerEnclosure 24 chi43QChiValue := by
  rfl'

theorem chi43RoundedFacts :
    ChiRoundedFacts 8 chi43Slice chi43LogChiCertificate
      chi43InputQChi :=
  { coversQChi := by
      rw [chi43InputQChi_eq, chi43QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi44Slice : ChiSlice :=
  { lo := (7/32), hi := (15/64) }

noncomputable def chi44LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (7/4) }, upper := { exponent := -3, mantissa := (15/8) } }

private noncomputable def chi44QChiValue : RationalEnclosure :=
  { lower := (-165796095873414171389668447/567262180201262340023277048), upper := (-9551749971934478343151578843881146235591526685201/37243370537306787180700938273853286455752125681280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi44QChiValue_eq :
    chi44QChiValue =
      (chi44Slice.qChiAD 8 chi44LogChiCertificate).value := by
  norm_num [chi44QChiValue, chi44LogChiCertificate, chi44Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi44LogChi_valid :
    (if chi44Slice.lo = 0 then
      if chi44Slice.hi = 0 then true
      else decide (chi44Slice.hi ≤ 1 / 4) &&
        chi44LogChiCertificate.check
          (IntervalAD.const chi44Slice.hi).value
    else chi44LogChiCertificate.check
      chi44Slice.chiAD.value) = true := by
  norm_num [chi44Slice, chi44LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi44ValidityFacts :
    ChiFacts chi44Slice chi44LogChiCertificate :=
  { domain := by norm_num [chi44Slice]
    onePlusPositive := by
      norm_num [chi44Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi44LogChi_valid }

noncomputable def chi44InputQChi : RationalEnclosure :=
  { lower := (-1225887/4194304), upper := (-2151413/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi44InputQChi_eq :
    chi44InputQChi = outerEnclosure 24 chi44QChiValue := by
  rfl'

theorem chi44RoundedFacts :
    ChiRoundedFacts 8 chi44Slice chi44LogChiCertificate
      chi44InputQChi :=
  { coversQChi := by
      rw [chi44InputQChi_eq, chi44QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi45Slice : ChiSlice :=
  { lo := (15/64), hi := (1/4) }

noncomputable def chi45LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (15/8) }, upper := { exponent := -2, mantissa := (1) } }

private noncomputable def chi45QChiValue : RationalEnclosure :=
  { lower := (-444506207635727633756504176610756/1512751297715310111416413067466855), upper := (-502151918901882573079004286225329329/1936321661075596942613008726357574400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi45QChiValue_eq :
    chi45QChiValue =
      (chi45Slice.qChiAD 8 chi45LogChiCertificate).value := by
  norm_num [chi45QChiValue, chi45LogChiCertificate, chi45Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi45LogChi_valid :
    (if chi45Slice.lo = 0 then
      if chi45Slice.hi = 0 then true
      else decide (chi45Slice.hi ≤ 1 / 4) &&
        chi45LogChiCertificate.check
          (IntervalAD.const chi45Slice.hi).value
    else chi45LogChiCertificate.check
      chi45Slice.chiAD.value) = true := by
  norm_num [chi45Slice, chi45LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi45ValidityFacts :
    ChiFacts chi45Slice chi45LogChiCertificate :=
  { domain := by norm_num [chi45Slice]
    onePlusPositive := by
      norm_num [chi45Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi45LogChi_valid }

noncomputable def chi45InputQChi : RationalEnclosure :=
  { lower := (-4929811/16777216), upper := (-1087721/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi45InputQChi_eq :
    chi45InputQChi = outerEnclosure 24 chi45QChiValue := by
  rfl'

theorem chi45RoundedFacts :
    ChiRoundedFacts 8 chi45Slice chi45LogChiCertificate
      chi45InputQChi :=
  { coversQChi := by
      rw [chi45InputQChi_eq, chi45QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi46Slice : ChiSlice :=
  { lo := (1/4), hi := (9/32) }

noncomputable def chi46LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (9/8) } }

private noncomputable def chi46QChiValue : RationalEnclosure :=
  { lower := (-597351034279/1915100787600), upper := (-103799840738251338502447829510603/423068186834869811513438044684800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi46QChiValue_eq :
    chi46QChiValue =
      (chi46Slice.qChiAD 8 chi46LogChiCertificate).value := by
  norm_num [chi46QChiValue, chi46LogChiCertificate, chi46Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi46LogChi_valid :
    (if chi46Slice.lo = 0 then
      if chi46Slice.hi = 0 then true
      else decide (chi46Slice.hi ≤ 1 / 4) &&
        chi46LogChiCertificate.check
          (IntervalAD.const chi46Slice.hi).value
    else chi46LogChiCertificate.check
      chi46Slice.chiAD.value) = true := by
  norm_num [chi46Slice, chi46LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi46ValidityFacts :
    ChiFacts chi46Slice chi46LogChiCertificate :=
  { domain := by norm_num [chi46Slice]
    onePlusPositive := by
      norm_num [chi46Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi46LogChi_valid }

noncomputable def chi46InputQChi : RationalEnclosure :=
  { lower := (-5233087/16777216), upper := (-1029073/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi46InputQChi_eq :
    chi46InputQChi = outerEnclosure 24 chi46QChiValue := by
  rfl'

theorem chi46RoundedFacts :
    ChiRoundedFacts 8 chi46Slice chi46LogChiCertificate
      chi46InputQChi :=
  { coversQChi := by
      rw [chi46InputQChi_eq, chi46QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi47Slice : ChiSlice :=
  { lo := (9/32), hi := (5/16) }

noncomputable def chi47LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (9/8) }, upper := { exponent := -2, mantissa := (5/4) } }

private noncomputable def chi47QChiValue : RationalEnclosure :=
  { lower := (-1564596426265438534363164986423/5056986920760553215746564127873), upper := (-120604250492214636891223810615727437120273/487618219376128158267925142095392473929920) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi47QChiValue_eq :
    chi47QChiValue =
      (chi47Slice.qChiAD 8 chi47LogChiCertificate).value := by
  norm_num [chi47QChiValue, chi47LogChiCertificate, chi47Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi47LogChi_valid :
    (if chi47Slice.lo = 0 then
      if chi47Slice.hi = 0 then true
      else decide (chi47Slice.hi ≤ 1 / 4) &&
        chi47LogChiCertificate.check
          (IntervalAD.const chi47Slice.hi).value
    else chi47LogChiCertificate.check
      chi47Slice.chiAD.value) = true := by
  norm_num [chi47Slice, chi47LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi47ValidityFacts :
    ChiFacts chi47Slice chi47LogChiCertificate :=
  { domain := by norm_num [chi47Slice]
    onePlusPositive := by
      norm_num [chi47Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi47LogChi_valid }

noncomputable def chi47InputQChi : RationalEnclosure :=
  { lower := (-2595377/8388608), upper := (-4149565/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi47InputQChi_eq :
    chi47InputQChi = outerEnclosure 24 chi47QChiValue := by
  rfl'

theorem chi47RoundedFacts :
    ChiRoundedFacts 8 chi47Slice chi47LogChiCertificate
      chi47InputQChi :=
  { coversQChi := by
      rw [chi47InputQChi_eq, chi47QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi48Slice : ChiSlice :=
  { lo := (5/16), hi := (11/32) }

noncomputable def chi48LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (5/4) }, upper := { exponent := -2, mantissa := (11/8) } }

private noncomputable def chi48QChiValue : RationalEnclosure :=
  { lower := (-7191657786880100557/23607477205972454340), upper := (-1337847264409023978471229761861922202300297/5424562437784472974357716506454125769701760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi48QChiValue_eq :
    chi48QChiValue =
      (chi48Slice.qChiAD 8 chi48LogChiCertificate).value := by
  norm_num [chi48QChiValue, chi48LogChiCertificate, chi48Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi48LogChi_valid :
    (if chi48Slice.lo = 0 then
      if chi48Slice.hi = 0 then true
      else decide (chi48Slice.hi ≤ 1 / 4) &&
        chi48LogChiCertificate.check
          (IntervalAD.const chi48Slice.hi).value
    else chi48LogChiCertificate.check
      chi48Slice.chiAD.value) = true := by
  norm_num [chi48Slice, chi48LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi48ValidityFacts :
    ChiFacts chi48Slice chi48LogChiCertificate :=
  { domain := by norm_num [chi48Slice]
    onePlusPositive := by
      norm_num [chi48Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi48LogChi_valid }

noncomputable def chi48InputQChi : RationalEnclosure :=
  { lower := (-5110923/16777216), upper := (-4137725/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi48InputQChi_eq :
    chi48InputQChi = outerEnclosure 24 chi48QChiValue := by
  rfl'

theorem chi48RoundedFacts :
    ChiRoundedFacts 8 chi48Slice chi48LogChiCertificate
      chi48InputQChi :=
  { coversQChi := by
      rw [chi48InputQChi_eq, chi48QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi49Slice : ChiSlice :=
  { lo := (11/32), hi := (3/8) }

noncomputable def chi49LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (11/8) }, upper := { exponent := -2, mantissa := (3/2) } }

private noncomputable def chi49QChiValue : RationalEnclosure :=
  { lower := (-13970585819932445985970418366906/46880838684654810859787239971495), upper := (-81809230950711785950643869203875991094155749/335735172871876900688580494587529296875000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi49QChiValue_eq :
    chi49QChiValue =
      (chi49Slice.qChiAD 8 chi49LogChiCertificate).value := by
  norm_num [chi49QChiValue, chi49LogChiCertificate, chi49Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi49LogChi_valid :
    (if chi49Slice.lo = 0 then
      if chi49Slice.hi = 0 then true
      else decide (chi49Slice.hi ≤ 1 / 4) &&
        chi49LogChiCertificate.check
          (IntervalAD.const chi49Slice.hi).value
    else chi49LogChiCertificate.check
      chi49Slice.chiAD.value) = true := by
  norm_num [chi49Slice, chi49LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi49ValidityFacts :
    ChiFacts chi49Slice chi49LogChiCertificate :=
  { domain := by norm_num [chi49Slice]
    onePlusPositive := by
      norm_num [chi49Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi49LogChi_valid }

noncomputable def chi49InputQChi : RationalEnclosure :=
  { lower := (-4999645/16777216), upper := (-511017/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi49InputQChi_eq :
    chi49InputQChi = outerEnclosure 24 chi49QChiValue := by
  rfl'

theorem chi49RoundedFacts :
    ChiRoundedFacts 8 chi49Slice chi49LogChiCertificate
      chi49InputQChi :=
  { coversQChi := by
      rw [chi49InputQChi_eq, chi49QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi50Slice : ChiSlice :=
  { lo := (3/8), hi := (13/32) }

noncomputable def chi50LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -2, mantissa := (13/8) } }

private noncomputable def chi50QChiValue : RationalEnclosure :=
  { lower := (-1842551361108221187821/6358219288330078125000), upper := (-350527405307436644951583059292819299/1467747053843618556719648437500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi50QChiValue_eq :
    chi50QChiValue =
      (chi50Slice.qChiAD 8 chi50LogChiCertificate).value := by
  norm_num [chi50QChiValue, chi50LogChiCertificate, chi50Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi50LogChi_valid :
    (if chi50Slice.lo = 0 then
      if chi50Slice.hi = 0 then true
      else decide (chi50Slice.hi ≤ 1 / 4) &&
        chi50LogChiCertificate.check
          (IntervalAD.const chi50Slice.hi).value
    else chi50LogChiCertificate.check
      chi50Slice.chiAD.value) = true := by
  norm_num [chi50Slice, chi50LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi50ValidityFacts :
    ChiFacts chi50Slice chi50LogChiCertificate :=
  { domain := by norm_num [chi50Slice]
    onePlusPositive := by
      norm_num [chi50Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi50LogChi_valid }

noncomputable def chi50InputQChi : RationalEnclosure :=
  { lower := (-2430939/8388608), upper := (-4006735/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi50InputQChi_eq :
    chi50InputQChi = outerEnclosure 24 chi50QChiValue := by
  rfl'

theorem chi50RoundedFacts :
    ChiRoundedFacts 8 chi50Slice chi50LogChiCertificate
      chi50InputQChi :=
  { coversQChi := by
      rw [chi50InputQChi_eq, chi50QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi51Slice : ChiSlice :=
  { lo := (13/32), hi := (7/16) }

noncomputable def chi51LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (13/8) }, upper := { exponent := -2, mantissa := (7/4) } }

private noncomputable def chi51QChiValue : RationalEnclosure :=
  { lower := (-29250016153892124618719/104373123828879541811175), upper := (-13556850377323925116782499327971195099167/58343715667541777215024921758280314753600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi51QChiValue_eq :
    chi51QChiValue =
      (chi51Slice.qChiAD 8 chi51LogChiCertificate).value := by
  norm_num [chi51QChiValue, chi51LogChiCertificate, chi51Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi51LogChi_valid :
    (if chi51Slice.lo = 0 then
      if chi51Slice.hi = 0 then true
      else decide (chi51Slice.hi ≤ 1 / 4) &&
        chi51LogChiCertificate.check
          (IntervalAD.const chi51Slice.hi).value
    else chi51LogChiCertificate.check
      chi51Slice.chiAD.value) = true := by
  norm_num [chi51Slice, chi51LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi51ValidityFacts :
    ChiFacts chi51Slice chi51LogChiCertificate :=
  { domain := by norm_num [chi51Slice]
    onePlusPositive := by
      norm_num [chi51Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi51LogChi_valid }

noncomputable def chi51InputQChi : RationalEnclosure :=
  { lower := (-4701727/16777216), upper := (-3898383/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi51InputQChi_eq :
    chi51InputQChi = outerEnclosure 24 chi51QChiValue := by
  rfl'

theorem chi51RoundedFacts :
    ChiRoundedFacts 8 chi51Slice chi51LogChiCertificate
      chi51InputQChi :=
  { coversQChi := by
      rw [chi51InputQChi_eq, chi51QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi52Slice : ChiSlice :=
  { lo := (7/16), hi := (15/32) }

noncomputable def chi52LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (7/4) }, upper := { exponent := -2, mantissa := (15/8) } }

private noncomputable def chi52QChiValue : RationalEnclosure :=
  { lower := (-10405551221615975929926427/38600680901269330829986308), upper := (-75307903289139224309485899131881835420223033763019/335391802814433089317321648718027264385744853979520) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi52QChiValue_eq :
    chi52QChiValue =
      (chi52Slice.qChiAD 8 chi52LogChiCertificate).value := by
  norm_num [chi52QChiValue, chi52LogChiCertificate, chi52Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi52LogChi_valid :
    (if chi52Slice.lo = 0 then
      if chi52Slice.hi = 0 then true
      else decide (chi52Slice.hi ≤ 1 / 4) &&
        chi52LogChiCertificate.check
          (IntervalAD.const chi52Slice.hi).value
    else chi52LogChiCertificate.check
      chi52Slice.chiAD.value) = true := by
  norm_num [chi52Slice, chi52LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi52ValidityFacts :
    ChiFacts chi52Slice chi52LogChiCertificate :=
  { domain := by norm_num [chi52Slice]
    onePlusPositive := by
      norm_num [chi52Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi52LogChi_valid }

noncomputable def chi52InputQChi : RationalEnclosure :=
  { lower := (-1130655/4194304), upper := (-3767107/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi52InputQChi_eq :
    chi52InputQChi = outerEnclosure 24 chi52QChiValue := by
  rfl'

theorem chi52RoundedFacts :
    ChiRoundedFacts 8 chi52Slice chi52LogChiCertificate
      chi52InputQChi :=
  { coversQChi := by
      rw [chi52InputQChi_eq, chi52QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi53Slice : ChiSlice :=
  { lo := (15/32), hi := (1/2) }

noncomputable def chi53LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (15/8) }, upper := { exponent := -1, mantissa := (1) } }

private noncomputable def chi53QChiValue : RationalEnclosure :=
  { lower := (-696419288187667655515694269182856/2699973835162768679869800538137045), upper := (-74492176832815752242917107232109947/345596650900834391023334468881541760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi53QChiValue_eq :
    chi53QChiValue =
      (chi53Slice.qChiAD 8 chi53LogChiCertificate).value := by
  norm_num [chi53QChiValue, chi53LogChiCertificate, chi53Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi53LogChi_valid :
    (if chi53Slice.lo = 0 then
      if chi53Slice.hi = 0 then true
      else decide (chi53Slice.hi ≤ 1 / 4) &&
        chi53LogChiCertificate.check
          (IntervalAD.const chi53Slice.hi).value
    else chi53LogChiCertificate.check
      chi53Slice.chiAD.value) = true := by
  norm_num [chi53Slice, chi53LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi53ValidityFacts :
    ChiFacts chi53Slice chi53LogChiCertificate :=
  { domain := by norm_num [chi53Slice]
    onePlusPositive := by
      norm_num [chi53Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi53LogChi_valid }

noncomputable def chi53InputQChi : RationalEnclosure :=
  { lower := (-4327441/16777216), upper := (-3616271/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi53InputQChi_eq :
    chi53InputQChi = outerEnclosure 24 chi53QChiValue := by
  rfl'

theorem chi53RoundedFacts :
    ChiRoundedFacts 8 chi53Slice chi53LogChiCertificate
      chi53InputQChi :=
  { coversQChi := by
      rw [chi53InputQChi_eq, chi53QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi54Slice : ChiSlice :=
  { lo := (1/4), hi := (17/64) }

noncomputable def chi54LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (17/16) } }

private noncomputable def chi54QChiValue : RationalEnclosure :=
  { lower := (-10154967582743/34471814176800), upper := (-9134924403493396112195130105019/34959217773969823427672279500800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi54QChiValue_eq :
    chi54QChiValue =
      (chi54Slice.qChiAD 8 chi54LogChiCertificate).value := by
  norm_num [chi54QChiValue, chi54LogChiCertificate, chi54Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi54LogChi_valid :
    (if chi54Slice.lo = 0 then
      if chi54Slice.hi = 0 then true
      else decide (chi54Slice.hi ≤ 1 / 4) &&
        chi54LogChiCertificate.check
          (IntervalAD.const chi54Slice.hi).value
    else chi54LogChiCertificate.check
      chi54Slice.chiAD.value) = true := by
  norm_num [chi54Slice, chi54LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi54ValidityFacts :
    ChiFacts chi54Slice chi54LogChiCertificate :=
  { domain := by norm_num [chi54Slice]
    onePlusPositive := by
      norm_num [chi54Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi54LogChi_valid }

noncomputable def chi54InputQChi : RationalEnclosure :=
  { lower := (-617795/2097152), upper := (-4383925/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi54InputQChi_eq :
    chi54InputQChi = outerEnclosure 24 chi54QChiValue := by
  rfl'

theorem chi54RoundedFacts :
    ChiRoundedFacts 8 chi54Slice chi54LogChiCertificate
      chi54InputQChi :=
  { coversQChi := by
      rw [chi54InputQChi_eq, chi54QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi55Slice : ChiSlice :=
  { lo := (17/64), hi := (9/32) }

noncomputable def chi55LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (17/16) }, upper := { exponent := -2, mantissa := (9/8) } }

private noncomputable def chi55QChiValue : RationalEnclosure :=
  { lower := (-3443234089574418086485729/11688094372278757005974115), upper := (-3732675347080691747699751114873809561619305242469/14221859224585797526931455798408515702931738316160) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi55QChiValue_eq :
    chi55QChiValue =
      (chi55Slice.qChiAD 8 chi55LogChiCertificate).value := by
  norm_num [chi55QChiValue, chi55LogChiCertificate, chi55Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi55LogChi_valid :
    (if chi55Slice.lo = 0 then
      if chi55Slice.hi = 0 then true
      else decide (chi55Slice.hi ≤ 1 / 4) &&
        chi55LogChiCertificate.check
          (IntervalAD.const chi55Slice.hi).value
    else chi55LogChiCertificate.check
      chi55Slice.chiAD.value) = true := by
  norm_num [chi55Slice, chi55LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi55ValidityFacts :
    ChiFacts chi55Slice chi55LogChiCertificate :=
  { domain := by norm_num [chi55Slice]
    onePlusPositive := by
      norm_num [chi55Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi55LogChi_valid }

noncomputable def chi55InputQChi : RationalEnclosure :=
  { lower := (-617807/2097152), upper := (-4403355/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi55InputQChi_eq :
    chi55InputQChi = outerEnclosure 24 chi55QChiValue := by
  rfl'

theorem chi55RoundedFacts :
    ChiRoundedFacts 8 chi55Slice chi55LogChiCertificate
      chi55InputQChi :=
  { coversQChi := by
      rw [chi55InputQChi_eq, chi55QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi56Slice : ChiSlice :=
  { lo := (9/32), hi := (19/64) }

noncomputable def chi56LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (9/8) }, upper := { exponent := -2, mantissa := (19/16) } }

private noncomputable def chi56QChiValue : RationalEnclosure :=
  { lower := (-29727332099043332152900134742037/101139738415211064314931282557460), upper := (-1586891883283469872765531249843399929202957430123883229997/6036539881927795788505752398676472045281940992187500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi56QChiValue_eq :
    chi56QChiValue =
      (chi56Slice.qChiAD 8 chi56LogChiCertificate).value := by
  norm_num [chi56QChiValue, chi56LogChiCertificate, chi56Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi56LogChi_valid :
    (if chi56Slice.lo = 0 then
      if chi56Slice.hi = 0 then true
      else decide (chi56Slice.hi ≤ 1 / 4) &&
        chi56LogChiCertificate.check
          (IntervalAD.const chi56Slice.hi).value
    else chi56LogChiCertificate.check
      chi56Slice.chiAD.value) = true := by
  norm_num [chi56Slice, chi56LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi56ValidityFacts :
    ChiFacts chi56Slice chi56LogChiCertificate :=
  { domain := by norm_num [chi56Slice]
    onePlusPositive := by
      norm_num [chi56Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi56LogChi_valid }

noncomputable def chi56InputQChi : RationalEnclosure :=
  { lower := (-308201/1048576), upper := (-4410411/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi56InputQChi_eq :
    chi56InputQChi = outerEnclosure 24 chi56QChiValue := by
  rfl'

theorem chi56RoundedFacts :
    ChiRoundedFacts 8 chi56Slice chi56LogChiCertificate
      chi56InputQChi :=
  { coversQChi := by
      rw [chi56InputQChi_eq, chi56QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi57Slice : ChiSlice :=
  { lo := (19/64), hi := (5/16) }

noncomputable def chi57LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (19/16) }, upper := { exponent := -2, mantissa := (5/4) } }

private noncomputable def chi57QChiValue : RationalEnclosure :=
  { lower := (-21662287550585022278879565546478294/74024395684300553945669769287109375), upper := (-1249727133529588623266851608490131014428094071/4758517878935430438594745603510605468750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi57QChiValue_eq :
    chi57QChiValue =
      (chi57Slice.qChiAD 8 chi57LogChiCertificate).value := by
  norm_num [chi57QChiValue, chi57LogChiCertificate, chi57Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi57LogChi_valid :
    (if chi57Slice.lo = 0 then
      if chi57Slice.hi = 0 then true
      else decide (chi57Slice.hi ≤ 1 / 4) &&
        chi57LogChiCertificate.check
          (IntervalAD.const chi57Slice.hi).value
    else chi57LogChiCertificate.check
      chi57Slice.chiAD.value) = true := by
  norm_num [chi57Slice, chi57LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi57ValidityFacts :
    ChiFacts chi57Slice chi57LogChiCertificate :=
  { domain := by norm_num [chi57Slice]
    onePlusPositive := by
      norm_num [chi57Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi57LogChi_valid }

noncomputable def chi57InputQChi : RationalEnclosure :=
  { lower := (-4909637/16777216), upper := (-4406191/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi57InputQChi_eq :
    chi57InputQChi = outerEnclosure 24 chi57QChiValue := by
  rfl'

theorem chi57RoundedFacts :
    ChiRoundedFacts 8 chi57Slice chi57LogChiCertificate
      chi57InputQChi :=
  { coversQChi := by
      rw [chi57InputQChi_eq, chi57QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi58Slice : ChiSlice :=
  { lo := (5/16), hi := (21/64) }

noncomputable def chi58LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (5/4) }, upper := { exponent := -2, mantissa := (21/16) } }

private noncomputable def chi58QChiValue : RationalEnclosure :=
  { lower := (-7191657786880100557/24731642787209237880), upper := (-49321576312607374889780005234065017510952958189/188420007271251816058380412893629109787788664320) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi58QChiValue_eq :
    chi58QChiValue =
      (chi58Slice.qChiAD 8 chi58LogChiCertificate).value := by
  norm_num [chi58QChiValue, chi58LogChiCertificate, chi58Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi58LogChi_valid :
    (if chi58Slice.lo = 0 then
      if chi58Slice.hi = 0 then true
      else decide (chi58Slice.hi ≤ 1 / 4) &&
        chi58LogChiCertificate.check
          (IntervalAD.const chi58Slice.hi).value
    else chi58LogChiCertificate.check
      chi58Slice.chiAD.value) = true := by
  norm_num [chi58Slice, chi58LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi58ValidityFacts :
    ChiFacts chi58Slice chi58LogChiCertificate :=
  { domain := by norm_num [chi58Slice]
    onePlusPositive := by
      norm_num [chi58Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi58LogChi_valid }

noncomputable def chi58InputQChi : RationalEnclosure :=
  { lower := (-4878609/16777216), upper := (-4391671/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi58InputQChi_eq :
    chi58InputQChi = outerEnclosure 24 chi58QChiValue := by
  rfl'

theorem chi58RoundedFacts :
    ChiRoundedFacts 8 chi58Slice chi58LogChiCertificate
      chi58InputQChi :=
  { coversQChi := by
      rw [chi58InputQChi_eq, chi58QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi59Slice : ChiSlice :=
  { lo := (21/64), hi := (11/32) }

noncomputable def chi59LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (21/16) }, upper := { exponent := -2, mantissa := (11/8) } }

private noncomputable def chi59QChiValue : RationalEnclosure :=
  { lower := (-160112704402761404621382924688357147/555131995384379127378415042620194775), upper := (-162586578974857515466433193864466250026786206552774148943/624524279532189824966176562469302195028679114370732227200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi59QChiValue_eq :
    chi59QChiValue =
      (chi59Slice.qChiAD 8 chi59LogChiCertificate).value := by
  norm_num [chi59QChiValue, chi59LogChiCertificate, chi59Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi59LogChi_valid :
    (if chi59Slice.lo = 0 then
      if chi59Slice.hi = 0 then true
      else decide (chi59Slice.hi ≤ 1 / 4) &&
        chi59LogChiCertificate.check
          (IntervalAD.const chi59Slice.hi).value
    else chi59LogChiCertificate.check
      chi59Slice.chiAD.value) = true := by
  norm_num [chi59Slice, chi59LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi59ValidityFacts :
    ChiFacts chi59Slice chi59LogChiCertificate :=
  { domain := by norm_num [chi59Slice]
    onePlusPositive := by
      norm_num [chi59Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi59LogChi_valid }

noncomputable def chi59InputQChi : RationalEnclosure :=
  { lower := (-1209733/4194304), upper := (-1091931/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi59InputQChi_eq :
    chi59InputQChi = outerEnclosure 24 chi59QChiValue := by
  rfl'

theorem chi59RoundedFacts :
    ChiRoundedFacts 8 chi59Slice chi59LogChiCertificate
      chi59InputQChi :=
  { coversQChi := by
      rw [chi59InputQChi_eq, chi59QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi60Slice : ChiSlice :=
  { lo := (11/32), hi := (23/64) }

noncomputable def chi60LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (11/8) }, upper := { exponent := -2, mantissa := (23/16) } }

private noncomputable def chi60QChiValue : RationalEnclosure :=
  { lower := (-160661736929223128838659811219419/562570064215857730317446879657940), upper := (-24432748338486131238259333871397404977314318724497547/94556058077351392124621242122665961738598793184526080) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi60QChiValue_eq :
    chi60QChiValue =
      (chi60Slice.qChiAD 8 chi60LogChiCertificate).value := by
  norm_num [chi60QChiValue, chi60LogChiCertificate, chi60Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi60LogChi_valid :
    (if chi60Slice.lo = 0 then
      if chi60Slice.hi = 0 then true
      else decide (chi60Slice.hi ≤ 1 / 4) &&
        chi60LogChiCertificate.check
          (IntervalAD.const chi60Slice.hi).value
    else chi60LogChiCertificate.check
      chi60Slice.chiAD.value) = true := by
  norm_num [chi60Slice, chi60LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi60ValidityFacts :
    ChiFacts chi60Slice chi60LogChiCertificate :=
  { domain := by norm_num [chi60Slice]
    onePlusPositive := by
      norm_num [chi60Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi60LogChi_valid }

noncomputable def chi60InputQChi : RationalEnclosure :=
  { lower := (-4791327/16777216), upper := (-4335137/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi60InputQChi_eq :
    chi60InputQChi = outerEnclosure 24 chi60QChiValue := by
  rfl'

theorem chi60RoundedFacts :
    ChiRoundedFacts 8 chi60Slice chi60LogChiCertificate
      chi60InputQChi :=
  { coversQChi := by
      rw [chi60InputQChi_eq, chi60QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi61Slice : ChiSlice :=
  { lo := (23/64), hi := (3/8) }

noncomputable def chi61LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (23/16) }, upper := { exponent := -2, mantissa := (3/2) } }

private noncomputable def chi61QChiValue : RationalEnclosure :=
  { lower := (-6945152381313804258093165116/24600791914040266028903303505), upper := (-10823465986799496886924025795405703546893/42282611102256707237177552899218750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi61QChiValue_eq :
    chi61QChiValue =
      (chi61Slice.qChiAD 8 chi61LogChiCertificate).value := by
  norm_num [chi61QChiValue, chi61LogChiCertificate, chi61Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi61LogChi_valid :
    (if chi61Slice.lo = 0 then
      if chi61Slice.hi = 0 then true
      else decide (chi61Slice.hi ≤ 1 / 4) &&
        chi61LogChiCertificate.check
          (IntervalAD.const chi61Slice.hi).value
    else chi61LogChiCertificate.check
      chi61Slice.chiAD.value) = true := by
  norm_num [chi61Slice, chi61LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi61ValidityFacts :
    ChiFacts chi61Slice chi61LogChiCertificate :=
  { domain := by norm_num [chi61Slice]
    onePlusPositive := by
      norm_num [chi61Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi61LogChi_valid }

noncomputable def chi61InputQChi : RationalEnclosure :=
  { lower := (-2368223/8388608), upper := (-4294617/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi61InputQChi_eq :
    chi61InputQChi = outerEnclosure 24 chi61QChiValue := by
  rfl'

theorem chi61RoundedFacts :
    ChiRoundedFacts 8 chi61Slice chi61LogChiCertificate
      chi61InputQChi :=
  { coversQChi := by
      rw [chi61InputQChi_eq, chi61QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi62Slice : ChiSlice :=
  { lo := (3/8), hi := (25/64) }

noncomputable def chi62LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -2, mantissa := (25/16) } }

private noncomputable def chi62QChiValue : RationalEnclosure :=
  { lower := (-1842551361108221187821/6612548059863281250000), upper := (-370662882259281931466712298132192073792867669865553/1464322318026818740778561386315149693281250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi62QChiValue_eq :
    chi62QChiValue =
      (chi62Slice.qChiAD 8 chi62LogChiCertificate).value := by
  norm_num [chi62QChiValue, chi62LogChiCertificate, chi62Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi62LogChi_valid :
    (if chi62Slice.lo = 0 then
      if chi62Slice.hi = 0 then true
      else decide (chi62Slice.hi ≤ 1 / 4) &&
        chi62LogChiCertificate.check
          (IntervalAD.const chi62Slice.hi).value
    else chi62LogChiCertificate.check
      chi62Slice.chiAD.value) = true := by
  norm_num [chi62Slice, chi62LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi62ValidityFacts :
    ChiFacts chi62Slice chi62LogChiCertificate :=
  { domain := by norm_num [chi62Slice]
    onePlusPositive := by
      norm_num [chi62Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi62LogChi_valid }

noncomputable def chi62InputQChi : RationalEnclosure :=
  { lower := (-4674883/16777216), upper := (-1061701/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi62InputQChi_eq :
    chi62InputQChi = outerEnclosure 24 chi62QChiValue := by
  rfl'

theorem chi62RoundedFacts :
    ChiRoundedFacts 8 chi62Slice chi62LogChiCertificate
      chi62InputQChi :=
  { coversQChi := by
      rw [chi62InputQChi_eq, chi62QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi63Slice : ChiSlice :=
  { lo := (25/64), hi := (13/32) }

noncomputable def chi63LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (25/16) }, upper := { exponent := -2, mantissa := (13/8) } }

private noncomputable def chi63QChiValue : RationalEnclosure :=
  { lower := (-57262531134689225903399772954990541/208523966457728797161092021954604915), upper := (-55444485215769444573928926868057287963814958545531/221884903537240168134345453066404927770690107487872) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi63QChiValue_eq :
    chi63QChiValue =
      (chi63Slice.qChiAD 8 chi63LogChiCertificate).value := by
  norm_num [chi63QChiValue, chi63LogChiCertificate, chi63Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi63LogChi_valid :
    (if chi63Slice.lo = 0 then
      if chi63Slice.hi = 0 then true
      else decide (chi63Slice.hi ≤ 1 / 4) &&
        chi63LogChiCertificate.check
          (IntervalAD.const chi63Slice.hi).value
    else chi63LogChiCertificate.check
      chi63Slice.chiAD.value) = true := by
  norm_num [chi63Slice, chi63LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi63ValidityFacts :
    ChiFacts chi63Slice chi63LogChiCertificate :=
  { domain := by norm_num [chi63Slice]
    onePlusPositive := by
      norm_num [chi63Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi63LogChi_valid }

noncomputable def chi63InputQChi : RationalEnclosure :=
  { lower := (-4607173/16777216), upper := (-2096141/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi63InputQChi_eq :
    chi63InputQChi = outerEnclosure 24 chi63QChiValue := by
  rfl'

theorem chi63RoundedFacts :
    ChiRoundedFacts 8 chi63Slice chi63LogChiCertificate
      chi63InputQChi :=
  { coversQChi := by
      rw [chi63InputQChi_eq, chi63QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
