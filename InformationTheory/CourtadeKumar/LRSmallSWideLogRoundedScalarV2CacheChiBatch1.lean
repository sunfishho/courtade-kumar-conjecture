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

noncomputable def chi64Slice : ChiSlice :=
  { lo := (13/32), hi := (27/64) }

noncomputable def chi64LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (13/8) }, upper := { exponent := -2, mantissa := (27/16) } }

private noncomputable def chi64QChiValue : RationalEnclosure :=
  { lower := (-29250016153892124618719/108238795081801006322700), upper := (-10895339321004852096313485488562937415468231423428033/44243017300745218028452820354190903908437048191916800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi64QChiValue_eq :
    chi64QChiValue =
      (chi64Slice.qChiAD 8 chi64LogChiCertificate).value := by
  norm_num [chi64QChiValue, chi64LogChiCertificate, chi64Slice,
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
private theorem chi64LogChi_valid :
    (if chi64Slice.lo = 0 then
      if chi64Slice.hi = 0 then true
      else decide (chi64Slice.hi ≤ 1 / 4) &&
        chi64LogChiCertificate.check
          (IntervalAD.const chi64Slice.hi).value
    else chi64LogChiCertificate.check
      chi64Slice.chiAD.value) = true := by
  norm_num [chi64Slice, chi64LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi64ValidityFacts :
    ChiFacts chi64Slice chi64LogChiCertificate :=
  { domain := by norm_num [chi64Slice]
    onePlusPositive := by
      norm_num [chi64Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi64LogChi_valid }

noncomputable def chi64InputQChi : RationalEnclosure :=
  { lower := (-283363/1048576), upper := (-4131577/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi64InputQChi_eq :
    chi64InputQChi = outerEnclosure 24 chi64QChiValue := by
  rfl'

theorem chi64RoundedFacts :
    ChiRoundedFacts 8 chi64Slice chi64LogChiCertificate
      chi64InputQChi :=
  { coversQChi := by
      rw [chi64InputQChi_eq, chi64QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi65Slice : ChiSlice :=
  { lo := (27/64), hi := (7/16) }

noncomputable def chi65LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (27/16) }, upper := { exponent := -2, mantissa := (7/4) } }

private noncomputable def chi65QChiValue : RationalEnclosure :=
  { lower := (-2363007240186968136355792795897457258/8898449566207916798755379164384482555), upper := (-1533961160194419549550992469717284667026281754358265201/6330749014673773787217889198441672569717024140597312640) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi65QChiValue_eq :
    chi65QChiValue =
      (chi65Slice.qChiAD 8 chi65LogChiCertificate).value := by
  norm_num [chi65QChiValue, chi65LogChiCertificate, chi65Slice,
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
private theorem chi65LogChi_valid :
    (if chi65Slice.lo = 0 then
      if chi65Slice.hi = 0 then true
      else decide (chi65Slice.hi ≤ 1 / 4) &&
        chi65LogChiCertificate.check
          (IntervalAD.const chi65Slice.hi).value
    else chi65LogChiCertificate.check
      chi65Slice.chiAD.value) = true := by
  norm_num [chi65Slice, chi65LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi65ValidityFacts :
    ChiFacts chi65Slice chi65LogChiCertificate :=
  { domain := by norm_num [chi65Slice]
    onePlusPositive := by
      norm_num [chi65Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi65LogChi_valid }

noncomputable def chi65InputQChi : RationalEnclosure :=
  { lower := (-4455235/16777216), upper := (-2032587/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi65InputQChi_eq :
    chi65InputQChi = outerEnclosure 24 chi65QChiValue := by
  rfl'

theorem chi65RoundedFacts :
    ChiRoundedFacts 8 chi65Slice chi65LogChiCertificate
      chi65InputQChi :=
  { coversQChi := by
      rw [chi65InputQChi_eq, chi65QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi66Slice : ChiSlice :=
  { lo := (7/16), hi := (29/64) }

noncomputable def chi66LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (7/4) }, upper := { exponent := -2, mantissa := (29/16) } }

private noncomputable def chi66QChiValue : RationalEnclosure :=
  { lower := (-301760985426863301967866383/1158020427038079924899589240), upper := (-18056489977914255569211783693990498422810588578499/75857429086009264568443969350852135609375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi66QChiValue_eq :
    chi66QChiValue =
      (chi66Slice.qChiAD 8 chi66LogChiCertificate).value := by
  norm_num [chi66QChiValue, chi66LogChiCertificate, chi66Slice,
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
private theorem chi66LogChi_valid :
    (if chi66Slice.lo = 0 then
      if chi66Slice.hi = 0 then true
      else decide (chi66Slice.hi ≤ 1 / 4) &&
        chi66LogChiCertificate.check
          (IntervalAD.const chi66Slice.hi).value
    else chi66LogChiCertificate.check
      chi66Slice.chiAD.value) = true := by
  norm_num [chi66Slice, chi66LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi66ValidityFacts :
    ChiFacts chi66Slice chi66LogChiCertificate :=
  { domain := by norm_num [chi66Slice]
    onePlusPositive := by
      norm_num [chi66Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi66LogChi_valid }

noncomputable def chi66InputQChi : RationalEnclosure :=
  { lower := (-2185933/8388608), upper := (-3993513/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi66InputQChi_eq :
    chi66InputQChi = outerEnclosure 24 chi66QChiValue := by
  rfl'

theorem chi66RoundedFacts :
    ChiRoundedFacts 8 chi66Slice chi66LogChiCertificate
      chi66InputQChi :=
  { coversQChi := by
      rw [chi66InputQChi_eq, chi66QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi67Slice : ChiSlice :=
  { lo := (29/64), hi := (15/32) }

noncomputable def chi67LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (29/16) }, upper := { exponent := -2, mantissa := (15/8) } }

private noncomputable def chi67QChiValue : RationalEnclosure :=
  { lower := (-149362594598580186021605733097/584931126711644267486572265625), upper := (-3285903847538832181432286165800549910933224913529687221/14074123562797275318151180557874579344776542968750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi67QChiValue_eq :
    chi67QChiValue =
      (chi67Slice.qChiAD 8 chi67LogChiCertificate).value := by
  norm_num [chi67QChiValue, chi67LogChiCertificate, chi67Slice,
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
private theorem chi67LogChi_valid :
    (if chi67Slice.lo = 0 then
      if chi67Slice.hi = 0 then true
      else decide (chi67Slice.hi ≤ 1 / 4) &&
        chi67LogChiCertificate.check
          (IntervalAD.const chi67Slice.hi).value
    else chi67LogChiCertificate.check
      chi67Slice.chiAD.value) = true := by
  norm_num [chi67Slice, chi67LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi67ValidityFacts :
    ChiFacts chi67Slice chi67LogChiCertificate :=
  { domain := by norm_num [chi67Slice]
    onePlusPositive := by
      norm_num [chi67Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi67LogChi_valid }

noncomputable def chi67InputQChi : RationalEnclosure :=
  { lower := (-4284075/16777216), upper := (-1958499/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi67InputQChi_eq :
    chi67InputQChi = outerEnclosure 24 chi67QChiValue := by
  rfl'

theorem chi67RoundedFacts :
    ChiRoundedFacts 8 chi67Slice chi67LogChiCertificate
      chi67InputQChi :=
  { coversQChi := by
      rw [chi67InputQChi_eq, chi67QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi68Slice : ChiSlice :=
  { lo := (15/32), hi := (31/64) }

noncomputable def chi68LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (15/8) }, upper := { exponent := -2, mantissa := (31/16) } }

private noncomputable def chi68QChiValue : RationalEnclosure :=
  { lower := (-2698624741727212165123315293083567/10799895340651074719479202152548180), upper := (-59100059558061362664798721107445910123607419201410515382104749/258481272899004630983562197516793166864756878387560351647868160) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi68QChiValue_eq :
    chi68QChiValue =
      (chi68Slice.qChiAD 8 chi68LogChiCertificate).value := by
  norm_num [chi68QChiValue, chi68LogChiCertificate, chi68Slice,
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
private theorem chi68LogChi_valid :
    (if chi68Slice.lo = 0 then
      if chi68Slice.hi = 0 then true
      else decide (chi68Slice.hi ≤ 1 / 4) &&
        chi68LogChiCertificate.check
          (IntervalAD.const chi68Slice.hi).value
    else chi68LogChiCertificate.check
      chi68Slice.chiAD.value) = true := by
  norm_num [chi68Slice, chi68LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi68ValidityFacts :
    ChiFacts chi68Slice chi68LogChiCertificate :=
  { domain := by norm_num [chi68Slice]
    onePlusPositive := by
      norm_num [chi68Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi68LogChi_valid }

noncomputable def chi68InputQChi : RationalEnclosure :=
  { lower := (-4192209/16777216), upper := (-3836001/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi68InputQChi_eq :
    chi68InputQChi = outerEnclosure 24 chi68QChiValue := by
  rfl'

theorem chi68RoundedFacts :
    ChiRoundedFacts 8 chi68Slice chi68LogChiCertificate
      chi68InputQChi :=
  { coversQChi := by
      rw [chi68InputQChi_eq, chi68QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi69Slice : ChiSlice :=
  { lo := (31/64), hi := (1/2) }

noncomputable def chi69LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (31/16) }, upper := { exponent := -1, mantissa := (1) } }

private noncomputable def chi69QChiValue : RationalEnclosure :=
  { lower := (-8612705857242178063912801389213841136/35272609603974298774416679203100081275), upper := (-2018779308716333308783416319526839272613/9029788058617420486250669875993620806400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi69QChiValue_eq :
    chi69QChiValue =
      (chi69Slice.qChiAD 8 chi69LogChiCertificate).value := by
  norm_num [chi69QChiValue, chi69LogChiCertificate, chi69Slice,
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
private theorem chi69LogChi_valid :
    (if chi69Slice.lo = 0 then
      if chi69Slice.hi = 0 then true
      else decide (chi69Slice.hi ≤ 1 / 4) &&
        chi69LogChiCertificate.check
          (IntervalAD.const chi69Slice.hi).value
    else chi69LogChiCertificate.check
      chi69Slice.chiAD.value) = true := by
  norm_num [chi69Slice, chi69LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi69ValidityFacts :
    ChiFacts chi69Slice chi69LogChiCertificate :=
  { domain := by norm_num [chi69Slice]
    onePlusPositive := by
      norm_num [chi69Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi69LogChi_valid }

noncomputable def chi69InputQChi : RationalEnclosure :=
  { lower := (-4096585/16777216), upper := (-1875431/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi69InputQChi_eq :
    chi69InputQChi = outerEnclosure 24 chi69QChiValue := by
  rfl'

theorem chi69RoundedFacts :
    ChiRoundedFacts 8 chi69Slice chi69LogChiCertificate
      chi69InputQChi :=
  { coversQChi := by
      rw [chi69InputQChi_eq, chi69QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi70Slice : ChiSlice :=
  { lo := (1/2), hi := (17/32) }

noncomputable def chi70LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (17/16) } }

private noncomputable def chi70QChiValue : RationalEnclosure :=
  { lower := (-10154967582743/41366177012160), upper := (-159693206754473744059422473849/776871506088218298392717322240) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi70QChiValue_eq :
    chi70QChiValue =
      (chi70Slice.qChiAD 8 chi70LogChiCertificate).value := by
  norm_num [chi70QChiValue, chi70LogChiCertificate, chi70Slice,
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
private theorem chi70LogChi_valid :
    (if chi70Slice.lo = 0 then
      if chi70Slice.hi = 0 then true
      else decide (chi70Slice.hi ≤ 1 / 4) &&
        chi70LogChiCertificate.check
          (IntervalAD.const chi70Slice.hi).value
    else chi70LogChiCertificate.check
      chi70Slice.chiAD.value) = true := by
  norm_num [chi70Slice, chi70LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi70ValidityFacts :
    ChiFacts chi70Slice chi70LogChiCertificate :=
  { domain := by norm_num [chi70Slice]
    onePlusPositive := by
      norm_num [chi70Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi70LogChi_valid }

noncomputable def chi70InputQChi : RationalEnclosure :=
  { lower := (-4118633/16777216), upper := (-3448713/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi70InputQChi_eq :
    chi70InputQChi = outerEnclosure 24 chi70QChiValue := by
  rfl'

theorem chi70RoundedFacts :
    ChiRoundedFacts 8 chi70Slice chi70LogChiCertificate
      chi70InputQChi :=
  { coversQChi := by
      rw [chi70InputQChi_eq, chi70QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi71Slice : ChiSlice :=
  { lo := (17/32), hi := (9/16) }

noncomputable def chi71LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (17/16) }, upper := { exponent := -1, mantissa := (9/8) } }

private noncomputable def chi71QChiValue : RationalEnclosure :=
  { lower := (-41400707885629907781256723/178178505319627273468849842), upper := (-158897640306471962887718501151276958686792409507/816035617456744714064955224138331975995447529600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi71QChiValue_eq :
    chi71QChiValue =
      (chi71Slice.qChiAD 8 chi71LogChiCertificate).value := by
  norm_num [chi71QChiValue, chi71LogChiCertificate, chi71Slice,
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
private theorem chi71LogChi_valid :
    (if chi71Slice.lo = 0 then
      if chi71Slice.hi = 0 then true
      else decide (chi71Slice.hi ≤ 1 / 4) &&
        chi71LogChiCertificate.check
          (IntervalAD.const chi71Slice.hi).value
    else chi71LogChiCertificate.check
      chi71Slice.chiAD.value) = true := by
  norm_num [chi71Slice, chi71LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi71ValidityFacts :
    ChiFacts chi71Slice chi71LogChiCertificate :=
  { domain := by norm_num [chi71Slice]
    onePlusPositive := by
      norm_num [chi71Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi71LogChi_valid }

noncomputable def chi71InputQChi : RationalEnclosure :=
  { lower := (-1949137/8388608), upper := (-1633421/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi71InputQChi_eq :
    chi71InputQChi = outerEnclosure 24 chi71QChiValue := by
  rfl'

theorem chi71RoundedFacts :
    ChiRoundedFacts 8 chi71Slice chi71LogChiCertificate
      chi71InputQChi :=
  { coversQChi := by
      rw [chi71InputQChi_eq, chi71QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi72Slice : ChiSlice :=
  { lo := (9/16), hi := (19/32) }

noncomputable def chi72LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (9/8) }, upper := { exponent := -1, mantissa := (19/16) } }

private noncomputable def chi72QChiValue : RationalEnclosure :=
  { lower := (-3852444023025901276126173812483/17620163486970568695981059679000), upper := (-2071136945925189267875764907592320691486149141944321116809/11308534160237936571179597867047460854737694335937500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi72QChiValue_eq :
    chi72QChiValue =
      (chi72Slice.qChiAD 8 chi72LogChiCertificate).value := by
  norm_num [chi72QChiValue, chi72LogChiCertificate, chi72Slice,
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
private theorem chi72LogChi_valid :
    (if chi72Slice.lo = 0 then
      if chi72Slice.hi = 0 then true
      else decide (chi72Slice.hi ≤ 1 / 4) &&
        chi72LogChiCertificate.check
          (IntervalAD.const chi72Slice.hi).value
    else chi72LogChiCertificate.check
      chi72Slice.chiAD.value) = true := by
  norm_num [chi72Slice, chi72LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi72ValidityFacts :
    ChiFacts chi72Slice chi72LogChiCertificate :=
  { domain := by norm_num [chi72Slice]
    onePlusPositive := by
      norm_num [chi72Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi72LogChi_valid }

noncomputable def chi72InputQChi : RationalEnclosure :=
  { lower := (-229259/1048576), upper := (-3072715/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi72InputQChi_eq :
    chi72InputQChi = outerEnclosure 24 chi72QChiValue := by
  rfl'

theorem chi72RoundedFacts :
    ChiRoundedFacts 8 chi72Slice chi72LogChiCertificate
      chi72InputQChi :=
  { coversQChi := by
      rw [chi72InputQChi_eq, chi72QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi73Slice : ChiSlice :=
  { lo := (19/32), hi := (5/8) }

noncomputable def chi73LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (19/16) }, upper := { exponent := -1, mantissa := (5/4) } }

private noncomputable def chi73QChiValue : RationalEnclosure :=
  { lower := (-715267673009639556517274366706263/3498836125949331094744354248046875), upper := (-23802290502872054517385868237672815868518133/139233741724444608358193933321308593750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi73QChiValue_eq :
    chi73QChiValue =
      (chi73Slice.qChiAD 8 chi73LogChiCertificate).value := by
  norm_num [chi73QChiValue, chi73LogChiCertificate, chi73Slice,
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
private theorem chi73LogChi_valid :
    (if chi73Slice.lo = 0 then
      if chi73Slice.hi = 0 then true
      else decide (chi73Slice.hi ≤ 1 / 4) &&
        chi73LogChiCertificate.check
          (IntervalAD.const chi73Slice.hi).value
    else chi73LogChiCertificate.check
      chi73Slice.chiAD.value) = true := by
  norm_num [chi73Slice, chi73LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi73ValidityFacts :
    ChiFacts chi73Slice chi73LogChiCertificate :=
  { domain := by norm_num [chi73Slice]
    onePlusPositive := by
      norm_num [chi73Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi73LogChi_valid }

noncomputable def chi73InputQChi : RationalEnclosure :=
  { lower := (-1714885/8388608), upper := (-2868099/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi73InputQChi_eq :
    chi73InputQChi = outerEnclosure 24 chi73QChiValue := by
  rfl'

theorem chi73RoundedFacts :
    ChiRoundedFacts 8 chi73Slice chi73LogChiCertificate
      chi73InputQChi :=
  { coversQChi := by
      rw [chi73InputQChi_eq, chi73QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi74Slice : ChiSlice :=
  { lo := (5/8), hi := (21/32) }

noncomputable def chi74LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (5/4) }, upper := { exponent := -1, mantissa := (21/16) } }

private noncomputable def chi74QChiValue : RationalEnclosure :=
  { lower := (-5811981136537018061/30620129165116199280), upper := (-2739833224762550307826538458310476431672574997/17316444579150660432736308454543211503773027840) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi74QChiValue_eq :
    chi74QChiValue =
      (chi74Slice.qChiAD 8 chi74LogChiCertificate).value := by
  norm_num [chi74QChiValue, chi74LogChiCertificate, chi74Slice,
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
private theorem chi74LogChi_valid :
    (if chi74Slice.lo = 0 then
      if chi74Slice.hi = 0 then true
      else decide (chi74Slice.hi ≤ 1 / 4) &&
        chi74LogChiCertificate.check
          (IntervalAD.const chi74Slice.hi).value
    else chi74LogChiCertificate.check
      chi74Slice.chiAD.value) = true := by
  norm_num [chi74Slice, chi74LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi74ValidityFacts :
    ChiFacts chi74Slice chi74LogChiCertificate :=
  { domain := by norm_num [chi74Slice]
    onePlusPositive := by
      norm_num [chi74Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi74LogChi_valid }

noncomputable def chi74InputQChi : RationalEnclosure :=
  { lower := (-1592235/8388608), upper := (-2654515/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi74InputQChi_eq :
    chi74InputQChi = outerEnclosure 24 chi74QChiValue := by
  rfl'

theorem chi74RoundedFacts :
    ChiRoundedFacts 8 chi74Slice chi74LogChiCertificate
      chi74InputQChi :=
  { coversQChi := by
      rw [chi74InputQChi_eq, chi74QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi75Slice : ChiSlice :=
  { lo := (21/32), hi := (11/16) }

noncomputable def chi75LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (21/16) }, upper := { exponent := -1, mantissa := (11/8) } }

private noncomputable def chi75QChiValue : RationalEnclosure :=
  { lower := (-121040935768033364617870555647262747/692282253067578676495435229620478190), upper := (-28973210576116932921598227354258837241165406045108157582043/199766948661184813541239700670327733889820664007362806180480) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi75QChiValue_eq :
    chi75QChiValue =
      (chi75Slice.qChiAD 8 chi75LogChiCertificate).value := by
  norm_num [chi75QChiValue, chi75LogChiCertificate, chi75Slice,
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
private theorem chi75LogChi_valid :
    (if chi75Slice.lo = 0 then
      if chi75Slice.hi = 0 then true
      else decide (chi75Slice.hi ≤ 1 / 4) &&
        chi75LogChiCertificate.check
          (IntervalAD.const chi75Slice.hi).value
    else chi75LogChiCertificate.check
      chi75Slice.chiAD.value) = true := by
  norm_num [chi75Slice, chi75LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi75ValidityFacts :
    ChiFacts chi75Slice chi75LogChiCertificate :=
  { domain := by norm_num [chi75Slice]
    onePlusPositive := by
      norm_num [chi75Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi75LogChi_valid }

noncomputable def chi75InputQChi : RationalEnclosure :=
  { lower := (-2933385/16777216), upper := (-608321/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi75InputQChi_eq :
    chi75InputQChi = outerEnclosure 24 chi75QChiValue := by
  rfl'

theorem chi75RoundedFacts :
    ChiRoundedFacts 8 chi75Slice chi75LogChiCertificate
      chi75InputQChi :=
  { coversQChi := by
      rw [chi75InputQChi_eq, chi75QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi76Slice : ChiSlice :=
  { lo := (3/4), hi := (13/16) }

noncomputable def chi76LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (13/8) } }

private noncomputable def chi76QChiValue : RationalEnclosure :=
  { lower := (-7566012198856161082619/56645953659667968750000), upper := (-213269041144354477248699884231841413/2546603862651748436017851562500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi76QChiValue_eq :
    chi76QChiValue =
      (chi76Slice.qChiAD 8 chi76LogChiCertificate).value := by
  norm_num [chi76QChiValue, chi76LogChiCertificate, chi76Slice,
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
private theorem chi76LogChi_valid :
    (if chi76Slice.lo = 0 then
      if chi76Slice.hi = 0 then true
      else decide (chi76Slice.hi ≤ 1 / 4) &&
        chi76LogChiCertificate.check
          (IntervalAD.const chi76Slice.hi).value
    else chi76LogChiCertificate.check
      chi76Slice.chiAD.value) = true := by
  norm_num [chi76Slice, chi76LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi76ValidityFacts :
    ChiFacts chi76Slice chi76LogChiCertificate :=
  { domain := by norm_num [chi76Slice]
    onePlusPositive := by
      norm_num [chi76Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi76LogChi_valid }

noncomputable def chi76InputQChi : RationalEnclosure :=
  { lower := (-1120439/8388608), upper := (-175629/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi76InputQChi_eq :
    chi76InputQChi = outerEnclosure 24 chi76QChiValue := by
  rfl'

theorem chi76RoundedFacts :
    ChiRoundedFacts 8 chi76Slice chi76LogChiCertificate
      chi76InputQChi :=
  { coversQChi := by
      rw [chi76InputQChi_eq, chi76QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi77Slice : ChiSlice :=
  { lo := (13/16), hi := (7/8) }

noncomputable def chi77LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (13/8) }, upper := { exponent := -1, mantissa := (7/4) } }

private noncomputable def chi77QChiValue : RationalEnclosure :=
  { lower := (-121363036731826529946071/1210728236415002685009630), upper := (-28803111999184477487018122157079277436881/514946707848303511941306918127430604129600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi77QChiValue_eq :
    chi77QChiValue =
      (chi77Slice.qChiAD 8 chi77LogChiCertificate).value := by
  norm_num [chi77QChiValue, chi77LogChiCertificate, chi77Slice,
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
private theorem chi77LogChi_valid :
    (if chi77Slice.lo = 0 then
      if chi77Slice.hi = 0 then true
      else decide (chi77Slice.hi ≤ 1 / 4) &&
        chi77LogChiCertificate.check
          (IntervalAD.const chi77Slice.hi).value
    else chi77LogChiCertificate.check
      chi77Slice.chiAD.value) = true := by
  norm_num [chi77Slice, chi77LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi77ValidityFacts :
    ChiFacts chi77Slice chi77LogChiCertificate :=
  { domain := by norm_num [chi77Slice]
    onePlusPositive := by
      norm_num [chi77Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi77LogChi_valid }

noncomputable def chi77InputQChi : RationalEnclosure :=
  { lower := (-105109/1048576), upper := (-938419/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi77InputQChi_eq :
    chi77InputQChi = outerEnclosure 24 chi77QChiValue := by
  rfl'

theorem chi77RoundedFacts :
    ChiRoundedFacts 8 chi77Slice chi77LogChiCertificate
      chi77InputQChi :=
  { coversQChi := by
      rw [chi77InputQChi_eq, chi77QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi78Slice : ChiSlice :=
  { lo := (7/8), hi := (15/16) }

noncomputable def chi78LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (7/4) }, upper := { exponent := -1, mantissa := (15/8) } }

private noncomputable def chi78QChiValue : RationalEnclosure :=
  { lower := (-43700375903788234187168863/654533284847610392334550440), upper := (-35608444558202258758720251541976466632884734038351/1298440975743203033111000092400503331595136183075200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi78QChiValue_eq :
    chi78QChiValue =
      (chi78Slice.qChiAD 8 chi78LogChiCertificate).value := by
  norm_num [chi78QChiValue, chi78LogChiCertificate, chi78Slice,
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
private theorem chi78LogChi_valid :
    (if chi78Slice.lo = 0 then
      if chi78Slice.hi = 0 then true
      else decide (chi78Slice.hi ≤ 1 / 4) &&
        chi78LogChiCertificate.check
          (IntervalAD.const chi78Slice.hi).value
    else chi78LogChiCertificate.check
      chi78Slice.chiAD.value) = true := by
  norm_num [chi78Slice, chi78LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi78ValidityFacts :
    ChiFacts chi78Slice chi78LogChiCertificate :=
  { domain := by norm_num [chi78Slice]
    onePlusPositive := by
      norm_num [chi78Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi78LogChi_valid }

noncomputable def chi78InputQChi : RationalEnclosure :=
  { lower := (-1120143/16777216), upper := (-230049/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi78InputQChi_eq :
    chi78InputQChi = outerEnclosure 24 chi78QChiValue := by
  rfl'

theorem chi78RoundedFacts :
    ChiRoundedFacts 8 chi78Slice chi78LogChiCertificate
      chi78InputQChi :=
  { coversQChi := by
      rw [chi78InputQChi_eq, chi78QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi79Slice : ChiSlice :=
  { lo := (15/16), hi := (1) }

noncomputable def chi79LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (15/8) }, upper := { exponent := 0, mantissa := (1) } }

private noncomputable def chi79QChiValue : RationalEnclosure :=
  { lower := (-59319953468152409761876008533444/1780833806171187852680081206005285), upper := (281769778973723946368911040533859/182357381751929636114440315494941184) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi79QChiValue_eq :
    chi79QChiValue =
      (chi79Slice.qChiAD 8 chi79LogChiCertificate).value := by
  norm_num [chi79QChiValue, chi79LogChiCertificate, chi79Slice,
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
private theorem chi79LogChi_valid :
    (if chi79Slice.lo = 0 then
      if chi79Slice.hi = 0 then true
      else decide (chi79Slice.hi ≤ 1 / 4) &&
        chi79LogChiCertificate.check
          (IntervalAD.const chi79Slice.hi).value
    else chi79LogChiCertificate.check
      chi79Slice.chiAD.value) = true := by
  norm_num [chi79Slice, chi79LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi79ValidityFacts :
    ChiFacts chi79Slice chi79LogChiCertificate :=
  { domain := by norm_num [chi79Slice]
    onePlusPositive := by
      norm_num [chi79Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi79LogChi_valid }

noncomputable def chi79InputQChi : RationalEnclosure :=
  { lower := (-558853/16777216), upper := (6481/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi79InputQChi_eq :
    chi79InputQChi = outerEnclosure 24 chi79QChiValue := by
  rfl'

theorem chi79RoundedFacts :
    ChiRoundedFacts 8 chi79Slice chi79LogChiCertificate
      chi79InputQChi :=
  { coversQChi := by
      rw [chi79InputQChi_eq, chi79QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi80Slice : ChiSlice :=
  { lo := (11/16), hi := (23/32) }

noncomputable def chi80LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (11/8) }, upper := { exponent := -1, mantissa := (23/16) } }

private noncomputable def chi80QChiValue : RationalEnclosure :=
  { lower := (-22549769880732918694856788987231/141296667291424732265777355821064), upper := (-2960578958340220269375815338480584502530532391716757/22520568764212801492391747321918035794999071031118080) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi80QChiValue_eq :
    chi80QChiValue =
      (chi80Slice.qChiAD 8 chi80LogChiCertificate).value := by
  norm_num [chi80QChiValue, chi80LogChiCertificate, chi80Slice,
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
private theorem chi80LogChi_valid :
    (if chi80Slice.lo = 0 then
      if chi80Slice.hi = 0 then true
      else decide (chi80Slice.hi ≤ 1 / 4) &&
        chi80LogChiCertificate.check
          (IntervalAD.const chi80Slice.hi).value
    else chi80LogChiCertificate.check
      chi80Slice.chiAD.value) = true := by
  norm_num [chi80Slice, chi80LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi80ValidityFacts :
    ChiFacts chi80Slice chi80LogChiCertificate :=
  { domain := by norm_num [chi80Slice]
    onePlusPositive := by
      norm_num [chi80Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi80LogChi_valid }

noncomputable def chi80InputQChi : RationalEnclosure :=
  { lower := (-10459/65536), upper := (-2205551/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi80InputQChi_eq :
    chi80InputQChi = outerEnclosure 24 chi80QChiValue := by
  rfl'

theorem chi80RoundedFacts :
    ChiRoundedFacts 8 chi80Slice chi80LogChiCertificate
      chi80InputQChi :=
  { coversQChi := by
      rw [chi80InputQChi_eq, chi80QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi81Slice : ChiSlice :=
  { lo := (23/32), hi := (3/4) }

noncomputable def chi81LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (23/16) }, upper := { exponent := -1, mantissa := (3/2) } }

private noncomputable def chi81QChiValue : RationalEnclosure :=
  { lower := (-747053556209147346814436618/5184074924414615446703761275), upper := (-1785455651713336661719735855352460030463/15187719505120943691514925610351562500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi81QChiValue_eq :
    chi81QChiValue =
      (chi81Slice.qChiAD 8 chi81LogChiCertificate).value := by
  norm_num [chi81QChiValue, chi81LogChiCertificate, chi81Slice,
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
private theorem chi81LogChi_valid :
    (if chi81Slice.lo = 0 then
      if chi81Slice.hi = 0 then true
      else decide (chi81Slice.hi ≤ 1 / 4) &&
        chi81LogChiCertificate.check
          (IntervalAD.const chi81Slice.hi).value
    else chi81LogChiCertificate.check
      chi81Slice.chiAD.value) = true := by
  norm_num [chi81Slice, chi81LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi81ValidityFacts :
    ChiFacts chi81Slice chi81LogChiCertificate :=
  { domain := by norm_num [chi81Slice]
    onePlusPositive := by
      norm_num [chi81Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi81LogChi_valid }

noncomputable def chi81InputQChi : RationalEnclosure :=
  { lower := (-2417689/16777216), upper := (-1972315/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi81InputQChi_eq :
    chi81InputQChi = outerEnclosure 24 chi81QChiValue := by
  rfl'

theorem chi81RoundedFacts :
    ChiRoundedFacts 8 chi81Slice chi81LogChiCertificate
      chi81InputQChi :=
  { coversQChi := by
      rw [chi81InputQChi_eq, chi81QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi82Slice : ChiSlice :=
  { lo := (1/2), hi := (33/64) }

noncomputable def chi82LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (33/32) } }

private noncomputable def chi82QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2507041031040), upper := (-207232098147238319752902016166452146348559/949447008884047402441758795750000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi82QChiValue_eq :
    chi82QChiValue =
      (chi82Slice.qChiAD 8 chi82LogChiCertificate).value := by
  norm_num [chi82QChiValue, chi82LogChiCertificate, chi82Slice,
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
private theorem chi82LogChi_valid :
    (if chi82Slice.lo = 0 then
      if chi82Slice.hi = 0 then true
      else decide (chi82Slice.hi ≤ 1 / 4) &&
        chi82LogChiCertificate.check
          (IntervalAD.const chi82Slice.hi).value
    else chi82LogChiCertificate.check
      chi82Slice.chiAD.value) = true := by
  norm_num [chi82Slice, chi82LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi82ValidityFacts :
    ChiFacts chi82Slice chi82LogChiCertificate :=
  { domain := by norm_num [chi82Slice]
    onePlusPositive := by
      norm_num [chi82Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi82LogChi_valid }

noncomputable def chi82InputQChi : RationalEnclosure :=
  { lower := (-3997497/16777216), upper := (-3661897/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi82InputQChi_eq :
    chi82InputQChi = outerEnclosure 24 chi82QChiValue := by
  rfl'

theorem chi82RoundedFacts :
    ChiRoundedFacts 8 chi82Slice chi82LogChiCertificate
      chi82InputQChi :=
  { coversQChi := by
      rw [chi82InputQChi_eq, chi82QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi83Slice : ChiSlice :=
  { lo := (33/64), hi := (17/32) }

noncomputable def chi83LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (33/32) }, upper := { exponent := -1, mantissa := (17/16) } }

private noncomputable def chi83QChiValue : RationalEnclosure :=
  { lower := (-1166042427326977922500455749021820310771/5022302699988857516171412900695800781250), upper := (-43264351122907796239821934696267406299977171171615957301031/203355277555159511512962310289557964726489419101562500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi83QChiValue_eq :
    chi83QChiValue =
      (chi83Slice.qChiAD 8 chi83LogChiCertificate).value := by
  norm_num [chi83QChiValue, chi83LogChiCertificate, chi83Slice,
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
private theorem chi83LogChi_valid :
    (if chi83Slice.lo = 0 then
      if chi83Slice.hi = 0 then true
      else decide (chi83Slice.hi ≤ 1 / 4) &&
        chi83LogChiCertificate.check
          (IntervalAD.const chi83Slice.hi).value
    else chi83LogChiCertificate.check
      chi83Slice.chiAD.value) = true := by
  norm_num [chi83Slice, chi83LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi83ValidityFacts :
    ChiFacts chi83Slice chi83LogChiCertificate :=
  { domain := by norm_num [chi83Slice]
    onePlusPositive := by
      norm_num [chi83Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi83LogChi_valid }

noncomputable def chi83InputQChi : RationalEnclosure :=
  { lower := (-3895215/16777216), upper := (-3569395/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi83InputQChi_eq :
    chi83InputQChi = outerEnclosure 24 chi83QChiValue := by
  rfl'

theorem chi83RoundedFacts :
    ChiRoundedFacts 8 chi83Slice chi83LogChiCertificate
      chi83InputQChi :=
  { coversQChi := by
      rw [chi83InputQChi_eq, chi83QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi84Slice : ChiSlice :=
  { lo := (17/32), hi := (35/64) }

noncomputable def chi84LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (17/16) }, upper := { exponent := -1, mantissa := (35/32) } }

private noncomputable def chi84QChiValue : RationalEnclosure :=
  { lower := (-207003539428149538906283615/916346598786654549268370616), upper := (-766997851872446965175463960317724777590138273890192934693/3704514143036983194134062845061045879873756933940102604288) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi84QChiValue_eq :
    chi84QChiValue =
      (chi84Slice.qChiAD 8 chi84LogChiCertificate).value := by
  norm_num [chi84QChiValue, chi84LogChiCertificate, chi84Slice,
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
private theorem chi84LogChi_valid :
    (if chi84Slice.lo = 0 then
      if chi84Slice.hi = 0 then true
      else decide (chi84Slice.hi ≤ 1 / 4) &&
        chi84LogChiCertificate.check
          (IntervalAD.const chi84Slice.hi).value
    else chi84LogChiCertificate.check
      chi84Slice.chiAD.value) = true := by
  norm_num [chi84Slice, chi84LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi84ValidityFacts :
    ChiFacts chi84Slice chi84LogChiCertificate :=
  { domain := by norm_num [chi84Slice]
    onePlusPositive := by
      norm_num [chi84Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi84LogChi_valid }

noncomputable def chi84InputQChi : RationalEnclosure :=
  { lower := (-3789989/16777216), upper := (-3473623/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi84InputQChi_eq :
    chi84InputQChi = outerEnclosure 24 chi84QChiValue := by
  rfl'

theorem chi84RoundedFacts :
    ChiRoundedFacts 8 chi84Slice chi84LogChiCertificate
      chi84InputQChi :=
  { coversQChi := by
      rw [chi84InputQChi_eq, chi84QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi85Slice : ChiSlice :=
  { lo := (35/64), hi := (9/16) }

noncomputable def chi85LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (35/32) }, upper := { exponent := -1, mantissa := (9/8) } }

private noncomputable def chi85QChiValue : RationalEnclosure :=
  { lower := (-1280055138538888746756045106633600440589/5832555539783214429919451080654788660165), upper := (-193440464914506150885033134083418277679473556126613923019306669/961645906154116768596962881490585574520229539398398994384672000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi85QChiValue_eq :
    chi85QChiValue =
      (chi85Slice.qChiAD 8 chi85LogChiCertificate).value := by
  norm_num [chi85QChiValue, chi85LogChiCertificate, chi85Slice,
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
private theorem chi85LogChi_valid :
    (if chi85Slice.lo = 0 then
      if chi85Slice.hi = 0 then true
      else decide (chi85Slice.hi ≤ 1 / 4) &&
        chi85LogChiCertificate.check
          (IntervalAD.const chi85Slice.hi).value
    else chi85LogChiCertificate.check
      chi85Slice.chiAD.value) = true := by
  norm_num [chi85Slice, chi85LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi85ValidityFacts :
    ChiFacts chi85Slice chi85LogChiCertificate :=
  { domain := by norm_num [chi85Slice]
    onePlusPositive := by
      norm_num [chi85Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi85LogChi_valid }

noncomputable def chi85InputQChi : RationalEnclosure :=
  { lower := (-3682051/16777216), upper := (-3374831/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi85InputQChi_eq :
    chi85InputQChi = outerEnclosure 24 chi85QChiValue := by
  rfl'

theorem chi85RoundedFacts :
    ChiRoundedFacts 8 chi85Slice chi85LogChiCertificate
      chi85InputQChi :=
  { coversQChi := by
      rw [chi85InputQChi_eq, chi85QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi86Slice : ChiSlice :=
  { lo := (9/16), hi := (37/64) }

noncomputable def chi86LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (9/8) }, upper := { exponent := -1, mantissa := (37/32) } }

private noncomputable def chi86QChiValue : RationalEnclosure :=
  { lower := (-7502127834313597221929917424309/35240326973941137391962119358000), upper := (-3069144824436118330847439613904782268924041573986311699149/15731081513089149336588649190035551867415736402332457856000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi86QChiValue_eq :
    chi86QChiValue =
      (chi86Slice.qChiAD 8 chi86LogChiCertificate).value := by
  norm_num [chi86QChiValue, chi86LogChiCertificate, chi86Slice,
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
private theorem chi86LogChi_valid :
    (if chi86Slice.lo = 0 then
      if chi86Slice.hi = 0 then true
      else decide (chi86Slice.hi ≤ 1 / 4) &&
        chi86LogChiCertificate.check
          (IntervalAD.const chi86Slice.hi).value
    else chi86LogChiCertificate.check
      chi86Slice.chiAD.value) = true := by
  norm_num [chi86Slice, chi86LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi86ValidityFacts :
    ChiFacts chi86Slice chi86LogChiCertificate :=
  { domain := by norm_num [chi86Slice]
    onePlusPositive := by
      norm_num [chi86Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi86LogChi_valid }

noncomputable def chi86InputQChi : RationalEnclosure :=
  { lower := (-1785807/8388608), upper := (-1636623/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi86InputQChi_eq :
    chi86InputQChi = outerEnclosure 24 chi86QChiValue := by
  rfl'

theorem chi86RoundedFacts :
    ChiRoundedFacts 8 chi86Slice chi86LogChiCertificate
      chi86InputQChi :=
  { coversQChi := by
      rw [chi86InputQChi_eq, chi86QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi87Slice : ChiSlice :=
  { lo := (37/64), hi := (19/32) }

noncomputable def chi87LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (37/32) }, upper := { exponent := -1, mantissa := (19/16) } }

private noncomputable def chi87QChiValue : RationalEnclosure :=
  { lower := (-797456501804813502700891424596769/3868047622006235981090068856054490), upper := (-1531178288229989122517262512111980329702241250515641403147/8106102584998447597875464217947615055924911376562500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi87QChiValue_eq :
    chi87QChiValue =
      (chi87Slice.qChiAD 8 chi87LogChiCertificate).value := by
  norm_num [chi87QChiValue, chi87LogChiCertificate, chi87Slice,
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
private theorem chi87LogChi_valid :
    (if chi87Slice.lo = 0 then
      if chi87Slice.hi = 0 then true
      else decide (chi87Slice.hi ≤ 1 / 4) &&
        chi87LogChiCertificate.check
          (IntervalAD.const chi87Slice.hi).value
    else chi87LogChiCertificate.check
      chi87Slice.chiAD.value) = true := by
  norm_num [chi87Slice, chi87LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi87ValidityFacts :
    ChiFacts chi87Slice chi87LogChiCertificate :=
  { domain := by norm_num [chi87Slice]
    onePlusPositive := by
      norm_num [chi87Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi87LogChi_valid }

noncomputable def chi87InputQChi : RationalEnclosure :=
  { lower := (-3458877/16777216), upper := (-1584541/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi87InputQChi_eq :
    chi87InputQChi = outerEnclosure 24 chi87QChiValue := by
  rfl'

theorem chi87RoundedFacts :
    ChiRoundedFacts 8 chi87Slice chi87LogChiCertificate
      chi87InputQChi :=
  { coversQChi := by
      rw [chi87InputQChi_eq, chi87QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi88Slice : ChiSlice :=
  { lo := (3/4), hi := (25/32) }

noncomputable def chi88LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (25/16) } }

private noncomputable def chi88QChiValue : RationalEnclosure :=
  { lower := (-7566012198856161082619/58911791806054687500000), upper := (-431883678538450891077020030798860319207786901105599/4177581444585193813068970328884793762343750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi88QChiValue_eq :
    chi88QChiValue =
      (chi88Slice.qChiAD 8 chi88LogChiCertificate).value := by
  norm_num [chi88QChiValue, chi88LogChiCertificate, chi88Slice,
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
private theorem chi88LogChi_valid :
    (if chi88Slice.lo = 0 then
      if chi88Slice.hi = 0 then true
      else decide (chi88Slice.hi ≤ 1 / 4) &&
        chi88LogChiCertificate.check
          (IntervalAD.const chi88Slice.hi).value
    else chi88LogChiCertificate.check
      chi88Slice.chiAD.value) = true := by
  norm_num [chi88Slice, chi88LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi88ValidityFacts :
    ChiFacts chi88Slice chi88LogChiCertificate :=
  { domain := by norm_num [chi88Slice]
    onePlusPositive := by
      norm_num [chi88Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi88LogChi_valid }

noncomputable def chi88InputQChi : RationalEnclosure :=
  { lower := (-1077345/8388608), upper := (-1734449/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi88InputQChi_eq :
    chi88InputQChi = outerEnclosure 24 chi88QChiValue := by
  rfl'

theorem chi88RoundedFacts :
    ChiRoundedFacts 8 chi88Slice chi88LogChiCertificate
      chi88InputQChi :=
  { coversQChi := by
      rw [chi88InputQChi_eq, chi88QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi89Slice : ChiSlice :=
  { lo := (25/32), hi := (13/16) }

noncomputable def chi89LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (25/16) }, upper := { exponent := -1, mantissa := (13/8) } }

private noncomputable def chi89QChiValue : RationalEnclosure :=
  { lower := (-2487489459379230584004889185777731/22090821486693580437611674878015930), upper := (-21072676085935506202184815118493133561958598130633/236843436359975460368121551025937844249613036082560) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi89QChiValue_eq :
    chi89QChiValue =
      (chi89Slice.qChiAD 8 chi89LogChiCertificate).value := by
  norm_num [chi89QChiValue, chi89LogChiCertificate, chi89Slice,
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
private theorem chi89LogChi_valid :
    (if chi89Slice.lo = 0 then
      if chi89Slice.hi = 0 then true
      else decide (chi89Slice.hi ≤ 1 / 4) &&
        chi89LogChiCertificate.check
          (IntervalAD.const chi89Slice.hi).value
    else chi89LogChiCertificate.check
      chi89Slice.chiAD.value) = true := by
  norm_num [chi89Slice, chi89LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi89ValidityFacts :
    ChiFacts chi89Slice chi89LogChiCertificate :=
  { domain := by norm_num [chi89Slice]
    onePlusPositive := by
      norm_num [chi89Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi89LogChi_valid }

noncomputable def chi89InputQChi : RationalEnclosure :=
  { lower := (-1889163/16777216), upper := (-1492719/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi89InputQChi_eq :
    chi89InputQChi = outerEnclosure 24 chi89QChiValue := by
  rfl'

theorem chi89RoundedFacts :
    ChiRoundedFacts 8 chi89Slice chi89LogChiCertificate
      chi89InputQChi :=
  { coversQChi := by
      rw [chi89InputQChi_eq, chi89QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi90Slice : ChiSlice :=
  { lo := (13/16), hi := (27/32) }

noncomputable def chi90LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (13/8) }, upper := { exponent := -1, mantissa := (27/16) } }

private noncomputable def chi90QChiValue : RationalEnclosure :=
  { lower := (-121363036731826529946071/1255570022948891673343320), upper := (-16973821776814906526728383144511402142226085915609/228221114582900158418676120007900741908487584848640) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi90QChiValue_eq :
    chi90QChiValue =
      (chi90Slice.qChiAD 8 chi90LogChiCertificate).value := by
  norm_num [chi90QChiValue, chi90LogChiCertificate, chi90Slice,
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
private theorem chi90LogChi_valid :
    (if chi90Slice.lo = 0 then
      if chi90Slice.hi = 0 then true
      else decide (chi90Slice.hi ≤ 1 / 4) &&
        chi90LogChiCertificate.check
          (IntervalAD.const chi90Slice.hi).value
    else chi90LogChiCertificate.check
      chi90Slice.chiAD.value) = true := by
  norm_num [chi90Slice, chi90LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi90ValidityFacts :
    ChiFacts chi90Slice chi90LogChiCertificate :=
  { domain := by norm_num [chi90Slice]
    onePlusPositive := by
      norm_num [chi90Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi90LogChi_valid }

noncomputable def chi90InputQChi : RationalEnclosure :=
  { lower := (-1621681/16777216), upper := (-311949/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi90InputQChi_eq :
    chi90InputQChi = outerEnclosure 24 chi90QChiValue := by
  rfl'

theorem chi90RoundedFacts :
    ChiRoundedFacts 8 chi90Slice chi90LogChiCertificate
      chi90InputQChi :=
  { coversQChi := by
      rw [chi90InputQChi_eq, chi90QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi91Slice : ChiSlice :=
  { lo := (27/32), hi := (7/8) }

noncomputable def chi91LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (27/16) }, upper := { exponent := -1, mantissa := (7/4) } }

private noncomputable def chi91QChiValue : RationalEnclosure :=
  { lower := (-93036194240079690913499492075985521/1153864888804982617860587627909196639), upper := (-4559938031699281514274723851083697644241524892719169/76482327185670463472634385920700023536954014939985280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi91QChiValue_eq :
    chi91QChiValue =
      (chi91Slice.qChiAD 8 chi91LogChiCertificate).value := by
  norm_num [chi91QChiValue, chi91LogChiCertificate, chi91Slice,
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
private theorem chi91LogChi_valid :
    (if chi91Slice.lo = 0 then
      if chi91Slice.hi = 0 then true
      else decide (chi91Slice.hi ≤ 1 / 4) &&
        chi91LogChiCertificate.check
          (IntervalAD.const chi91Slice.hi).value
    else chi91LogChiCertificate.check
      chi91Slice.chiAD.value) = true := by
  norm_num [chi91Slice, chi91LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi91ValidityFacts :
    ChiFacts chi91Slice chi91LogChiCertificate :=
  { domain := by norm_num [chi91Slice]
    onePlusPositive := by
      norm_num [chi91Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi91LogChi_valid }

noncomputable def chi91InputQChi : RationalEnclosure :=
  { lower := (-338187/4194304), upper := (-1000271/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi91InputQChi_eq :
    chi91InputQChi = outerEnclosure 24 chi91QChiValue := by
  rfl'

theorem chi91RoundedFacts :
    ChiRoundedFacts 8 chi91Slice chi91LogChiCertificate
      chi91InputQChi :=
  { coversQChi := by
      rw [chi91InputQChi_eq, chi91QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi92Slice : ChiSlice :=
  { lo := (7/8), hi := (29/32) }

noncomputable def chi92LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (7/4) }, upper := { exponent := -1, mantissa := (29/16) } }

private noncomputable def chi92QChiValue : RationalEnclosure :=
  { lower := (-1267310901209858791427897027/19635998545428311770036513200), upper := (-7259463794408647757324535323047000076382315435767/162247656881015607947934156044950219921875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi92QChiValue_eq :
    chi92QChiValue =
      (chi92Slice.qChiAD 8 chi92LogChiCertificate).value := by
  norm_num [chi92QChiValue, chi92LogChiCertificate, chi92Slice,
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
private theorem chi92LogChi_valid :
    (if chi92Slice.lo = 0 then
      if chi92Slice.hi = 0 then true
      else decide (chi92Slice.hi ≤ 1 / 4) &&
        chi92LogChiCertificate.check
          (IntervalAD.const chi92Slice.hi).value
    else chi92LogChiCertificate.check
      chi92Slice.chiAD.value) = true := by
  norm_num [chi92Slice, chi92LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi92ValidityFacts :
    ChiFacts chi92Slice chi92LogChiCertificate :=
  { domain := by norm_num [chi92Slice]
    onePlusPositive := by
      norm_num [chi92Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi92LogChi_valid }

noncomputable def chi92InputQChi : RationalEnclosure :=
  { lower := (-1082805/16777216), upper := (-93833/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi92InputQChi_eq :
    chi92InputQChi = outerEnclosure 24 chi92QChiValue := by
  rfl'

theorem chi92RoundedFacts :
    ChiRoundedFacts 8 chi92Slice chi92LogChiCertificate
      chi92InputQChi :=
  { coversQChi := by
      rw [chi92InputQChi_eq, chi92QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi93Slice : ChiSlice :=
  { lo := (29/32), hi := (15/16) }

noncomputable def chi93LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (29/16) }, upper := { exponent := -1, mantissa := (15/8) } }

private noncomputable def chi93QChiValue : RationalEnclosure :=
  { lower := (-37148820873698975162107950569/767329004933554845520019531250), upper := (-60418683996974239018471597618793517777892807928415923/2029601743098425045879957479977185201019785156250000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi93QChiValue_eq :
    chi93QChiValue =
      (chi93Slice.qChiAD 8 chi93LogChiCertificate).value := by
  norm_num [chi93QChiValue, chi93LogChiCertificate, chi93Slice,
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
private theorem chi93LogChi_valid :
    (if chi93Slice.lo = 0 then
      if chi93Slice.hi = 0 then true
      else decide (chi93Slice.hi ≤ 1 / 4) &&
        chi93LogChiCertificate.check
          (IntervalAD.const chi93Slice.hi).value
    else chi93LogChiCertificate.check
      chi93Slice.chiAD.value) = true := by
  norm_num [chi93Slice, chi93LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi93ValidityFacts :
    ChiFacts chi93Slice chi93LogChiCertificate :=
  { domain := by norm_num [chi93Slice]
    onePlusPositive := by
      norm_num [chi93Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi93LogChi_valid }

noncomputable def chi93InputQChi : RationalEnclosure :=
  { lower := (-812239/16777216), upper := (-124859/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi93InputQChi_eq :
    chi93InputQChi = outerEnclosure 24 chi93QChiValue := by
  rfl'

theorem chi93RoundedFacts :
    ChiRoundedFacts 8 chi93Slice chi93LogChiCertificate
      chi93InputQChi :=
  { coversQChi := by
      rw [chi93InputQChi_eq, chi93QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi94Slice : ChiSlice :=
  { lo := (15/16), hi := (31/32) }

noncomputable def chi94LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (15/8) }, upper := { exponent := -1, mantissa := (31/16) } }

private noncomputable def chi94QChiValue : RationalEnclosure :=
  { lower := (-14829988367038102440469002133361/459570014495790413594859666065880), upper := (-22589127367615459074876566182479146482500641616411432338428061/1534388832740899830732209640578410501175897214258071023611813120) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi94QChiValue_eq :
    chi94QChiValue =
      (chi94Slice.qChiAD 8 chi94LogChiCertificate).value := by
  norm_num [chi94QChiValue, chi94LogChiCertificate, chi94Slice,
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
private theorem chi94LogChi_valid :
    (if chi94Slice.lo = 0 then
      if chi94Slice.hi = 0 then true
      else decide (chi94Slice.hi ≤ 1 / 4) &&
        chi94LogChiCertificate.check
          (IntervalAD.const chi94Slice.hi).value
    else chi94LogChiCertificate.check
      chi94Slice.chiAD.value) = true := by
  norm_num [chi94Slice, chi94LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi94ValidityFacts :
    ChiFacts chi94Slice chi94LogChiCertificate :=
  { domain := by norm_num [chi94Slice]
    onePlusPositive := by
      norm_num [chi94Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi94LogChi_valid }

noncomputable def chi94InputQChi : RationalEnclosure :=
  { lower := (-541389/16777216), upper := (-15437/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi94InputQChi_eq :
    chi94InputQChi = outerEnclosure 24 chi94QChiValue := by
  rfl'

theorem chi94RoundedFacts :
    ChiRoundedFacts 8 chi94Slice chi94LogChiCertificate
      chi94InputQChi :=
  { coversQChi := by
      rw [chi94InputQChi_eq, chi94QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi95Slice : ChiSlice :=
  { lo := (31/32), hi := (1) }

noncomputable def chi95LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (31/16) }, upper := { exponent := 0, mantissa := (1) } }

private noncomputable def chi95QChiValue : RationalEnclosure :=
  { lower := (-2640512086851919203099596033966946376/163739166687922797468607952932285640445), upper := (63042226073589570974002855310960844727/167668906688432944607854543802660495815680) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi95QChiValue_eq :
    chi95QChiValue =
      (chi95Slice.qChiAD 8 chi95LogChiCertificate).value := by
  norm_num [chi95QChiValue, chi95LogChiCertificate, chi95Slice,
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
private theorem chi95LogChi_valid :
    (if chi95Slice.lo = 0 then
      if chi95Slice.hi = 0 then true
      else decide (chi95Slice.hi ≤ 1 / 4) &&
        chi95LogChiCertificate.check
          (IntervalAD.const chi95Slice.hi).value
    else chi95LogChiCertificate.check
      chi95Slice.chiAD.value) = true := by
  norm_num [chi95Slice, chi95LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi95ValidityFacts :
    ChiFacts chi95Slice chi95LogChiCertificate :=
  { domain := by norm_num [chi95Slice]
    onePlusPositive := by
      norm_num [chi95Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi95LogChi_valid }

noncomputable def chi95InputQChi : RationalEnclosure :=
  { lower := (-270555/16777216), upper := (6309/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi95InputQChi_eq :
    chi95InputQChi = outerEnclosure 24 chi95QChiValue := by
  rfl'

theorem chi95RoundedFacts :
    ChiRoundedFacts 8 chi95Slice chi95LogChiCertificate
      chi95InputQChi :=
  { coversQChi := by
      rw [chi95InputQChi_eq, chi95QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi96Slice : ChiSlice :=
  { lo := (3/64), hi := (7/128) }

noncomputable def chi96LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (3/2) }, upper := { exponent := -5, mantissa := (7/4) } }

private noncomputable def chi96QChiValue : RationalEnclosure :=
  { lower := (-7316803602317445751829/45768669422607421875000), upper := (-26528337002114820266650688478750041379473/206482057807151088123116933935546875000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi96QChiValue_eq :
    chi96QChiValue =
      (chi96Slice.qChiAD 8 chi96LogChiCertificate).value := by
  norm_num [chi96QChiValue, chi96LogChiCertificate, chi96Slice,
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
private theorem chi96LogChi_valid :
    (if chi96Slice.lo = 0 then
      if chi96Slice.hi = 0 then true
      else decide (chi96Slice.hi ≤ 1 / 4) &&
        chi96LogChiCertificate.check
          (IntervalAD.const chi96Slice.hi).value
    else chi96LogChiCertificate.check
      chi96Slice.chiAD.value) = true := by
  norm_num [chi96Slice, chi96LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi96ValidityFacts :
    ChiFacts chi96Slice chi96LogChiCertificate :=
  { domain := by norm_num [chi96Slice]
    onePlusPositive := by
      norm_num [chi96Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi96LogChi_valid }

noncomputable def chi96InputQChi : RationalEnclosure :=
  { lower := (-335261/2097152), upper := (-2155497/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi96InputQChi_eq :
    chi96InputQChi = outerEnclosure 24 chi96QChiValue := by
  rfl'

theorem chi96RoundedFacts :
    ChiRoundedFacts 8 chi96Slice chi96LogChiCertificate
      chi96InputQChi :=
  { coversQChi := by
      rw [chi96InputQChi_eq, chi96QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi97Slice : ChiSlice :=
  { lo := (7/128), hi := (1/16) }

noncomputable def chi97LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (7/4) }, upper := { exponent := -4, mantissa := (1) } }

private noncomputable def chi97QChiValue : RationalEnclosure :=
  { lower := (-1902152398673393588301683638/11045249181803425370645538675), upper := (-3415523760331535920967606584187/24034462219604253606524692156800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi97QChiValue_eq :
    chi97QChiValue =
      (chi97Slice.qChiAD 8 chi97LogChiCertificate).value := by
  norm_num [chi97QChiValue, chi97LogChiCertificate, chi97Slice,
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
private theorem chi97LogChi_valid :
    (if chi97Slice.lo = 0 then
      if chi97Slice.hi = 0 then true
      else decide (chi97Slice.hi ≤ 1 / 4) &&
        chi97LogChiCertificate.check
          (IntervalAD.const chi97Slice.hi).value
    else chi97LogChiCertificate.check
      chi97Slice.chiAD.value) = true := by
  norm_num [chi97Slice, chi97LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi97ValidityFacts :
    ChiFacts chi97Slice chi97LogChiCertificate :=
  { domain := by norm_num [chi97Slice]
    onePlusPositive := by
      norm_num [chi97Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi97LogChi_valid }

noncomputable def chi97InputQChi : RationalEnclosure :=
  { lower := (-2889281/16777216), upper := (-298025/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi97InputQChi_eq :
    chi97InputQChi = outerEnclosure 24 chi97QChiValue := by
  rfl'

theorem chi97RoundedFacts :
    ChiRoundedFacts 8 chi97Slice chi97LogChiCertificate
      chi97InputQChi :=
  { coversQChi := by
      rw [chi97InputQChi_eq, chi97QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi98Slice : ChiSlice :=
  { lo := (7/64), hi := (15/128) }

noncomputable def chi98LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (7/4) }, upper := { exponent := -4, mantissa := (15/8) } }

private noncomputable def chi98QChiValue : RationalEnclosure :=
  { lower := (-25865437267088201934282985/110647293390905566323221622), upper := (-30470419263380651458056444372231333598313695311577/145388158000780153241532770202837720713376538922112) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi98QChiValue_eq :
    chi98QChiValue =
      (chi98Slice.qChiAD 8 chi98LogChiCertificate).value := by
  norm_num [chi98QChiValue, chi98LogChiCertificate, chi98Slice,
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
private theorem chi98LogChi_valid :
    (if chi98Slice.lo = 0 then
      if chi98Slice.hi = 0 then true
      else decide (chi98Slice.hi ≤ 1 / 4) &&
        chi98LogChiCertificate.check
          (IntervalAD.const chi98Slice.hi).value
    else chi98LogChiCertificate.check
      chi98Slice.chiAD.value) = true := by
  norm_num [chi98Slice, chi98LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi98ValidityFacts :
    ChiFacts chi98Slice chi98LogChiCertificate :=
  { domain := by norm_num [chi98Slice]
    onePlusPositive := by
      norm_num [chi98Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi98LogChi_valid }

noncomputable def chi98InputQChi : RationalEnclosure :=
  { lower := (-1960961/8388608), upper := (-3516165/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi98InputQChi_eq :
    chi98InputQChi = outerEnclosure 24 chi98QChiValue := by
  rfl'

theorem chi98RoundedFacts :
    ChiRoundedFacts 8 chi98Slice chi98LogChiCertificate
      chi98InputQChi :=
  { coversQChi := by
      rw [chi98InputQChi_eq, chi98QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi99Slice : ChiSlice :=
  { lo := (15/128), hi := (1/8) }

noncomputable def chi99LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (15/8) }, upper := { exponent := -3, mantissa := (1) } }

private noncomputable def chi99QChiValue : RationalEnclosure :=
  { lower := (-394123591525339629404666158096336/1642962801822450728601623306185521), upper := (-1023511924192687179032744529928362097/4731732869248658098372675121814300480) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi99QChiValue_eq :
    chi99QChiValue =
      (chi99Slice.qChiAD 8 chi99LogChiCertificate).value := by
  norm_num [chi99QChiValue, chi99LogChiCertificate, chi99Slice,
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
private theorem chi99LogChi_valid :
    (if chi99Slice.lo = 0 then
      if chi99Slice.hi = 0 then true
      else decide (chi99Slice.hi ≤ 1 / 4) &&
        chi99LogChiCertificate.check
          (IntervalAD.const chi99Slice.hi).value
    else chi99LogChiCertificate.check
      chi99Slice.chiAD.value) = true := by
  norm_num [chi99Slice, chi99LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi99ValidityFacts :
    ChiFacts chi99Slice chi99LogChiCertificate :=
  { domain := by norm_num [chi99Slice]
    onePlusPositive := by
      norm_num [chi99Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi99LogChi_valid }

noncomputable def chi99InputQChi : RationalEnclosure :=
  { lower := (-2012309/8388608), upper := (-1814523/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi99InputQChi_eq :
    chi99InputQChi = outerEnclosure 24 chi99QChiValue := by
  rfl'

theorem chi99RoundedFacts :
    ChiRoundedFacts 8 chi99Slice chi99LogChiCertificate
      chi99InputQChi :=
  { coversQChi := by
      rw [chi99InputQChi_eq, chi99QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi100Slice : ChiSlice :=
  { lo := (0), hi := (1/64) }

noncomputable def chi100LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -6, mantissa := (1) }, upper := { exponent := -6, mantissa := (1) } }

private noncomputable def chi100QChiValue : RationalEnclosure :=
  { lower := (-597351034279/9336116339550), upper := (0) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi100QChiValue_eq :
    chi100QChiValue =
      (chi100Slice.qChiAD 8 chi100LogChiCertificate).value := by
  norm_num [chi100QChiValue, chi100LogChiCertificate, chi100Slice,
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
private theorem chi100LogChi_valid :
    (if chi100Slice.lo = 0 then
      if chi100Slice.hi = 0 then true
      else decide (chi100Slice.hi ≤ 1 / 4) &&
        chi100LogChiCertificate.check
          (IntervalAD.const chi100Slice.hi).value
    else chi100LogChiCertificate.check
      chi100Slice.chiAD.value) = true := by
  norm_num [chi100Slice, chi100LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi100ValidityFacts :
    ChiFacts chi100Slice chi100LogChiCertificate :=
  { domain := by norm_num [chi100Slice]
    onePlusPositive := by
      norm_num [chi100Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi100LogChi_valid }

noncomputable def chi100InputQChi : RationalEnclosure :=
  { lower := (-536727/8388608), upper := (0) }

set_option maxRecDepth 1000000 in
private theorem chi100InputQChi_eq :
    chi100InputQChi = outerEnclosure 24 chi100QChiValue := by
  rfl'

theorem chi100RoundedFacts :
    ChiRoundedFacts 8 chi100Slice chi100LogChiCertificate
      chi100InputQChi :=
  { coversQChi := by
      rw [chi100InputQChi_eq, chi100QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi101Slice : ChiSlice :=
  { lo := (1/64), hi := (3/128) }

noncomputable def chi101LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -6, mantissa := (1) }, upper := { exponent := -6, mantissa := (3/2) } }

private noncomputable def chi101QChiValue : RationalEnclosure :=
  { lower := (-597351034279/6224077559700), upper := (-201249473104791251178301/3619292259946289062500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi101QChiValue_eq :
    chi101QChiValue =
      (chi101Slice.qChiAD 8 chi101LogChiCertificate).value := by
  norm_num [chi101QChiValue, chi101LogChiCertificate, chi101Slice,
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
private theorem chi101LogChi_valid :
    (if chi101Slice.lo = 0 then
      if chi101Slice.hi = 0 then true
      else decide (chi101Slice.hi ≤ 1 / 4) &&
        chi101LogChiCertificate.check
          (IntervalAD.const chi101Slice.hi).value
    else chi101LogChiCertificate.check
      chi101Slice.chiAD.value) = true := by
  norm_num [chi101Slice, chi101LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi101ValidityFacts :
    ChiFacts chi101Slice chi101LogChiCertificate :=
  { domain := by norm_num [chi101Slice]
    onePlusPositive := by
      norm_num [chi101Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi101LogChi_valid }

noncomputable def chi101InputQChi : RationalEnclosure :=
  { lower := (-1610181/16777216), upper := (-932891/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi101InputQChi_eq :
    chi101InputQChi = outerEnclosure 24 chi101QChiValue := by
  rfl'

theorem chi101RoundedFacts :
    ChiRoundedFacts 8 chi101Slice chi101LogChiCertificate
      chi101InputQChi :=
  { coversQChi := by
      rw [chi101InputQChi_eq, chi101QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi102Slice : ChiSlice :=
  { lo := (3/128), hi := (1/32) }

noncomputable def chi102LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -6, mantissa := (3/2) }, upper := { exponent := -5, mantissa := (1) } }

private noncomputable def chi102QChiValue : RationalEnclosure :=
  { lower := (-32904848827383612938998/287107318697662353515625), upper := (-70526402650477155090297313/909555985634194335937500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi102QChiValue_eq :
    chi102QChiValue =
      (chi102Slice.qChiAD 8 chi102LogChiCertificate).value := by
  norm_num [chi102QChiValue, chi102LogChiCertificate, chi102Slice,
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
private theorem chi102LogChi_valid :
    (if chi102Slice.lo = 0 then
      if chi102Slice.hi = 0 then true
      else decide (chi102Slice.hi ≤ 1 / 4) &&
        chi102LogChiCertificate.check
          (IntervalAD.const chi102Slice.hi).value
    else chi102LogChiCertificate.check
      chi102Slice.chiAD.value) = true := by
  norm_num [chi102Slice, chi102LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi102ValidityFacts :
    ChiFacts chi102Slice chi102LogChiCertificate :=
  { domain := by norm_num [chi102Slice]
    onePlusPositive := by
      norm_num [chi102Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi102LogChi_valid }

noncomputable def chi102InputQChi : RationalEnclosure :=
  { lower := (-1922807/16777216), upper := (-650447/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi102InputQChi_eq :
    chi102InputQChi = outerEnclosure 24 chi102QChiValue := by
  rfl'

theorem chi102RoundedFacts :
    ChiRoundedFacts 8 chi102Slice chi102LogChiCertificate
      chi102InputQChi :=
  { coversQChi := by
      rw [chi102InputQChi_eq, chi102QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi103Slice : ChiSlice :=
  { lo := (5/64), hi := (11/128) }

noncomputable def chi103LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (5/4) }, upper := { exponent := -4, mantissa := (11/8) } }

private noncomputable def chi103QChiValue : RationalEnclosure :=
  { lower := (-1576299222410328361/7756742510533806426), upper := (-441188704462000224000451822585762862102791/2505030494525055626032300978063533162752640) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi103QChiValue_eq :
    chi103QChiValue =
      (chi103Slice.qChiAD 8 chi103LogChiCertificate).value := by
  norm_num [chi103QChiValue, chi103LogChiCertificate, chi103Slice,
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
private theorem chi103LogChi_valid :
    (if chi103Slice.lo = 0 then
      if chi103Slice.hi = 0 then true
      else decide (chi103Slice.hi ≤ 1 / 4) &&
        chi103LogChiCertificate.check
          (IntervalAD.const chi103Slice.hi).value
    else chi103LogChiCertificate.check
      chi103Slice.chiAD.value) = true := by
  norm_num [chi103Slice, chi103LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi103ValidityFacts :
    ChiFacts chi103Slice chi103LogChiCertificate :=
  { domain := by norm_num [chi103Slice]
    onePlusPositive := by
      norm_num [chi103Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi103LogChi_valid }

noncomputable def chi103InputQChi : RationalEnclosure :=
  { lower := (-1704705/8388608), upper := (-2954821/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi103InputQChi_eq :
    chi103InputQChi = outerEnclosure 24 chi103QChiValue := by
  rfl'

theorem chi103RoundedFacts :
    ChiRoundedFacts 8 chi103Slice chi103LogChiCertificate
      chi103InputQChi :=
  { coversQChi := by
      rw [chi103InputQChi_eq, chi103QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi104Slice : ChiSlice :=
  { lo := (11/128), hi := (3/32) }

noncomputable def chi104LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (11/8) }, upper := { exponent := -4, mantissa := (3/2) } }

private noncomputable def chi104QChiValue : RationalEnclosure :=
  { lower := (-32107509685565634177538738149748/151545036678302760686288985024135), upper := (-274658748446973694025175229595468222459667107/1479931998811550397327040869376318359375000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi104QChiValue_eq :
    chi104QChiValue =
      (chi104Slice.qChiAD 8 chi104LogChiCertificate).value := by
  norm_num [chi104QChiValue, chi104LogChiCertificate, chi104Slice,
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
private theorem chi104LogChi_valid :
    (if chi104Slice.lo = 0 then
      if chi104Slice.hi = 0 then true
      else decide (chi104Slice.hi ≤ 1 / 4) &&
        chi104LogChiCertificate.check
          (IntervalAD.const chi104Slice.hi).value
    else chi104LogChiCertificate.check
      chi104Slice.chiAD.value) = true := by
  norm_num [chi104Slice, chi104LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi104ValidityFacts :
    ChiFacts chi104Slice chi104LogChiCertificate :=
  { domain := by norm_num [chi104Slice]
    onePlusPositive := by
      norm_num [chi104Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi104LogChi_valid }

noncomputable def chi104InputQChi : RationalEnclosure :=
  { lower := (-444319/2097152), upper := (-1556831/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi104InputQChi_eq :
    chi104InputQChi = outerEnclosure 24 chi104QChiValue := by
  rfl'

theorem chi104RoundedFacts :
    ChiRoundedFacts 8 chi104Slice chi104LogChiCertificate
      chi104InputQChi :=
  { coversQChi := by
      rw [chi104InputQChi_eq, chi104QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi105Slice : ChiSlice :=
  { lo := (3/32), hi := (13/128) }

noncomputable def chi105LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (3/2) }, upper := { exponent := -4, mantissa := (13/8) } }

private noncomputable def chi105QChiValue : RationalEnclosure :=
  { lower := (-15563783192208241930811/70807442074584960937500), upper := (-4738066748112038028763003954848349997/24388322258310631573775976562500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi105QChiValue_eq :
    chi105QChiValue =
      (chi105Slice.qChiAD 8 chi105LogChiCertificate).value := by
  norm_num [chi105QChiValue, chi105LogChiCertificate, chi105Slice,
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
private theorem chi105LogChi_valid :
    (if chi105Slice.lo = 0 then
      if chi105Slice.hi = 0 then true
      else decide (chi105Slice.hi ≤ 1 / 4) &&
        chi105LogChiCertificate.check
          (IntervalAD.const chi105Slice.hi).value
    else chi105LogChiCertificate.check
      chi105Slice.chiAD.value) = true := by
  norm_num [chi105Slice, chi105LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi105ValidityFacts :
    ChiFacts chi105Slice chi105LogChiCertificate :=
  { domain := by norm_num [chi105Slice]
    onePlusPositive := by
      norm_num [chi105Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi105LogChi_valid }

noncomputable def chi105InputQChi : RationalEnclosure :=
  { lower := (-3687705/16777216), upper := (-3259411/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi105InputQChi_eq :
    chi105InputQChi = outerEnclosure 24 chi105QChiValue := by
  rfl'

theorem chi105RoundedFacts :
    ChiRoundedFacts 8 chi105Slice chi105LogChiCertificate
      chi105InputQChi :=
  { coversQChi := by
      rw [chi105InputQChi_eq, chi105QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi106Slice : ChiSlice :=
  { lo := (13/128), hi := (7/64) }

noncomputable def chi106LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (13/8) }, upper := { exponent := -4, mantissa := (7/4) } }

private noncomputable def chi106QChiValue : RationalEnclosure :=
  { lower := (-668387399423260834759342/2943322091974403079075135), upper := (-7190628808526477048544628379953342703914237/35552630981168044538237403843956605365113280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi106QChiValue_eq :
    chi106QChiValue =
      (chi106Slice.qChiAD 8 chi106LogChiCertificate).value := by
  norm_num [chi106QChiValue, chi106LogChiCertificate, chi106Slice,
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
private theorem chi106LogChi_valid :
    (if chi106Slice.lo = 0 then
      if chi106Slice.hi = 0 then true
      else decide (chi106Slice.hi ≤ 1 / 4) &&
        chi106LogChiCertificate.check
          (IntervalAD.const chi106Slice.hi).value
    else chi106LogChiCertificate.check
      chi106Slice.chiAD.value) = true := by
  norm_num [chi106Slice, chi106LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi106ValidityFacts :
    ChiFacts chi106Slice chi106LogChiCertificate :=
  { domain := by norm_num [chi106Slice]
    onePlusPositive := by
      norm_num [chi106Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi106LogChi_valid }

noncomputable def chi106InputQChi : RationalEnclosure :=
  { lower := (-238117/1048576), upper := (-3393243/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi106InputQChi_eq :
    chi106InputQChi = outerEnclosure 24 chi106QChiValue := by
  rfl'

theorem chi106RoundedFacts :
    ChiRoundedFacts 8 chi106Slice chi106LogChiCertificate
      chi106InputQChi :=
  { coversQChi := by
      rw [chi106InputQChi_eq, chi106QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi107Slice : ChiSlice :=
  { lo := (1/8), hi := (17/128) }

noncomputable def chi107LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -3, mantissa := (17/16) } }

private noncomputable def chi107QChiValue : RationalEnclosure :=
  { lower := (-10154967582743/41366177012160), upper := (-4680098057297663765274401977/21035736392678179881782261760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi107QChiValue_eq :
    chi107QChiValue =
      (chi107Slice.qChiAD 8 chi107LogChiCertificate).value := by
  norm_num [chi107QChiValue, chi107LogChiCertificate, chi107Slice,
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
private theorem chi107LogChi_valid :
    (if chi107Slice.lo = 0 then
      if chi107Slice.hi = 0 then true
      else decide (chi107Slice.hi ≤ 1 / 4) &&
        chi107LogChiCertificate.check
          (IntervalAD.const chi107Slice.hi).value
    else chi107LogChiCertificate.check
      chi107Slice.chiAD.value) = true := by
  norm_num [chi107Slice, chi107LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi107ValidityFacts :
    ChiFacts chi107Slice chi107LogChiCertificate :=
  { domain := by norm_num [chi107Slice]
    onePlusPositive := by
      norm_num [chi107Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi107LogChi_valid }

noncomputable def chi107InputQChi : RationalEnclosure :=
  { lower := (-4118633/16777216), upper := (-466581/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi107InputQChi_eq :
    chi107InputQChi = outerEnclosure 24 chi107QChiValue := by
  rfl'

theorem chi107RoundedFacts :
    ChiRoundedFacts 8 chi107Slice chi107LogChiCertificate
      chi107InputQChi :=
  { coversQChi := by
      rw [chi107InputQChi_eq, chi107QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi108Slice : ChiSlice :=
  { lo := (17/128), hi := (9/64) }

noncomputable def chi108LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (17/16) }, upper := { exponent := -3, mantissa := (9/8) } }

private noncomputable def chi108QChiValue : RationalEnclosure :=
  { lower := (-660691451144603818888120093/2636314619525097413569717050), upper := (-1856193307088912200258470349644701372196912290377/8136016022712379401925479793567576733982868540800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi108QChiValue_eq :
    chi108QChiValue =
      (chi108Slice.qChiAD 8 chi108LogChiCertificate).value := by
  norm_num [chi108QChiValue, chi108LogChiCertificate, chi108Slice,
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
private theorem chi108LogChi_valid :
    (if chi108Slice.lo = 0 then
      if chi108Slice.hi = 0 then true
      else decide (chi108Slice.hi ≤ 1 / 4) &&
        chi108LogChiCertificate.check
          (IntervalAD.const chi108Slice.hi).value
    else chi108LogChiCertificate.check
      chi108Slice.chiAD.value) = true := by
  norm_num [chi108Slice, chi108LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi108ValidityFacts :
    ChiFacts chi108Slice chi108LogChiCertificate :=
  { domain := by norm_num [chi108Slice]
    onePlusPositive := by
      norm_num [chi108Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi108LogChi_valid }

noncomputable def chi108InputQChi : RationalEnclosure :=
  { lower := (-525571/2097152), upper := (-3827641/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi108InputQChi_eq :
    chi108InputQChi = outerEnclosure 24 chi108QChiValue := by
  rfl'

theorem chi108RoundedFacts :
    ChiRoundedFacts 8 chi108Slice chi108LogChiCertificate
      chi108InputQChi :=
  { coversQChi := by
      rw [chi108InputQChi_eq, chi108QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi109Slice : ChiSlice :=
  { lo := (9/64), hi := (19/128) }

noncomputable def chi109LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (9/8) }, upper := { exponent := -3, mantissa := (19/16) } }

private noncomputable def chi109QChiValue : RationalEnclosure :=
  { lower := (-419827489657497806752133891693/1644548592117253078291565570040), upper := (-7402613803145301502396419059454441669177587882894165613779/31725981718565567933419154172885307825409202070312500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi109QChiValue_eq :
    chi109QChiValue =
      (chi109Slice.qChiAD 8 chi109LogChiCertificate).value := by
  norm_num [chi109QChiValue, chi109LogChiCertificate, chi109Slice,
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
private theorem chi109LogChi_valid :
    (if chi109Slice.lo = 0 then
      if chi109Slice.hi = 0 then true
      else decide (chi109Slice.hi ≤ 1 / 4) &&
        chi109LogChiCertificate.check
          (IntervalAD.const chi109Slice.hi).value
    else chi109LogChiCertificate.check
      chi109Slice.chiAD.value) = true := by
  norm_num [chi109Slice, chi109LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi109ValidityFacts :
    ChiFacts chi109Slice chi109LogChiCertificate :=
  { domain := by norm_num [chi109Slice]
    onePlusPositive := by
      norm_num [chi109Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi109LogChi_valid }

noncomputable def chi109InputQChi : RationalEnclosure :=
  { lower := (-4282961/16777216), upper := (-1957311/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi109InputQChi_eq :
    chi109InputQChi = outerEnclosure 24 chi109QChiValue := by
  rfl'

theorem chi109RoundedFacts :
    ChiRoundedFacts 8 chi109Slice chi109LogChiCertificate
      chi109InputQChi :=
  { coversQChi := by
      rw [chi109InputQChi_eq, chi109QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi110Slice : ChiSlice :=
  { lo := (19/128), hi := (5/32) }

noncomputable def chi110LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (19/16) }, upper := { exponent := -3, mantissa := (5/4) } }

private noncomputable def chi110QChiValue : RationalEnclosure :=
  { lower := (-11342031784014910107678188108591723/43701149259406351124552032470703125), upper := (-707009326515516120777188879314909861160093401/2969773808781389117098889424841558593750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi110QChiValue_eq :
    chi110QChiValue =
      (chi110Slice.qChiAD 8 chi110LogChiCertificate).value := by
  norm_num [chi110QChiValue, chi110LogChiCertificate, chi110Slice,
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
private theorem chi110LogChi_valid :
    (if chi110Slice.lo = 0 then
      if chi110Slice.hi = 0 then true
      else decide (chi110Slice.hi ≤ 1 / 4) &&
        chi110LogChiCertificate.check
          (IntervalAD.const chi110Slice.hi).value
    else chi110LogChiCertificate.check
      chi110Slice.chiAD.value) = true := by
  norm_num [chi110Slice, chi110LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi110ValidityFacts :
    ChiFacts chi110Slice chi110LogChiCertificate :=
  { domain := by norm_num [chi110Slice]
    onePlusPositive := by
      norm_num [chi110Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi110LogChi_valid }

noncomputable def chi110InputQChi : RationalEnclosure :=
  { lower := (-544287/2097152), upper := (-3994125/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi110InputQChi_eq :
    chi110InputQChi = outerEnclosure 24 chi110QChiValue := by
  rfl'

theorem chi110RoundedFacts :
    ChiRoundedFacts 8 chi110Slice chi110LogChiCertificate
      chi110InputQChi :=
  { coversQChi := by
      rw [chi110InputQChi_eq, chi110QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi111Slice : ChiSlice :=
  { lo := (5/32), hi := (21/128) }

noncomputable def chi111LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (5/4) }, upper := { exponent := -3, mantissa := (21/16) } }

private noncomputable def chi111QChiValue : RationalEnclosure :=
  { lower := (-22954650010983384167/87149598393023028720), upper := (-47018659640818334915615490327236738861244139175/193979365095501636214724783619528904250248161792) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi111QChiValue_eq :
    chi111QChiValue =
      (chi111Slice.qChiAD 8 chi111LogChiCertificate).value := by
  norm_num [chi111QChiValue, chi111LogChiCertificate, chi111Slice,
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
private theorem chi111LogChi_valid :
    (if chi111Slice.lo = 0 then
      if chi111Slice.hi = 0 then true
      else decide (chi111Slice.hi ≤ 1 / 4) &&
        chi111LogChiCertificate.check
          (IntervalAD.const chi111Slice.hi).value
    else chi111LogChiCertificate.check
      chi111Slice.chiAD.value) = true := by
  norm_num [chi111Slice, chi111LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi111ValidityFacts :
    ChiFacts chi111Slice chi111LogChiCertificate :=
  { domain := by norm_num [chi111Slice]
    onePlusPositive := by
      norm_num [chi111Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi111LogChi_valid }

noncomputable def chi111InputQChi : RationalEnclosure :=
  { lower := (-4419013/16777216), upper := (-4066629/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi111InputQChi_eq :
    chi111InputQChi = outerEnclosure 24 chi111QChiValue := by
  rfl'

theorem chi111RoundedFacts :
    ChiRoundedFacts 8 chi111Slice chi111LogChiCertificate
      chi111InputQChi :=
  { coversQChi := by
      rw [chi111InputQChi_eq, chi111QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi112Slice : ChiSlice :=
  { lo := (21/128), hi := (11/64) }

noncomputable def chi112LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (21/16) }, upper := { exponent := -3, mantissa := (11/8) } }

private noncomputable def chi112QChiValue : RationalEnclosure :=
  { lower := (-173136627281004084622553714368721947/648742488723705803759873265493404090), upper := (-5123546440705257706547401168144240147807194132638849797897/20800332180654463464461715862948170754425771444512269825920) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi112QChiValue_eq :
    chi112QChiValue =
      (chi112Slice.qChiAD 8 chi112LogChiCertificate).value := by
  norm_num [chi112QChiValue, chi112LogChiCertificate, chi112Slice,
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
private theorem chi112LogChi_valid :
    (if chi112Slice.lo = 0 then
      if chi112Slice.hi = 0 then true
      else decide (chi112Slice.hi ≤ 1 / 4) &&
        chi112LogChiCertificate.check
          (IntervalAD.const chi112Slice.hi).value
    else chi112LogChiCertificate.check
      chi112Slice.chiAD.value) = true := by
  norm_num [chi112Slice, chi112LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi112ValidityFacts :
    ChiFacts chi112Slice chi112LogChiCertificate :=
  { domain := by norm_num [chi112Slice]
    onePlusPositive := by
      norm_num [chi112Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi112LogChi_valid }

noncomputable def chi112InputQChi : RationalEnclosure :=
  { lower := (-2238755/8388608), upper := (-2066285/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi112InputQChi_eq :
    chi112InputQChi = outerEnclosure 24 chi112QChiValue := by
  rfl'

theorem chi112RoundedFacts :
    ChiRoundedFacts 8 chi112Slice chi112LogChiCertificate
      chi112InputQChi :=
  { coversQChi := by
      rw [chi112InputQChi_eq, chi112QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi113Slice : ChiSlice :=
  { lo := (11/64), hi := (23/128) }

noncomputable def chi113LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (11/8) }, upper := { exponent := -3, mantissa := (23/16) } }

private noncomputable def chi113QChiValue : RationalEnclosure :=
  { lower := (-176632699437742640626785099980507/654151237460299686415635906579000), upper := (-71528138122164545556573900892759533913172495790017587/286246286481155978564911939866129916249567316978016000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi113QChiValue_eq :
    chi113QChiValue =
      (chi113Slice.qChiAD 8 chi113LogChiCertificate).value := by
  norm_num [chi113QChiValue, chi113LogChiCertificate, chi113Slice,
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
private theorem chi113LogChi_valid :
    (if chi113Slice.lo = 0 then
      if chi113Slice.hi = 0 then true
      else decide (chi113Slice.hi ≤ 1 / 4) &&
        chi113LogChiCertificate.check
          (IntervalAD.const chi113Slice.hi).value
    else chi113LogChiCertificate.check
      chi113Slice.chiAD.value) = true := by
  norm_num [chi113Slice, chi113LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi113ValidityFacts :
    ChiFacts chi113Slice chi113LogChiCertificate :=
  { domain := by norm_num [chi113Slice]
    onePlusPositive := by
      norm_num [chi113Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi113LogChi_valid }

noncomputable def chi113InputQChi : RationalEnclosure :=
  { lower := (-4530153/16777216), upper := (-524043/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi113InputQChi_eq :
    chi113InputQChi = outerEnclosure 24 chi113QChiValue := by
  rfl'

theorem chi113RoundedFacts :
    ChiRoundedFacts 8 chi113Slice chi113LogChiCertificate
      chi113InputQChi :=
  { coversQChi := by
      rw [chi113InputQChi_eq, chi113QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi114Slice : ChiSlice :=
  { lo := (23/128), hi := (3/16) }

noncomputable def chi114LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (23/16) }, upper := { exponent := -3, mantissa := (3/2) } }

private noncomputable def chi114QChiValue : RationalEnclosure :=
  { lower := (-11649144094000166475743020378/42697926195633105406487342865), upper := (-1468992984583149525958580806355651747107/5804004963062535791003173037109375000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi114QChiValue_eq :
    chi114QChiValue =
      (chi114Slice.qChiAD 8 chi114LogChiCertificate).value := by
  norm_num [chi114QChiValue, chi114LogChiCertificate, chi114Slice,
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
private theorem chi114LogChi_valid :
    (if chi114Slice.lo = 0 then
      if chi114Slice.hi = 0 then true
      else decide (chi114Slice.hi ≤ 1 / 4) &&
        chi114LogChiCertificate.check
          (IntervalAD.const chi114Slice.hi).value
    else chi114LogChiCertificate.check
      chi114Slice.chiAD.value) = true := by
  norm_num [chi114Slice, chi114LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi114ValidityFacts :
    ChiFacts chi114Slice chi114LogChiCertificate :=
  { domain := by norm_num [chi114Slice]
    onePlusPositive := by
      norm_num [chi114Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi114LogChi_valid }

noncomputable def chi114InputQChi : RationalEnclosure :=
  { lower := (-4577277/16777216), upper := (-4246311/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi114InputQChi_eq :
    chi114InputQChi = outerEnclosure 24 chi114QChiValue := by
  rfl'

theorem chi114RoundedFacts :
    ChiRoundedFacts 8 chi114Slice chi114LogChiCertificate
      chi114InputQChi :=
  { coversQChi := by
      rw [chi114InputQChi_eq, chi114QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi115Slice : ChiSlice :=
  { lo := (3/16), hi := (25/128) }

noncomputable def chi115LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (3/2) }, upper := { exponent := -3, mantissa := (25/16) } }

private noncomputable def chi115QChiValue : RationalEnclosure :=
  { lower := (-772375893196035652217/2805323419335937500000), upper := (-39956346639846806245936979921694469697854210733797/156085460566919329279499990309981305406250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi115QChiValue_eq :
    chi115QChiValue =
      (chi115Slice.qChiAD 8 chi115LogChiCertificate).value := by
  norm_num [chi115QChiValue, chi115LogChiCertificate, chi115Slice,
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
private theorem chi115LogChi_valid :
    (if chi115Slice.lo = 0 then
      if chi115Slice.hi = 0 then true
      else decide (chi115Slice.hi ≤ 1 / 4) &&
        chi115LogChiCertificate.check
          (IntervalAD.const chi115Slice.hi).value
    else chi115LogChiCertificate.check
      chi115Slice.chiAD.value) = true := by
  norm_num [chi115Slice, chi115LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi115ValidityFacts :
    ChiFacts chi115Slice chi115LogChiCertificate :=
  { domain := by norm_num [chi115Slice]
    onePlusPositive := by
      norm_num [chi115Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi115LogChi_valid }

noncomputable def chi115InputQChi : RationalEnclosure :=
  { lower := (-4619189/16777216), upper := (-2147401/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi115InputQChi_eq :
    chi115InputQChi = outerEnclosure 24 chi115QChiValue := by
  rfl'

theorem chi115RoundedFacts :
    ChiRoundedFacts 8 chi115Slice chi115LogChiCertificate
      chi115InputQChi :=
  { coversQChi := by
      rw [chi115InputQChi_eq, chi115QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi116Slice : ChiSlice :=
  { lo := (25/128), hi := (13/64) }

noncomputable def chi116LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (25/16) }, upper := { exponent := -3, mantissa := (13/8) } }

private noncomputable def chi116QChiValue : RationalEnclosure :=
  { lower := (-42915985722135064158371367613944031/154635750406855063063281724146111510), upper := (-16545852208097561655649074595753219612942373443153/63989279297256527888931085715779698270948083432832) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi116QChiValue_eq :
    chi116QChiValue =
      (chi116Slice.qChiAD 8 chi116LogChiCertificate).value := by
  norm_num [chi116QChiValue, chi116LogChiCertificate, chi116Slice,
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
private theorem chi116LogChi_valid :
    (if chi116Slice.lo = 0 then
      if chi116Slice.hi = 0 then true
      else decide (chi116Slice.hi ≤ 1 / 4) &&
        chi116LogChiCertificate.check
          (IntervalAD.const chi116Slice.hi).value
    else chi116LogChiCertificate.check
      chi116Slice.chiAD.value) = true := by
  norm_num [chi116Slice, chi116LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi116ValidityFacts :
    ChiFacts chi116Slice chi116LogChiCertificate :=
  { domain := by norm_num [chi116Slice]
    onePlusPositive := by
      norm_num [chi116Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi116LogChi_valid }

noncomputable def chi116InputQChi : RationalEnclosure :=
  { lower := (-4656173/16777216), upper := (-2169061/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi116InputQChi_eq :
    chi116InputQChi = outerEnclosure 24 chi116QChiValue := by
  rfl'

theorem chi116RoundedFacts :
    ChiRoundedFacts 8 chi116Slice chi116LogChiCertificate
      chi116InputQChi :=
  { coversQChi := by
      rw [chi116InputQChi_eq, chi116QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi117Slice : ChiSlice :=
  { lo := (13/64), hi := (27/128) }

noncomputable def chi117LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (13/8) }, upper := { exponent := -3, mantissa := (27/16) } }

private noncomputable def chi117QChiValue : RationalEnclosure :=
  { lower := (-931637544808289956327813/3333754888519470994739160), upper := (-24667597410857101261327200412804257043990810381737917/94561571450196759444288620597475829379229269383407360) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi117QChiValue_eq :
    chi117QChiValue =
      (chi117Slice.qChiAD 8 chi117LogChiCertificate).value := by
  norm_num [chi117QChiValue, chi117LogChiCertificate, chi117Slice,
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
private theorem chi117LogChi_valid :
    (if chi117Slice.lo = 0 then
      if chi117Slice.hi = 0 then true
      else decide (chi117Slice.hi ≤ 1 / 4) &&
        chi117LogChiCertificate.check
          (IntervalAD.const chi117Slice.hi).value
    else chi117LogChiCertificate.check
      chi117Slice.chiAD.value) = true := by
  norm_num [chi117Slice, chi117LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi117ValidityFacts :
    ChiFacts chi117Slice chi117LogChiCertificate :=
  { domain := by norm_num [chi117Slice]
    onePlusPositive := by
      norm_num [chi117Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi117LogChi_valid }

noncomputable def chi117InputQChi : RationalEnclosure :=
  { lower := (-4688493/16777216), upper := (-4376551/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi117InputQChi_eq :
    chi117InputQChi = outerEnclosure 24 chi117QChiValue := by
  rfl'

theorem chi117RoundedFacts :
    ChiRoundedFacts 8 chi117Slice chi117LogChiCertificate
      chi117InputQChi :=
  { coversQChi := by
      rw [chi117InputQChi_eq, chi117QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi118Slice : ChiSlice :=
  { lo := (27/128), hi := (7/32) }

noncomputable def chi118LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (27/16) }, upper := { exponent := -3, mantissa := (7/4) } }

private noncomputable def chi118QChiValue : RationalEnclosure :=
  { lower := (-1420277836391179272714696043804995637/5052233270191308072553420404687160425), upper := (-228884314884161366926351875707472316429586069910761731/870688639995062055917278461187630211451764633356329600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi118QChiValue_eq :
    chi118QChiValue =
      (chi118Slice.qChiAD 8 chi118LogChiCertificate).value := by
  norm_num [chi118QChiValue, chi118LogChiCertificate, chi118Slice,
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
private theorem chi118LogChi_valid :
    (if chi118Slice.lo = 0 then
      if chi118Slice.hi = 0 then true
      else decide (chi118Slice.hi ≤ 1 / 4) &&
        chi118LogChiCertificate.check
          (IntervalAD.const chi118Slice.hi).value
    else chi118LogChiCertificate.check
      chi118Slice.chiAD.value) = true := by
  norm_num [chi118Slice, chi118LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi118ValidityFacts :
    ChiFacts chi118Slice chi118LogChiCertificate :=
  { domain := by norm_num [chi118Slice]
    onePlusPositive := by
      norm_num [chi118Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi118LogChi_valid }

noncomputable def chi118InputQChi : RationalEnclosure :=
  { lower := (-589549/2097152), upper := (-4410349/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi118InputQChi_eq :
    chi118InputQChi = outerEnclosure 24 chi118QChiValue := by
  rfl'

theorem chi118RoundedFacts :
    ChiRoundedFacts 8 chi118Slice chi118LogChiCertificate
      chi118InputQChi :=
  { coversQChi := by
      rw [chi118InputQChi_eq, chi118QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi119Slice : ChiSlice :=
  { lo := (7/32), hi := (29/128) }

noncomputable def chi119LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (7/4) }, upper := { exponent := -3, mantissa := (29/16) } }

private noncomputable def chi119QChiValue : RationalEnclosure :=
  { lower := (-4808086780329010970300384963/17017865406037870200698311440), upper := (-287316790534847458169749056018285271677919588430951/1085729402275911002694208565533584914296875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi119QChiValue_eq :
    chi119QChiValue =
      (chi119Slice.qChiAD 8 chi119LogChiCertificate).value := by
  norm_num [chi119QChiValue, chi119LogChiCertificate, chi119Slice,
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
private theorem chi119LogChi_valid :
    (if chi119Slice.lo = 0 then
      if chi119Slice.hi = 0 then true
      else decide (chi119Slice.hi ≤ 1 / 4) &&
        chi119LogChiCertificate.check
          (IntervalAD.const chi119Slice.hi).value
    else chi119LogChiCertificate.check
      chi119Slice.chiAD.value) = true := by
  norm_num [chi119Slice, chi119LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi119ValidityFacts :
    ChiFacts chi119Slice chi119LogChiCertificate :=
  { domain := by norm_num [chi119Slice]
    onePlusPositive := by
      norm_num [chi119Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi119LogChi_valid }

noncomputable def chi119InputQChi : RationalEnclosure :=
  { lower := (-4629/16384), upper := (-2219879/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi119InputQChi_eq :
    chi119InputQChi = outerEnclosure 24 chi119QChiValue := by
  rfl'

theorem chi119RoundedFacts :
    ChiRoundedFacts 8 chi119Slice chi119LogChiCertificate
      chi119InputQChi :=
  { coversQChi := by
      rw [chi119InputQChi_eq, chi119QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi120Slice : ChiSlice :=
  { lo := (29/128), hi := (15/64) }

noncomputable def chi120LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (29/16) }, upper := { exponent := -3, mantissa := (15/8) } }

private noncomputable def chi120QChiValue : RationalEnclosure :=
  { lower := (-560301557520621768924314981819/1974928750402755913879394531250), upper := (-28342463768616593470824069769447987669522091529820343/106496670204758395955786832889083143514535781250000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi120QChiValue_eq :
    chi120QChiValue =
      (chi120Slice.qChiAD 8 chi120LogChiCertificate).value := by
  norm_num [chi120QChiValue, chi120LogChiCertificate, chi120Slice,
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
private theorem chi120LogChi_valid :
    (if chi120Slice.lo = 0 then
      if chi120Slice.hi = 0 then true
      else decide (chi120Slice.hi ≤ 1 / 4) &&
        chi120LogChiCertificate.check
          (IntervalAD.const chi120Slice.hi).value
    else chi120LogChiCertificate.check
      chi120Slice.chiAD.value) = true := by
  norm_num [chi120Slice, chi120LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi120ValidityFacts :
    ChiFacts chi120Slice chi120LogChiCertificate :=
  { domain := by norm_num [chi120Slice]
    onePlusPositive := by
      norm_num [chi120Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi120LogChi_valid }

noncomputable def chi120InputQChi : RationalEnclosure :=
  { lower := (-2379909/8388608), upper := (-558125/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi120InputQChi_eq :
    chi120InputQChi = outerEnclosure 24 chi120QChiValue := by
  rfl'

theorem chi120RoundedFacts :
    ChiRoundedFacts 8 chi120Slice chi120LogChiCertificate
      chi120InputQChi :=
  { coversQChi := by
      rw [chi120InputQChi_eq, chi120QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi121Slice : ChiSlice :=
  { lo := (15/64), hi := (31/128) }

noncomputable def chi121LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (15/8) }, upper := { exponent := -3, mantissa := (31/16) } }

private noncomputable def chi121QChiValue : RationalEnclosure :=
  { lower := (-3444923109176889161612907368733359/12102010381722480891331304539734840), upper := (-13532863871118342989021406001529313496919902029128795688025711/50608421305968313767976381622764226778711108244503866838888192) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi121QChiValue_eq :
    chi121QChiValue =
      (chi121Slice.qChiAD 8 chi121LogChiCertificate).value := by
  norm_num [chi121QChiValue, chi121LogChiCertificate, chi121Slice,
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
private theorem chi121LogChi_valid :
    (if chi121Slice.lo = 0 then
      if chi121Slice.hi = 0 then true
      else decide (chi121Slice.hi ≤ 1 / 4) &&
        chi121LogChiCertificate.check
          (IntervalAD.const chi121Slice.hi).value
    else chi121LogChiCertificate.check
      chi121Slice.chiAD.value) = true := by
  norm_num [chi121Slice, chi121LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi121ValidityFacts :
    ChiFacts chi121Slice chi121LogChiCertificate :=
  { domain := by norm_num [chi121Slice]
    onePlusPositive := by
      norm_num [chi121Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi121LogChi_valid }

noncomputable def chi121InputQChi : RationalEnclosure :=
  { lower := (-2387877/8388608), upper := (-1121571/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi121InputQChi_eq :
    chi121InputQChi = outerEnclosure 24 chi121QChiValue := by
  rfl'

theorem chi121RoundedFacts :
    ChiRoundedFacts 8 chi121Slice chi121LogChiCertificate
      chi121InputQChi :=
  { coversQChi := by
      rw [chi121InputQChi_eq, chi121QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi122Slice : ChiSlice :=
  { lo := (31/128), hi := (1/4) }

noncomputable def chi122LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (31/16) }, upper := { exponent := -2, mantissa := (1) } }

private noncomputable def chi122QChiValue : RationalEnclosure :=
  { lower := (-39312456638179524563893207805008943176/137748822769204893108511452466843475295), upper := (-18932924007022155676288907752998622261429/70527397257832905271557863663023859351040) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi122QChiValue_eq :
    chi122QChiValue =
      (chi122Slice.qChiAD 8 chi122LogChiCertificate).value := by
  norm_num [chi122QChiValue, chi122LogChiCertificate, chi122Slice,
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
private theorem chi122LogChi_valid :
    (if chi122Slice.lo = 0 then
      if chi122Slice.hi = 0 then true
      else decide (chi122Slice.hi ≤ 1 / 4) &&
        chi122LogChiCertificate.check
          (IntervalAD.const chi122Slice.hi).value
    else chi122LogChiCertificate.check
      chi122Slice.chiAD.value) = true := by
  norm_num [chi122Slice, chi122LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi122ValidityFacts :
    ChiFacts chi122Slice chi122LogChiCertificate :=
  { domain := by norm_num [chi122Slice]
    onePlusPositive := by
      norm_num [chi122Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi122LogChi_valid }

noncomputable def chi122InputQChi : RationalEnclosure :=
  { lower := (-4788089/16777216), upper := (-2251903/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi122InputQChi_eq :
    chi122InputQChi = outerEnclosure 24 chi122QChiValue := by
  rfl'

theorem chi122RoundedFacts :
    ChiRoundedFacts 8 chi122Slice chi122LogChiCertificate
      chi122InputQChi :=
  { coversQChi := by
      rw [chi122InputQChi_eq, chi122QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi123Slice : ChiSlice :=
  { lo := (3/128), hi := (7/256) }

noncomputable def chi123LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -6, mantissa := (3/2) }, upper := { exponent := -6, mantissa := (7/4) } }

private noncomputable def chi123QChiValue : RationalEnclosure :=
  { lower := (-16452424413691806469499/164061324970092773437500), upper := (-21441400979134432576330714998830563920353/262167913677161468181527463603515625000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi123QChiValue_eq :
    chi123QChiValue =
      (chi123Slice.qChiAD 8 chi123LogChiCertificate).value := by
  norm_num [chi123QChiValue, chi123LogChiCertificate, chi123Slice,
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
private theorem chi123LogChi_valid :
    (if chi123Slice.lo = 0 then
      if chi123Slice.hi = 0 then true
      else decide (chi123Slice.hi ≤ 1 / 4) &&
        chi123LogChiCertificate.check
          (IntervalAD.const chi123Slice.hi).value
    else chi123LogChiCertificate.check
      chi123Slice.chiAD.value) = true := by
  norm_num [chi123Slice, chi123LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi123ValidityFacts :
    ChiFacts chi123Slice chi123LogChiCertificate :=
  { domain := by norm_num [chi123Slice]
    onePlusPositive := by
      norm_num [chi123Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi123LogChi_valid }

noncomputable def chi123InputQChi : RationalEnclosure :=
  { lower := (-210307/2097152), upper := (-343031/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi123InputQChi_eq :
    chi123InputQChi = outerEnclosure 24 chi123QChiValue := by
  rfl'

theorem chi123RoundedFacts :
    ChiRoundedFacts 8 chi123Slice chi123LogChiCertificate
      chi123InputQChi :=
  { coversQChi := by
      rw [chi123InputQChi_eq, chi123QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi124Slice : ChiSlice :=
  { lo := (7/256), hi := (1/32) }

noncomputable def chi124LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -6, mantissa := (7/4) }, upper := { exponent := -5, mantissa := (1) } }

private noncomputable def chi124QChiValue : RationalEnclosure :=
  { lower := (-785280103463282622761173372/7172593913121730549332781905), upper := (-1387732747609376207275399300351/15148518344513094920190835383360) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi124QChiValue_eq :
    chi124QChiValue =
      (chi124Slice.qChiAD 8 chi124LogChiCertificate).value := by
  norm_num [chi124QChiValue, chi124LogChiCertificate, chi124Slice,
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
private theorem chi124LogChi_valid :
    (if chi124Slice.lo = 0 then
      if chi124Slice.hi = 0 then true
      else decide (chi124Slice.hi ≤ 1 / 4) &&
        chi124LogChiCertificate.check
          (IntervalAD.const chi124Slice.hi).value
    else chi124LogChiCertificate.check
      chi124Slice.chiAD.value) = true := by
  norm_num [chi124Slice, chi124LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi124ValidityFacts :
    ChiFacts chi124Slice chi124LogChiCertificate :=
  { domain := by norm_num [chi124Slice]
    onePlusPositive := by
      norm_num [chi124Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi124LogChi_valid }

noncomputable def chi124InputQChi : RationalEnclosure :=
  { lower := (-1836827/16777216), upper := (-1536935/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi124InputQChi_eq :
    chi124InputQChi = outerEnclosure 24 chi124QChiValue := by
  rfl'

theorem chi124RoundedFacts :
    ChiRoundedFacts 8 chi124Slice chi124LogChiCertificate
      chi124InputQChi :=
  { coversQChi := by
      rw [chi124InputQChi_eq, chi124QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi125Slice : ChiSlice :=
  { lo := (1/16), hi := (9/128) }

noncomputable def chi125LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (1) }, upper := { exponent := -4, mantissa := (9/8) } }

private noncomputable def chi125QChiValue : RationalEnclosure :=
  { lower := (-597351034279/3255671338920), upper := (-2227711295320691072360966397678313/14419402055684074990460446918110720) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi125QChiValue_eq :
    chi125QChiValue =
      (chi125Slice.qChiAD 8 chi125LogChiCertificate).value := by
  norm_num [chi125QChiValue, chi125LogChiCertificate, chi125Slice,
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
private theorem chi125LogChi_valid :
    (if chi125Slice.lo = 0 then
      if chi125Slice.hi = 0 then true
      else decide (chi125Slice.hi ≤ 1 / 4) &&
        chi125LogChiCertificate.check
          (IntervalAD.const chi125Slice.hi).value
    else chi125LogChiCertificate.check
      chi125Slice.chiAD.value) = true := by
  norm_num [chi125Slice, chi125LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi125ValidityFacts :
    ChiFacts chi125Slice chi125LogChiCertificate :=
  { domain := by norm_num [chi125Slice]
    onePlusPositive := by
      norm_num [chi125Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi125LogChi_valid }

noncomputable def chi125InputQChi : RationalEnclosure :=
  { lower := (-1539143/8388608), upper := (-2591979/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi125InputQChi_eq :
    chi125InputQChi = outerEnclosure 24 chi125QChiValue := by
  rfl'

theorem chi125RoundedFacts :
    ChiRoundedFacts 8 chi125Slice chi125LogChiCertificate
      chi125InputQChi :=
  { coversQChi := by
      rw [chi125InputQChi_eq, chi125QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi126Slice : ChiSlice :=
  { lo := (9/128), hi := (5/64) }

noncomputable def chi126LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (9/8) }, upper := { exponent := -4, mantissa := (5/4) } }

private noncomputable def chi126QChiValue : RationalEnclosure :=
  { lower := (-251882138202221406987114119590/1299825906461905798418910479397), upper := (-177514599473416656553610822891909392787105/1070721260804306499444064197033157968887232) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi126QChiValue_eq :
    chi126QChiValue =
      (chi126Slice.qChiAD 8 chi126LogChiCertificate).value := by
  norm_num [chi126QChiValue, chi126LogChiCertificate, chi126Slice,
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
private theorem chi126LogChi_valid :
    (if chi126Slice.lo = 0 then
      if chi126Slice.hi = 0 then true
      else decide (chi126Slice.hi ≤ 1 / 4) &&
        chi126LogChiCertificate.check
          (IntervalAD.const chi126Slice.hi).value
    else chi126LogChiCertificate.check
      chi126Slice.chiAD.value) = true := by
  norm_num [chi126Slice, chi126LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi126ValidityFacts :
    ChiFacts chi126Slice chi126LogChiCertificate :=
  { domain := by norm_num [chi126Slice]
    onePlusPositive := by
      norm_num [chi126Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi126LogChi_valid }

noncomputable def chi126InputQChi : RationalEnclosure :=
  { lower := (-1625557/8388608), upper := (-1390745/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi126InputQChi_eq :
    chi126InputQChi = outerEnclosure 24 chi126QChiValue := by
  rfl'

theorem chi126RoundedFacts :
    ChiRoundedFacts 8 chi126Slice chi126LogChiCertificate
      chi126InputQChi :=
  { coversQChi := by
      rw [chi126InputQChi_eq, chi126QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi127Slice : ChiSlice :=
  { lo := (5/64), hi := (21/256) }

noncomputable def chi127LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (5/4) }, upper := { exponent := -4, mantissa := (21/16) } }

private noncomputable def chi127QChiValue : RationalEnclosure :=
  { lower := (-143299929310029851/738737381955600612), upper := (-260031442648060706336833009576020011758101442247/1441085073619622233022739028265679541966388451840) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi127QChiValue_eq :
    chi127QChiValue =
      (chi127Slice.qChiAD 8 chi127LogChiCertificate).value := by
  norm_num [chi127QChiValue, chi127LogChiCertificate, chi127Slice,
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
private theorem chi127LogChi_valid :
    (if chi127Slice.lo = 0 then
      if chi127Slice.hi = 0 then true
      else decide (chi127Slice.hi ≤ 1 / 4) &&
        chi127LogChiCertificate.check
          (IntervalAD.const chi127Slice.hi).value
    else chi127LogChiCertificate.check
      chi127Slice.chiAD.value) = true := by
  norm_num [chi127Slice, chi127LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi127ValidityFacts :
    ChiFacts chi127Slice chi127LogChiCertificate :=
  { domain := by norm_num [chi127Slice]
    onePlusPositive := by
      norm_num [chi127Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi127LogChi_valid }

noncomputable def chi127InputQChi : RationalEnclosure :=
  { lower := (-3254437/16777216), upper := (-378413/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi127InputQChi_eq :
    chi127InputQChi = outerEnclosure 24 chi127QChiValue := by
  rfl'

theorem chi127RoundedFacts :
    ChiRoundedFacts 8 chi127Slice chi127LogChiCertificate
      chi127InputQChi :=
  { coversQChi := by
      rw [chi127InputQChi_eq, chi127QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
