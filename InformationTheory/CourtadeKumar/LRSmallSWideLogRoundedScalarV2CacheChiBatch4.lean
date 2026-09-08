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

noncomputable def chi256Slice : ChiSlice :=
  { lo := (47/128), hi := (3/8) }

noncomputable def chi256LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (47/32) }, upper := { exponent := -2, mantissa := (3/2) } }

private noncomputable def chi256QChiValue : RationalEnclosure :=
  { lower := (-100620711671305591791783125598015137597768/366156982702673984869665923804860417431375), upper := (-1647803979369376486593995864686832056946057717907485543/6293323140202209114947383065396038424601757812500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi256QChiValue_eq :
    chi256QChiValue =
      (chi256Slice.qChiAD 8 chi256LogChiCertificate).value := by
  norm_num [chi256QChiValue, chi256LogChiCertificate, chi256Slice,
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
private theorem chi256LogChi_valid :
    (if chi256Slice.lo = 0 then
      if chi256Slice.hi = 0 then true
      else decide (chi256Slice.hi ≤ 1 / 4) &&
        chi256LogChiCertificate.check
          (IntervalAD.const chi256Slice.hi).value
    else chi256LogChiCertificate.check
      chi256Slice.chiAD.value) = true := by
  norm_num [chi256Slice, chi256LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi256ValidityFacts :
    ChiFacts chi256Slice chi256LogChiCertificate :=
  { domain := by norm_num [chi256Slice]
    onePlusPositive := by
      norm_num [chi256Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi256LogChi_valid }

noncomputable def chi256InputQChi : RationalEnclosure :=
  { lower := (-4610415/16777216), upper := (-549105/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi256InputQChi_eq :
    chi256InputQChi = outerEnclosure 24 chi256QChiValue := by
  rfl'

theorem chi256RoundedFacts :
    ChiRoundedFacts 8 chi256Slice chi256LogChiCertificate
      chi256InputQChi :=
  { coversQChi := by
      rw [chi256InputQChi_eq, chi256QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi257Slice : ChiSlice :=
  { lo := (17/64), hi := (69/256) }

noncomputable def chi257LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (17/16) }, upper := { exponent := -2, mantissa := (69/64) } }

private noncomputable def chi257QChiValue : RationalEnclosure :=
  { lower := (-79194384060211615989171767/280514264934690168143378760), upper := (-40930320928097691639627112294021753258315229804490902177545958173/149226671514859550681493479842639424462928435068005388797615872000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi257QChiValue_eq :
    chi257QChiValue =
      (chi257Slice.qChiAD 8 chi257LogChiCertificate).value := by
  norm_num [chi257QChiValue, chi257LogChiCertificate, chi257Slice,
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
private theorem chi257LogChi_valid :
    (if chi257Slice.lo = 0 then
      if chi257Slice.hi = 0 then true
      else decide (chi257Slice.hi ≤ 1 / 4) &&
        chi257LogChiCertificate.check
          (IntervalAD.const chi257Slice.hi).value
    else chi257LogChiCertificate.check
      chi257Slice.chiAD.value) = true := by
  norm_num [chi257Slice, chi257LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi257ValidityFacts :
    ChiFacts chi257Slice chi257LogChiCertificate :=
  { domain := by norm_num [chi257Slice]
    onePlusPositive := by
      norm_num [chi257Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi257LogChi_valid }

noncomputable def chi257InputQChi : RationalEnclosure :=
  { lower := (-592065/2097152), upper := (-4601703/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi257InputQChi_eq :
    chi257InputQChi = outerEnclosure 24 chi257QChiValue := by
  rfl'

theorem chi257RoundedFacts :
    ChiRoundedFacts 8 chi257Slice chi257LogChiCertificate
      chi257InputQChi :=
  { coversQChi := by
      rw [chi257InputQChi_eq, chi257QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi258Slice : ChiSlice :=
  { lo := (69/256), hi := (35/128) }

noncomputable def chi258LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (69/64) }, upper := { exponent := -2, mantissa := (35/32) } }

private noncomputable def chi258QChiValue : RationalEnclosure :=
  { lower := (-5816703539609594854754875460744148316917229/20598521467563943984100599761018073499487225), upper := (-5804950425971399146051179583541574049215414704037280091754685957436799618767/21153666768654309229464488747292610930460840309721893235525414158300057664000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi258QChiValue_eq :
    chi258QChiValue =
      (chi258Slice.qChiAD 8 chi258LogChiCertificate).value := by
  norm_num [chi258QChiValue, chi258LogChiCertificate, chi258Slice,
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
private theorem chi258LogChi_valid :
    (if chi258Slice.lo = 0 then
      if chi258Slice.hi = 0 then true
      else decide (chi258Slice.hi ≤ 1 / 4) &&
        chi258LogChiCertificate.check
          (IntervalAD.const chi258Slice.hi).value
    else chi258LogChiCertificate.check
      chi258Slice.chiAD.value) = true := by
  norm_num [chi258Slice, chi258LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi258ValidityFacts :
    ChiFacts chi258Slice chi258LogChiCertificate :=
  { domain := by norm_num [chi258Slice]
    onePlusPositive := by
      norm_num [chi258Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi258LogChi_valid }

noncomputable def chi258InputQChi : RationalEnclosure :=
  { lower := (-4737627/16777216), upper := (-1150993/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi258InputQChi_eq :
    chi258InputQChi = outerEnclosure 24 chi258QChiValue := by
  rfl'

theorem chi258RoundedFacts :
    ChiRoundedFacts 8 chi258Slice chi258LogChiCertificate
      chi258InputQChi :=
  { coversQChi := by
      rw [chi258InputQChi_eq, chi258QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi259Slice : ChiSlice :=
  { lo := (3/8), hi := (49/128) }

noncomputable def chi259LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -2, mantissa := (49/32) } }

private noncomputable def chi259QChiValue : RationalEnclosure :=
  { lower := (-90285016694302838203229/330627402993164062500000), upper := (-282266024275082338092715343209247041937426259331171/1084362834804477298751278404237235179375000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi259QChiValue_eq :
    chi259QChiValue =
      (chi259Slice.qChiAD 8 chi259LogChiCertificate).value := by
  norm_num [chi259QChiValue, chi259LogChiCertificate, chi259Slice,
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
private theorem chi259LogChi_valid :
    (if chi259Slice.lo = 0 then
      if chi259Slice.hi = 0 then true
      else decide (chi259Slice.hi ≤ 1 / 4) &&
        chi259LogChiCertificate.check
          (IntervalAD.const chi259Slice.hi).value
    else chi259LogChiCertificate.check
      chi259Slice.chiAD.value) = true := by
  norm_num [chi259Slice, chi259LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi259ValidityFacts :
    ChiFacts chi259Slice chi259LogChiCertificate :=
  { domain := by norm_num [chi259Slice]
    onePlusPositive := by
      norm_num [chi259Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi259LogChi_valid }

noncomputable def chi259InputQChi : RationalEnclosure :=
  { lower := (-4581385/16777216), upper := (-545901/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi259InputQChi_eq :
    chi259InputQChi = outerEnclosure 24 chi259QChiValue := by
  rfl'

theorem chi259RoundedFacts :
    ChiRoundedFacts 8 chi259Slice chi259LogChiCertificate
      chi259InputQChi :=
  { coversQChi := by
      rw [chi259InputQChi_eq, chi259QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi260Slice : ChiSlice :=
  { lo := (49/128), hi := (25/64) }

noncomputable def chi260LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (49/32) }, upper := { exponent := -2, mantissa := (25/16) } }

private noncomputable def chi260QChiValue : RationalEnclosure :=
  { lower := (-6111767766521323686266067402610105/22532214749183943870156434373760731), upper := (-1032574777651978665794940960320724290674135792168158098869463377/3991735062865952246313032712578677317948175917968080473769547520) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi260QChiValue_eq :
    chi260QChiValue =
      (chi260Slice.qChiAD 8 chi260LogChiCertificate).value := by
  norm_num [chi260QChiValue, chi260LogChiCertificate, chi260Slice,
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
private theorem chi260LogChi_valid :
    (if chi260Slice.lo = 0 then
      if chi260Slice.hi = 0 then true
      else decide (chi260Slice.hi ≤ 1 / 4) &&
        chi260LogChiCertificate.check
          (IntervalAD.const chi260Slice.hi).value
    else chi260LogChiCertificate.check
      chi260Slice.chiAD.value) = true := by
  norm_num [chi260Slice, chi260LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi260ValidityFacts :
    ChiFacts chi260Slice chi260LogChiCertificate :=
  { domain := by norm_num [chi260Slice]
    onePlusPositive := by
      norm_num [chi260Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi260LogChi_valid }

noncomputable def chi260InputQChi : RationalEnclosure :=
  { lower := (-4550749/16777216), upper := (-4339899/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi260InputQChi_eq :
    chi260InputQChi = outerEnclosure 24 chi260QChiValue := by
  rfl'

theorem chi260RoundedFacts :
    ChiRoundedFacts 8 chi260Slice chi260LogChiCertificate
      chi260InputQChi :=
  { coversQChi := by
      rw [chi260InputQChi_eq, chi260QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi261Slice : ChiSlice :=
  { lo := (25/64), hi := (51/128) }

noncomputable def chi261LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (25/16) }, upper := { exponent := -2, mantissa := (51/32) } }

private noncomputable def chi261QChiValue : RationalEnclosure :=
  { lower := (-973463029289716840357796140234839197/3614415418600632484125595047213151860), upper := (-14306111388913254312319699224940493907927650645429208640035063192091649/55675629696962355791098343540291308055078726770276181849040528883760640) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi261QChiValue_eq :
    chi261QChiValue =
      (chi261Slice.qChiAD 8 chi261LogChiCertificate).value := by
  norm_num [chi261QChiValue, chi261LogChiCertificate, chi261Slice,
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
private theorem chi261LogChi_valid :
    (if chi261Slice.lo = 0 then
      if chi261Slice.hi = 0 then true
      else decide (chi261Slice.hi ≤ 1 / 4) &&
        chi261LogChiCertificate.check
          (IntervalAD.const chi261Slice.hi).value
    else chi261LogChiCertificate.check
      chi261Slice.chiAD.value) = true := by
  norm_num [chi261Slice, chi261LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi261ValidityFacts :
    ChiFacts chi261Slice chi261LogChiCertificate :=
  { domain := by norm_num [chi261Slice]
    onePlusPositive := by
      norm_num [chi261Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi261LogChi_valid }

noncomputable def chi261InputQChi : RationalEnclosure :=
  { lower := (-4518573/16777216), upper := (-4310983/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi261InputQChi_eq :
    chi261InputQChi = outerEnclosure 24 chi261QChiValue := by
  rfl'

theorem chi261RoundedFacts :
    ChiRoundedFacts 8 chi261Slice chi261LogChiCertificate
      chi261InputQChi :=
  { coversQChi := by
      rw [chi261InputQChi_eq, chi261QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi262Slice : ChiSlice :=
  { lo := (51/128), hi := (13/32) }

noncomputable def chi262LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (51/32) }, upper := { exponent := -2, mantissa := (13/8) } }

private noncomputable def chi262QChiValue : RationalEnclosure :=
  { lower := (-48468542969769681619774164622955681220154/181311446054869983974835555821303776649505), upper := (-134246389726192419262609786058737151741239168352719642279/526169377355537020296515213083601902752759896002208920320) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi262QChiValue_eq :
    chi262QChiValue =
      (chi262Slice.qChiAD 8 chi262LogChiCertificate).value := by
  norm_num [chi262QChiValue, chi262LogChiCertificate, chi262Slice,
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
private theorem chi262LogChi_valid :
    (if chi262Slice.lo = 0 then
      if chi262Slice.hi = 0 then true
      else decide (chi262Slice.hi ≤ 1 / 4) &&
        chi262LogChiCertificate.check
          (IntervalAD.const chi262Slice.hi).value
    else chi262LogChiCertificate.check
      chi262Slice.chiAD.value) = true := by
  norm_num [chi262Slice, chi262LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi262ValidityFacts :
    ChiFacts chi262Slice chi262LogChiCertificate :=
  { domain := by norm_num [chi262Slice]
    onePlusPositive := by
      norm_num [chi262Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi262LogChi_valid }

noncomputable def chi262InputQChi : RationalEnclosure :=
  { lower := (-560615/2097152), upper := (-1070131/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi262InputQChi_eq :
    chi262InputQChi = outerEnclosure 24 chi262QChiValue := by
  rfl'

theorem chi262RoundedFacts :
    ChiRoundedFacts 8 chi262Slice chi262LogChiCertificate
      chi262InputQChi :=
  { coversQChi := by
      rw [chi262InputQChi_eq, chi262QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi263Slice : ChiSlice :=
  { lo := (13/32), hi := (53/128) }

noncomputable def chi263LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (13/8) }, upper := { exponent := -2, mantissa := (53/32) } }

private noncomputable def chi263QChiValue : RationalEnclosure :=
  { lower := (-1550250856156282604792107/5844894934417254341425800), upper := (-7327522444102509948744742733288045510950150339255933940197/28935627621591338078257915746419777808296867343750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi263QChiValue_eq :
    chi263QChiValue =
      (chi263Slice.qChiAD 8 chi263LogChiCertificate).value := by
  norm_num [chi263QChiValue, chi263LogChiCertificate, chi263Slice,
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
private theorem chi263LogChi_valid :
    (if chi263Slice.lo = 0 then
      if chi263Slice.hi = 0 then true
      else decide (chi263Slice.hi ≤ 1 / 4) &&
        chi263LogChiCertificate.check
          (IntervalAD.const chi263Slice.hi).value
    else chi263LogChiCertificate.check
      chi263Slice.chiAD.value) = true := by
  norm_num [chi263Slice, chi263LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi263ValidityFacts :
    ChiFacts chi263Slice chi263LogChiCertificate :=
  { domain := by norm_num [chi263Slice]
    onePlusPositive := by
      norm_num [chi263Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi263LogChi_valid }

noncomputable def chi263InputQChi : RationalEnclosure :=
  { lower := (-556231/2097152), upper := (-4248583/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi263InputQChi_eq :
    chi263InputQChi = outerEnclosure 24 chi263QChiValue := by
  rfl'

theorem chi263RoundedFacts :
    ChiRoundedFacts 8 chi263Slice chi263LogChiCertificate
      chi263InputQChi :=
  { coversQChi := by
      rw [chi263InputQChi_eq, chi263QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi264Slice : ChiSlice :=
  { lo := (53/128), hi := (27/64) }

noncomputable def chi264LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (53/32) }, upper := { exponent := -2, mantissa := (27/16) } }

private noncomputable def chi264QChiValue : RationalEnclosure :=
  { lower := (-33189276505291265019573532561123198742347/126166150908246700359248423333587646484375), upper := (-21115140449061503282100281915971492936286651447402055849213019754178277/84041453419273477429496469060236187556204523214573991517460937500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi264QChiValue_eq :
    chi264QChiValue =
      (chi264Slice.qChiAD 8 chi264LogChiCertificate).value := by
  norm_num [chi264QChiValue, chi264LogChiCertificate, chi264Slice,
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
private theorem chi264LogChi_valid :
    (if chi264Slice.lo = 0 then
      if chi264Slice.hi = 0 then true
      else decide (chi264Slice.hi ≤ 1 / 4) &&
        chi264LogChiCertificate.check
          (IntervalAD.const chi264Slice.hi).value
    else chi264LogChiCertificate.check
      chi264Slice.chiAD.value) = true := by
  norm_num [chi264Slice, chi264LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi264ValidityFacts :
    ChiFacts chi264Slice chi264LogChiCertificate :=
  { domain := by norm_num [chi264Slice]
    onePlusPositive := by
      norm_num [chi264Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi264LogChi_valid }

noncomputable def chi264InputQChi : RationalEnclosure :=
  { lower := (-551677/2097152), upper := (-1053805/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi264InputQChi_eq :
    chi264InputQChi = outerEnclosure 24 chi264QChiValue := by
  rfl'

theorem chi264RoundedFacts :
    ChiRoundedFacts 8 chi264Slice chi264LogChiCertificate
      chi264InputQChi :=
  { coversQChi := by
      rw [chi264InputQChi_eq, chi264QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi265Slice : ChiSlice :=
  { lo := (27/64), hi := (55/128) }

noncomputable def chi265LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (27/16) }, upper := { exponent := -2, mantissa := (55/32) } }

private noncomputable def chi265QChiValue : RationalEnclosure :=
  { lower := (-1181503620093484068177896397948728629/4530119779160394006639102120050282028), upper := (-836603540353347851504851639211490059043616593431629248881496077/3357470020664001085888045769818165368736456921497125565213159936) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi265QChiValue_eq :
    chi265QChiValue =
      (chi265Slice.qChiAD 8 chi265LogChiCertificate).value := by
  norm_num [chi265QChiValue, chi265LogChiCertificate, chi265Slice,
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
private theorem chi265LogChi_valid :
    (if chi265Slice.lo = 0 then
      if chi265Slice.hi = 0 then true
      else decide (chi265Slice.hi ≤ 1 / 4) &&
        chi265LogChiCertificate.check
          (IntervalAD.const chi265Slice.hi).value
    else chi265LogChiCertificate.check
      chi265Slice.chiAD.value) = true := by
  norm_num [chi265Slice, chi265LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi265ValidityFacts :
    ChiFacts chi265Slice chi265LogChiCertificate :=
  { domain := by norm_num [chi265Slice]
    onePlusPositive := by
      norm_num [chi265Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi265LogChi_valid }

noncomputable def chi265InputQChi : RationalEnclosure :=
  { lower := (-2187839/8388608), upper := (-1045123/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi265InputQChi_eq :
    chi265InputQChi = outerEnclosure 24 chi265QChiValue := by
  rfl'

theorem chi265RoundedFacts :
    ChiRoundedFacts 8 chi265Slice chi265LogChiCertificate
      chi265InputQChi :=
  { coversQChi := by
      rw [chi265InputQChi_eq, chi265QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi266Slice : ChiSlice :=
  { lo := (55/128), hi := (7/16) }

noncomputable def chi266LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (55/32) }, upper := { exponent := -2, mantissa := (7/4) } }

private noncomputable def chi266QChiValue : RationalEnclosure :=
  { lower := (-12563340252258545481813454094219596/48603458708646498249236416498373505), upper := (-187922134517916929966318242166535521522316562927435693/760730115160250303878756921941388158601908929326721280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi266QChiValue_eq :
    chi266QChiValue =
      (chi266Slice.qChiAD 8 chi266LogChiCertificate).value := by
  norm_num [chi266QChiValue, chi266LogChiCertificate, chi266Slice,
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
private theorem chi266LogChi_valid :
    (if chi266Slice.lo = 0 then
      if chi266Slice.hi = 0 then true
      else decide (chi266Slice.hi ≤ 1 / 4) &&
        chi266LogChiCertificate.check
          (IntervalAD.const chi266Slice.hi).value
    else chi266LogChiCertificate.check
      chi266Slice.chiAD.value) = true := by
  norm_num [chi266Slice, chi266LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi266ValidityFacts :
    ChiFacts chi266Slice chi266LogChiCertificate :=
  { domain := by norm_num [chi266Slice]
    onePlusPositive := by
      norm_num [chi266Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi266LogChi_valid }

noncomputable def chi266InputQChi : RationalEnclosure :=
  { lower := (-4336685/16777216), upper := (-4144453/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi266InputQChi_eq :
    chi266InputQChi = outerEnclosure 24 chi266QChiValue := by
  rfl'

theorem chi266RoundedFacts :
    ChiRoundedFacts 8 chi266Slice chi266LogChiCertificate
      chi266InputQChi :=
  { coversQChi := by
      rw [chi266InputQChi_eq, chi266QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi267Slice : ChiSlice :=
  { lo := (7/16), hi := (57/128) }

noncomputable def chi267LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (7/4) }, upper := { exponent := -2, mantissa := (57/32) } }

private noncomputable def chi267QChiValue : RationalEnclosure :=
  { lower := (-197705473210703542668602113/772013618025386616599726160), upper := (-38495042735563761877736499552425994645539155345163108537137151/157247484901684584660261573430919509596092967036911780765153280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi267QChiValue_eq :
    chi267QChiValue =
      (chi267Slice.qChiAD 8 chi267LogChiCertificate).value := by
  norm_num [chi267QChiValue, chi267LogChiCertificate, chi267Slice,
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
private theorem chi267LogChi_valid :
    (if chi267Slice.lo = 0 then
      if chi267Slice.hi = 0 then true
      else decide (chi267Slice.hi ≤ 1 / 4) &&
        chi267LogChiCertificate.check
          (IntervalAD.const chi267Slice.hi).value
    else chi267LogChiCertificate.check
      chi267Slice.chiAD.value) = true := by
  norm_num [chi267Slice, chi267LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi267ValidityFacts :
    ChiFacts chi267Slice chi267LogChiCertificate :=
  { domain := by norm_num [chi267Slice]
    onePlusPositive := by
      norm_num [chi267Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi267LogChi_valid }

noncomputable def chi267InputQChi : RationalEnclosure :=
  { lower := (-4296489/16777216), upper := (-2053577/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi267InputQChi_eq :
    chi267InputQChi = outerEnclosure 24 chi267QChiValue := by
  rfl'

theorem chi267RoundedFacts :
    ChiRoundedFacts 8 chi267Slice chi267LogChiCertificate
      chi267InputQChi :=
  { coversQChi := by
      rw [chi267InputQChi_eq, chi267QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi268Slice : ChiSlice :=
  { lo := (57/128), hi := (29/64) }

noncomputable def chi268LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (57/32) }, upper := { exponent := -2, mantissa := (29/16) } }

private noncomputable def chi268QChiValue : RationalEnclosure :=
  { lower := (-1760189857450743968075311776120953925756259/6940104109323095923724548165310595458369325), upper := (-101769045519407198116437671127893697561119204243649197280105714721/419648600076845849011316105070539352898784393690248710937500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi268QChiValue_eq :
    chi268QChiValue =
      (chi268Slice.qChiAD 8 chi268LogChiCertificate).value := by
  norm_num [chi268QChiValue, chi268LogChiCertificate, chi268Slice,
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
private theorem chi268LogChi_valid :
    (if chi268Slice.lo = 0 then
      if chi268Slice.hi = 0 then true
      else decide (chi268Slice.hi ≤ 1 / 4) &&
        chi268LogChiCertificate.check
          (IntervalAD.const chi268Slice.hi).value
    else chi268LogChiCertificate.check
      chi268Slice.chiAD.value) = true := by
  norm_num [chi268Slice, chi268LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi268ValidityFacts :
    ChiFacts chi268Slice chi268LogChiCertificate :=
  { domain := by norm_num [chi268Slice]
    onePlusPositive := by
      norm_num [chi268Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi268LogChi_valid }

noncomputable def chi268InputQChi : RationalEnclosure :=
  { lower := (-132973/524288), upper := (-4068645/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi268InputQChi_eq :
    chi268InputQChi = outerEnclosure 24 chi268QChiValue := by
  rfl'

theorem chi268RoundedFacts :
    ChiRoundedFacts 8 chi268Slice chi268LogChiCertificate
      chi268InputQChi :=
  { coversQChi := by
      rw [chi268InputQChi_eq, chi268QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi269Slice : ChiSlice :=
  { lo := (29/64), hi := (59/128) }

noncomputable def chi269LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (29/16) }, upper := { exponent := -2, mantissa := (59/32) } }

private noncomputable def chi269QChiValue : RationalEnclosure :=
  { lower := (-8812393081316230975274738252723/35095867602698656049194335937500), upper := (-349278806522547068141417915841865420922170200967112897621836879/1454446232588820329986819637343398589283905761566640625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi269QChiValue_eq :
    chi269QChiValue =
      (chi269Slice.qChiAD 8 chi269LogChiCertificate).value := by
  norm_num [chi269QChiValue, chi269LogChiCertificate, chi269Slice,
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
private theorem chi269LogChi_valid :
    (if chi269Slice.lo = 0 then
      if chi269Slice.hi = 0 then true
      else decide (chi269Slice.hi ≤ 1 / 4) &&
        chi269LogChiCertificate.check
          (IntervalAD.const chi269Slice.hi).value
    else chi269LogChiCertificate.check
      chi269Slice.chiAD.value) = true := by
  norm_num [chi269Slice, chi269LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi269ValidityFacts :
    ChiFacts chi269Slice chi269LogChiCertificate :=
  { domain := by norm_num [chi269Slice]
    onePlusPositive := by
      norm_num [chi269Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi269LogChi_valid }

noncomputable def chi269InputQChi : RationalEnclosure :=
  { lower := (-2106337/8388608), upper := (-4028973/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi269InputQChi_eq :
    chi269InputQChi = outerEnclosure 24 chi269QChiValue := by
  rfl'

theorem chi269RoundedFacts :
    ChiRoundedFacts 8 chi269Slice chi269LogChiCertificate
      chi269InputQChi :=
  { coversQChi := by
      rw [chi269InputQChi_eq, chi269QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi270Slice : ChiSlice :=
  { lo := (59/128), hi := (15/32) }

noncomputable def chi270LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (59/32) }, upper := { exponent := -2, mantissa := (15/8) } }

private noncomputable def chi270QChiValue : RationalEnclosure :=
  { lower := (-1782383099692516879888709629160583531134/7172556819236492917611774950678725449849), upper := (-116382317086970395840967812239977259505859428848406805808855547/489588832352984935714679843190093098705106721598860421136215808) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi270QChiValue_eq :
    chi270QChiValue =
      (chi270Slice.qChiAD 8 chi270LogChiCertificate).value := by
  norm_num [chi270QChiValue, chi270LogChiCertificate, chi270Slice,
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
private theorem chi270LogChi_valid :
    (if chi270Slice.lo = 0 then
      if chi270Slice.hi = 0 then true
      else decide (chi270Slice.hi ≤ 1 / 4) &&
        chi270LogChiCertificate.check
          (IntervalAD.const chi270Slice.hi).value
    else chi270LogChiCertificate.check
      chi270Slice.chiAD.value) = true := by
  norm_num [chi270Slice, chi270LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi270ValidityFacts :
    ChiFacts chi270Slice chi270LogChiCertificate :=
  { domain := by norm_num [chi270Slice]
    onePlusPositive := by
      norm_num [chi270Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi270LogChi_valid }

noncomputable def chi270InputQChi : RationalEnclosure :=
  { lower := (-4169145/16777216), upper := (-3988185/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi270InputQChi_eq :
    chi270InputQChi = outerEnclosure 24 chi270QChiValue := by
  rfl'

theorem chi270RoundedFacts :
    ChiRoundedFacts 8 chi270Slice chi270LogChiCertificate
      chi270InputQChi :=
  { coversQChi := by
      rw [chi270InputQChi_eq, chi270QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi271Slice : ChiSlice :=
  { lo := (15/32), hi := (61/128) }

noncomputable def chi271LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (15/8) }, upper := { exponent := -2, mantissa := (61/32) } }

private noncomputable def chi271QChiValue : RationalEnclosure :=
  { lower := (-5310197072430965873307168802519277/21599790681302149438958404305096360), upper := (-175933878561897133507025464984291826467311571374804141199624547/747956875736078233697045744368479388708045821749507979316792320) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi271QChiValue_eq :
    chi271QChiValue =
      (chi271Slice.qChiAD 8 chi271LogChiCertificate).value := by
  norm_num [chi271QChiValue, chi271LogChiCertificate, chi271Slice,
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
private theorem chi271LogChi_valid :
    (if chi271Slice.lo = 0 then
      if chi271Slice.hi = 0 then true
      else decide (chi271Slice.hi ≤ 1 / 4) &&
        chi271LogChiCertificate.check
          (IntervalAD.const chi271Slice.hi).value
    else chi271LogChiCertificate.check
      chi271Slice.chiAD.value) = true := by
  norm_num [chi271Slice, chi271LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi271ValidityFacts :
    ChiFacts chi271Slice chi271LogChiCertificate :=
  { domain := by norm_num [chi271Slice]
    onePlusPositive := by
      norm_num [chi271Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi271LogChi_valid }

noncomputable def chi271InputQChi : RationalEnclosure :=
  { lower := (-257787/1048576), upper := (-986581/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi271InputQChi_eq :
    chi271InputQChi = outerEnclosure 24 chi271QChiValue := by
  rfl'

theorem chi271RoundedFacts :
    ChiRoundedFacts 8 chi271Slice chi271LogChiCertificate
      chi271InputQChi :=
  { coversQChi := by
      rw [chi271InputQChi_eq, chi271QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi272Slice : ChiSlice :=
  { lo := (61/128), hi := (31/64) }

noncomputable def chi272LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (61/32) }, upper := { exponent := -2, mantissa := (31/16) } }

private noncomputable def chi272QChiValue : RationalEnclosure :=
  { lower := (-75696229660303311903245686695539/311339684216436122780432475148755), upper := (-4348087727640243949084746117894620958056492867808405453172274891/18688375410818634398937199248805972911585962555135672424165300480) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi272QChiValue_eq :
    chi272QChiValue =
      (chi272Slice.qChiAD 8 chi272LogChiCertificate).value := by
  norm_num [chi272QChiValue, chi272LogChiCertificate, chi272Slice,
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
private theorem chi272LogChi_valid :
    (if chi272Slice.lo = 0 then
      if chi272Slice.hi = 0 then true
      else decide (chi272Slice.hi ≤ 1 / 4) &&
        chi272LogChiCertificate.check
          (IntervalAD.const chi272Slice.hi).value
    else chi272LogChiCertificate.check
      chi272Slice.chiAD.value) = true := by
  norm_num [chi272Slice, chi272LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi272ValidityFacts :
    ChiFacts chi272Slice chi272LogChiCertificate :=
  { domain := by norm_num [chi272Slice]
    onePlusPositive := by
      norm_num [chi272Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi272LogChi_valid }

noncomputable def chi272InputQChi : RationalEnclosure :=
  { lower := (-254941/1048576), upper := (-487929/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi272InputQChi_eq :
    chi272InputQChi = outerEnclosure 24 chi272QChiValue := by
  rfl'

theorem chi272RoundedFacts :
    ChiRoundedFacts 8 chi272Slice chi272LogChiCertificate
      chi272InputQChi :=
  { coversQChi := by
      rw [chi272InputQChi_eq, chi272QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi273Slice : ChiSlice :=
  { lo := (31/64), hi := (63/128) }

noncomputable def chi273LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (31/16) }, upper := { exponent := -2, mantissa := (63/32) } }

private noncomputable def chi273QChiValue : RationalEnclosure :=
  { lower := (-3768058812543452902961850607781055497/15676715379544132788629635201377813900), upper := (-35928992406151035204598143978166327994087461952948962718788412020349/156181073729658725949969367415136510035029140008663427440625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi273QChiValue_eq :
    chi273QChiValue =
      (chi273Slice.qChiAD 8 chi273LogChiCertificate).value := by
  norm_num [chi273QChiValue, chi273LogChiCertificate, chi273Slice,
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
private theorem chi273LogChi_valid :
    (if chi273Slice.lo = 0 then
      if chi273Slice.hi = 0 then true
      else decide (chi273Slice.hi ≤ 1 / 4) &&
        chi273LogChiCertificate.check
          (IntervalAD.const chi273Slice.hi).value
    else chi273LogChiCertificate.check
      chi273Slice.chiAD.value) = true := by
  norm_num [chi273Slice, chi273LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi273ValidityFacts :
    ChiFacts chi273Slice chi273LogChiCertificate :=
  { domain := by norm_num [chi273Slice]
    onePlusPositive := by
      norm_num [chi273Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi273LogChi_valid }

noncomputable def chi273InputQChi : RationalEnclosure :=
  { lower := (-63009/262144), upper := (-964887/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi273InputQChi_eq :
    chi273InputQChi = outerEnclosure 24 chi273QChiValue := by
  rfl'

theorem chi273RoundedFacts :
    ChiRoundedFacts 8 chi273Slice chi273LogChiCertificate
      chi273InputQChi :=
  { coversQChi := by
      rw [chi273InputQChi_eq, chi273QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi274Slice : ChiSlice :=
  { lo := (63/128), hi := (1/2) }

noncomputable def chi274LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (63/32) }, upper := { exponent := -1, mantissa := (1) } }

private noncomputable def chi274QChiValue : RationalEnclosure :=
  { lower := (-4528563623376448562250748074960610934396704/19064771477495916764127572350553741455078125), upper := (-2219440598322716621663813825029533883463784211/9761162996477909383233317043483515625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi274QChiValue_eq :
    chi274QChiValue =
      (chi274Slice.qChiAD 8 chi274LogChiCertificate).value := by
  norm_num [chi274QChiValue, chi274LogChiCertificate, chi274Slice,
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
private theorem chi274LogChi_valid :
    (if chi274Slice.lo = 0 then
      if chi274Slice.hi = 0 then true
      else decide (chi274Slice.hi ≤ 1 / 4) &&
        chi274LogChiCertificate.check
          (IntervalAD.const chi274Slice.hi).value
    else chi274LogChiCertificate.check
      chi274Slice.chiAD.value) = true := by
  norm_num [chi274Slice, chi274LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi274ValidityFacts :
    ChiFacts chi274Slice chi274LogChiCertificate :=
  { domain := by norm_num [chi274Slice]
    onePlusPositive := by
      norm_num [chi274Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi274LogChi_valid }

noncomputable def chi274InputQChi : RationalEnclosure :=
  { lower := (-996297/4194304), upper := (-476839/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi274InputQChi_eq :
    chi274InputQChi = outerEnclosure 24 chi274QChiValue := by
  rfl'

theorem chi274RoundedFacts :
    ChiRoundedFacts 8 chi274Slice chi274LogChiCertificate
      chi274InputQChi :=
  { coversQChi := by
      rw [chi274InputQChi_eq, chi274QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi275Slice : ChiSlice :=
  { lo := (33/128), hi := (67/256) }

noncomputable def chi275LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (33/32) }, upper := { exponent := -2, mantissa := (67/64) } }

private noncomputable def chi275QChiValue : RationalEnclosure :=
  { lower := (-4702326268547920608316536531904736267273/16671973911303217734094793340454101562500), upper := (-76448433901858226779193001768701211857105163066992035564034435909276325929623/279138760851871554168803816920847123451275338083187233077845437656250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi275QChiValue_eq :
    chi275QChiValue =
      (chi275Slice.qChiAD 8 chi275LogChiCertificate).value := by
  norm_num [chi275QChiValue, chi275LogChiCertificate, chi275Slice,
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
private theorem chi275LogChi_valid :
    (if chi275Slice.lo = 0 then
      if chi275Slice.hi = 0 then true
      else decide (chi275Slice.hi ≤ 1 / 4) &&
        chi275LogChiCertificate.check
          (IntervalAD.const chi275Slice.hi).value
    else chi275LogChiCertificate.check
      chi275Slice.chiAD.value) = true := by
  norm_num [chi275Slice, chi275LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi275ValidityFacts :
    ChiFacts chi275Slice chi275LogChiCertificate :=
  { domain := by norm_num [chi275Slice]
    onePlusPositive := by
      norm_num [chi275Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi275LogChi_valid }

noncomputable def chi275InputQChi : RationalEnclosure :=
  { lower := (-2366005/8388608), upper := (-2297409/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi275InputQChi_eq :
    chi275InputQChi = outerEnclosure 24 chi275QChiValue := by
  rfl'

theorem chi275RoundedFacts :
    ChiRoundedFacts 8 chi275Slice chi275LogChiCertificate
      chi275InputQChi :=
  { coversQChi := by
      rw [chi275InputQChi_eq, chi275QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi276Slice : ChiSlice :=
  { lo := (67/256), hi := (17/64) }

noncomputable def chi276LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (67/64) }, upper := { exponent := -2, mantissa := (17/16) } }

private noncomputable def chi276QChiValue : RationalEnclosure :=
  { lower := (-6030354050190143773270121718613726834418702/21368523164850216694224138453490292316518295), upper := (-10860880609591271144321933506314405218064077833611649629382165627/39623592061497751680950962015855039925016799201585221490679815680) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi276QChiValue_eq :
    chi276QChiValue =
      (chi276Slice.qChiAD 8 chi276LogChiCertificate).value := by
  norm_num [chi276QChiValue, chi276LogChiCertificate, chi276Slice,
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
private theorem chi276LogChi_valid :
    (if chi276Slice.lo = 0 then
      if chi276Slice.hi = 0 then true
      else decide (chi276Slice.hi ≤ 1 / 4) &&
        chi276LogChiCertificate.check
          (IntervalAD.const chi276Slice.hi).value
    else chi276LogChiCertificate.check
      chi276Slice.chiAD.value) = true := by
  norm_num [chi276Slice, chi276LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi276ValidityFacts :
    ChiFacts chi276Slice chi276LogChiCertificate :=
  { domain := by norm_num [chi276Slice]
    onePlusPositive := by
      norm_num [chi276Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi276LogChi_valid }

noncomputable def chi276InputQChi : RationalEnclosure :=
  { lower := (-2367327/8388608), upper := (-4598657/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi276InputQChi_eq :
    chi276InputQChi = outerEnclosure 24 chi276QChiValue := by
  rfl'

theorem chi276RoundedFacts :
    ChiRoundedFacts 8 chi276Slice chi276LogChiCertificate
      chi276InputQChi :=
  { coversQChi := by
      rw [chi276InputQChi_eq, chi276QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi277Slice : ChiSlice :=
  { lo := (1/4), hi := (65/256) }

noncomputable def chi277LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (65/64) } }

private noncomputable def chi277QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2121342410880), upper := (-76259743329735301601157917360443129476569/279065566245515285239650628775178242457600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi277QChiValue_eq :
    chi277QChiValue =
      (chi277Slice.qChiAD 8 chi277LogChiCertificate).value := by
  norm_num [chi277QChiValue, chi277LogChiCertificate, chi277Slice,
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
private theorem chi277LogChi_valid :
    (if chi277Slice.lo = 0 then
      if chi277Slice.hi = 0 then true
      else decide (chi277Slice.hi ≤ 1 / 4) &&
        chi277LogChiCertificate.check
          (IntervalAD.const chi277Slice.hi).value
    else chi277LogChiCertificate.check
      chi277Slice.chiAD.value) = true := by
  norm_num [chi277Slice, chi277LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi277ValidityFacts :
    ChiFacts chi277Slice chi277LogChiCertificate :=
  { domain := by norm_num [chi277Slice]
    onePlusPositive := by
      norm_num [chi277Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi277LogChi_valid }

noncomputable def chi277InputQChi : RationalEnclosure :=
  { lower := (-2362157/8388608), upper := (-4584679/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi277InputQChi_eq :
    chi277InputQChi = outerEnclosure 24 chi277QChiValue := by
  rfl'

theorem chi277RoundedFacts :
    ChiRoundedFacts 8 chi277Slice chi277LogChiCertificate
      chi277InputQChi :=
  { coversQChi := by
      rw [chi277InputQChi_eq, chi277QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi278Slice : ChiSlice :=
  { lo := (65/256), hi := (33/128) }

noncomputable def chi278LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (65/64) }, upper := { exponent := -2, mantissa := (33/32) } }

private noncomputable def chi278QChiValue : RationalEnclosure :=
  { lower := (-1876601157916513275631124407596290357/6658280444645084597670108885238738695), upper := (-198479679429485545943512025913452649533292159447129515628799183941751/725450197128513967357994590704160546320538271645121737578125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi278QChiValue_eq :
    chi278QChiValue =
      (chi278Slice.qChiAD 8 chi278LogChiCertificate).value := by
  norm_num [chi278QChiValue, chi278LogChiCertificate, chi278Slice,
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
private theorem chi278LogChi_valid :
    (if chi278Slice.lo = 0 then
      if chi278Slice.hi = 0 then true
      else decide (chi278Slice.hi ≤ 1 / 4) &&
        chi278LogChiCertificate.check
          (IntervalAD.const chi278Slice.hi).value
    else chi278LogChiCertificate.check
      chi278Slice.chiAD.value) = true := by
  norm_num [chi278Slice, chi278LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi278ValidityFacts :
    ChiFacts chi278Slice chi278LogChiCertificate :=
  { domain := by norm_num [chi278Slice]
    onePlusPositive := by
      norm_num [chi278Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi278LogChi_valid }

noncomputable def chi278InputQChi : RationalEnclosure :=
  { lower := (-2364285/8388608), upper := (-4590165/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi278InputQChi_eq :
    chi278InputQChi = outerEnclosure 24 chi278QChiValue := by
  rfl'

theorem chi278RoundedFacts :
    ChiRoundedFacts 8 chi278Slice chi278LogChiCertificate
      chi278InputQChi :=
  { coversQChi := by
      rw [chi278InputQChi_eq, chi278QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi279Slice : ChiSlice :=
  { lo := (35/128), hi := (71/256) }

noncomputable def chi279LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (35/32) }, upper := { exponent := -2, mantissa := (71/64) } }

private noncomputable def chi279QChiValue : RationalEnclosure :=
  { lower := (-97631082177064768553465996181675572667803/345711473812605073482498373144265655129780), upper := (-90873748530218844249633479752431723049742091300532037746634878149465227/331041895370680833818991374334199067869599535053327534216093750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi279QChiValue_eq :
    chi279QChiValue =
      (chi279Slice.qChiAD 8 chi279LogChiCertificate).value := by
  norm_num [chi279QChiValue, chi279LogChiCertificate, chi279Slice,
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
private theorem chi279LogChi_valid :
    (if chi279Slice.lo = 0 then
      if chi279Slice.hi = 0 then true
      else decide (chi279Slice.hi ≤ 1 / 4) &&
        chi279LogChiCertificate.check
          (IntervalAD.const chi279Slice.hi).value
    else chi279LogChiCertificate.check
      chi279Slice.chiAD.value) = true := by
  norm_num [chi279Slice, chi279LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi279ValidityFacts :
    ChiFacts chi279Slice chi279LogChiCertificate :=
  { domain := by norm_num [chi279Slice]
    onePlusPositive := by
      norm_num [chi279Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi279LogChi_valid }

noncomputable def chi279InputQChi : RationalEnclosure :=
  { lower := (-4737991/16777216), upper := (-4605485/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi279InputQChi_eq :
    chi279InputQChi = outerEnclosure 24 chi279QChiValue := by
  rfl'

theorem chi279RoundedFacts :
    ChiRoundedFacts 8 chi279Slice chi279LogChiCertificate
      chi279InputQChi :=
  { coversQChi := by
      rw [chi279InputQChi_eq, chi279QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi280Slice : ChiSlice :=
  { lo := (71/256), hi := (9/32) }

noncomputable def chi280LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (71/64) }, upper := { exponent := -2, mantissa := (9/8) } }

private noncomputable def chi280QChiValue : RationalEnclosure :=
  { lower := (-13889237752176655053253682363978454412/49185501876686846012151960296630859375), upper := (-7302903379216435566087562113082747896716147067194913170546207/26599119156855784213671301102499104329112645756171875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi280QChiValue_eq :
    chi280QChiValue =
      (chi280Slice.qChiAD 8 chi280LogChiCertificate).value := by
  norm_num [chi280QChiValue, chi280LogChiCertificate, chi280Slice,
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
private theorem chi280LogChi_valid :
    (if chi280Slice.lo = 0 then
      if chi280Slice.hi = 0 then true
      else decide (chi280Slice.hi ≤ 1 / 4) &&
        chi280LogChiCertificate.check
          (IntervalAD.const chi280Slice.hi).value
    else chi280LogChiCertificate.check
      chi280Slice.chiAD.value) = true := by
  norm_num [chi280Slice, chi280LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi280ValidityFacts :
    ChiFacts chi280Slice chi280LogChiCertificate :=
  { domain := by norm_num [chi280Slice]
    onePlusPositive := by
      norm_num [chi280Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi280LogChi_valid }

noncomputable def chi280InputQChi : RationalEnclosure :=
  { lower := (-4737631/16777216), upper := (-4606257/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi280InputQChi_eq :
    chi280InputQChi = outerEnclosure 24 chi280QChiValue := by
  rfl'

theorem chi280RoundedFacts :
    ChiRoundedFacts 8 chi280Slice chi280LogChiCertificate
      chi280InputQChi :=
  { coversQChi := by
      rw [chi280InputQChi_eq, chi280QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi281Slice : ChiSlice :=
  { lo := (9/32), hi := (73/256) }

noncomputable def chi281LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (9/8) }, upper := { exponent := -2, mantissa := (73/64) } }

private noncomputable def chi281QChiValue : RationalEnclosure :=
  { lower := (-114215539117377013008511044008879/404558953660844257259725130229840), upper := (-1051620717302844330553749504120417291916332313853328233558538593892067/3830241769147604051852332158349714950118605927195747485609613977210880) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi281QChiValue_eq :
    chi281QChiValue =
      (chi281Slice.qChiAD 8 chi281LogChiCertificate).value := by
  norm_num [chi281QChiValue, chi281LogChiCertificate, chi281Slice,
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
private theorem chi281LogChi_valid :
    (if chi281Slice.lo = 0 then
      if chi281Slice.hi = 0 then true
      else decide (chi281Slice.hi ≤ 1 / 4) &&
        chi281LogChiCertificate.check
          (IntervalAD.const chi281Slice.hi).value
    else chi281LogChiCertificate.check
      chi281Slice.chiAD.value) = true := by
  norm_num [chi281Slice, chi281LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi281ValidityFacts :
    ChiFacts chi281Slice chi281LogChiCertificate :=
  { domain := by norm_num [chi281Slice]
    onePlusPositive := by
      norm_num [chi281Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi281LogChi_valid }

noncomputable def chi281InputQChi : RationalEnclosure :=
  { lower := (-4736563/16777216), upper := (-2303153/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi281InputQChi_eq :
    chi281InputQChi = outerEnclosure 24 chi281QChiValue := by
  rfl'

theorem chi281RoundedFacts :
    ChiRoundedFacts 8 chi281Slice chi281LogChiCertificate
      chi281InputQChi :=
  { coversQChi := by
      rw [chi281InputQChi_eq, chi281QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi282Slice : ChiSlice :=
  { lo := (73/256), hi := (37/128) }

noncomputable def chi282LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (73/64) }, upper := { exponent := -2, mantissa := (37/32) } }

private noncomputable def chi282QChiValue : RationalEnclosure :=
  { lower := (-172976526930122712465575479698288932578733879/612922000393265942668087214884427835279071745), upper := (-607675122237207772080109181585697235199216842027199594212152185952404479/2213606785619467812560546717755225027582416725539048139627654839479206400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi282QChiValue_eq :
    chi282QChiValue =
      (chi282Slice.qChiAD 8 chi282LogChiCertificate).value := by
  norm_num [chi282QChiValue, chi282LogChiCertificate, chi282Slice,
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
private theorem chi282LogChi_valid :
    (if chi282Slice.lo = 0 then
      if chi282Slice.hi = 0 then true
      else decide (chi282Slice.hi ≤ 1 / 4) &&
        chi282LogChiCertificate.check
          (IntervalAD.const chi282Slice.hi).value
    else chi282LogChiCertificate.check
      chi282Slice.chiAD.value) = true := by
  norm_num [chi282Slice, chi282LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi282ValidityFacts :
    ChiFacts chi282Slice chi282LogChiCertificate :=
  { domain := by norm_num [chi282Slice]
    onePlusPositive := by
      norm_num [chi282Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi282LogChi_valid }

noncomputable def chi282InputQChi : RationalEnclosure :=
  { lower := (-4734803/16777216), upper := (-4605649/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi282InputQChi_eq :
    chi282InputQChi = outerEnclosure 24 chi282QChiValue := by
  rfl'

theorem chi282RoundedFacts :
    ChiRoundedFacts 8 chi282Slice chi282LogChiCertificate
      chi282InputQChi :=
  { coversQChi := by
      rw [chi282InputQChi_eq, chi282QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi283Slice : ChiSlice :=
  { lo := (37/128), hi := (75/256) }

noncomputable def chi283LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (37/32) }, upper := { exponent := -2, mantissa := (75/64) } }

private noncomputable def chi283QChiValue : RationalEnclosure :=
  { lower := (-142594509087687840142981868733553/505527015945369454954345632672468), upper := (-205299661613997131910333746345788893168372600734536264719040225423765723/748073629574919784645309158643415922495828427475577961672722170108544000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi283QChiValue_eq :
    chi283QChiValue =
      (chi283Slice.qChiAD 8 chi283LogChiCertificate).value := by
  norm_num [chi283QChiValue, chi283LogChiCertificate, chi283Slice,
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
private theorem chi283LogChi_valid :
    (if chi283Slice.lo = 0 then
      if chi283Slice.hi = 0 then true
      else decide (chi283Slice.hi ≤ 1 / 4) &&
        chi283LogChiCertificate.check
          (IntervalAD.const chi283Slice.hi).value
    else chi283LogChiCertificate.check
      chi283Slice.chiAD.value) = true := by
  norm_num [chi283Slice, chi283LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi283ValidityFacts :
    ChiFacts chi283Slice chi283LogChiCertificate :=
  { domain := by norm_num [chi283Slice]
    onePlusPositive := by
      norm_num [chi283Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi283LogChi_valid }

noncomputable def chi283InputQChi : RationalEnclosure :=
  { lower := (-4732367/16777216), upper := (-4604301/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi283InputQChi_eq :
    chi283InputQChi = outerEnclosure 24 chi283QChiValue := by
  rfl'

theorem chi283RoundedFacts :
    ChiRoundedFacts 8 chi283Slice chi283LogChiCertificate
      chi283InputQChi :=
  { coversQChi := by
      rw [chi283InputQChi_eq, chi283QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi284Slice : ChiSlice :=
  { lo := (75/256), hi := (19/64) }

noncomputable def chi284LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (75/64) }, upper := { exponent := -2, mantissa := (19/16) } }

private noncomputable def chi284QChiValue : RationalEnclosure :=
  { lower := (-401208575105664362491690338269016776811230066/1423298903909553695944347861656850162868081035), upper := (-6524894274859759051594619353373534718368994880344111733870103606318553563/23785944129922222883814680974729083124041285513077168478336796875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi284QChiValue_eq :
    chi284QChiValue =
      (chi284Slice.qChiAD 8 chi284LogChiCertificate).value := by
  norm_num [chi284QChiValue, chi284LogChiCertificate, chi284Slice,
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
private theorem chi284LogChi_valid :
    (if chi284Slice.lo = 0 then
      if chi284Slice.hi = 0 then true
      else decide (chi284Slice.hi ≤ 1 / 4) &&
        chi284LogChiCertificate.check
          (IntervalAD.const chi284Slice.hi).value
    else chi284LogChiCertificate.check
      chi284Slice.chiAD.value) = true := by
  norm_num [chi284Slice, chi284LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi284ValidityFacts :
    ChiFacts chi284Slice chi284LogChiCertificate :=
  { domain := by norm_num [chi284Slice]
    onePlusPositive := by
      norm_num [chi284Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi284LogChi_valid }

noncomputable def chi284InputQChi : RationalEnclosure :=
  { lower := (-4729269/16777216), upper := (-4602279/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi284InputQChi_eq :
    chi284InputQChi = outerEnclosure 24 chi284QChiValue := by
  rfl'

theorem chi284RoundedFacts :
    ChiRoundedFacts 8 chi284Slice chi284LogChiCertificate
      chi284InputQChi :=
  { coversQChi := by
      rw [chi284InputQChi_eq, chi284QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi285Slice : ChiSlice :=
  { lo := (19/64), hi := (77/256) }

noncomputable def chi285LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (19/16) }, upper := { exponent := -2, mantissa := (77/64) } }

private noncomputable def chi285QChiValue : RationalEnclosure :=
  { lower := (-10831143775292511139439782773239147/38454231524311976075672607421875000), upper := (-13250928095213219720683297735585726068231152710891149592421372603/48333292469615490843503047396931717470770065631184687500000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi285QChiValue_eq :
    chi285QChiValue =
      (chi285Slice.qChiAD 8 chi285LogChiCertificate).value := by
  norm_num [chi285QChiValue, chi285LogChiCertificate, chi285Slice,
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
private theorem chi285LogChi_valid :
    (if chi285Slice.lo = 0 then
      if chi285Slice.hi = 0 then true
      else decide (chi285Slice.hi ≤ 1 / 4) &&
        chi285LogChiCertificate.check
          (IntervalAD.const chi285Slice.hi).value
    else chi285LogChiCertificate.check
      chi285Slice.chiAD.value) = true := by
  norm_num [chi285Slice, chi285LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi285ValidityFacts :
    ChiFacts chi285Slice chi285LogChiCertificate :=
  { domain := by norm_num [chi285Slice]
    onePlusPositive := by
      norm_num [chi285Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi285LogChi_valid }

noncomputable def chi285InputQChi : RationalEnclosure :=
  { lower := (-2362763/8388608), upper := (-4599597/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi285InputQChi_eq :
    chi285InputQChi = outerEnclosure 24 chi285QChiValue := by
  rfl'

theorem chi285RoundedFacts :
    ChiRoundedFacts 8 chi285Slice chi285LogChiCertificate
      chi285InputQChi :=
  { coversQChi := by
      rw [chi285InputQChi_eq, chi285QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi286Slice : ChiSlice :=
  { lo := (77/256), hi := (39/128) }

noncomputable def chi286LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (77/64) }, upper := { exponent := -2, mantissa := (39/32) } }

private noncomputable def chi286QChiValue : RationalEnclosure :=
  { lower := (-693868286565314246875351460358506497/2465750576904006311086078249285538745), upper := (-119070339371820429575394495444481066410728571142071063949717389588596917/434628221552062080285727711743369554878877386224128876748161888092884480) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi286QChiValue_eq :
    chi286QChiValue =
      (chi286Slice.qChiAD 8 chi286LogChiCertificate).value := by
  norm_num [chi286QChiValue, chi286LogChiCertificate, chi286Slice,
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
private theorem chi286LogChi_valid :
    (if chi286Slice.lo = 0 then
      if chi286Slice.hi = 0 then true
      else decide (chi286Slice.hi ≤ 1 / 4) &&
        chi286LogChiCertificate.check
          (IntervalAD.const chi286Slice.hi).value
    else chi286LogChiCertificate.check
      chi286Slice.chiAD.value) = true := by
  norm_num [chi286Slice, chi286LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi286ValidityFacts :
    ChiFacts chi286Slice chi286LogChiCertificate :=
  { domain := by norm_num [chi286Slice]
    onePlusPositive := by
      norm_num [chi286Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi286LogChi_valid }

noncomputable def chi286InputQChi : RationalEnclosure :=
  { lower := (-2360575/8388608), upper := (-2298135/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi286InputQChi_eq :
    chi286InputQChi = outerEnclosure 24 chi286QChiValue := by
  rfl'

theorem chi286RoundedFacts :
    ChiRoundedFacts 8 chi286Slice chi286LogChiCertificate
      chi286InputQChi :=
  { coversQChi := by
      rw [chi286InputQChi_eq, chi286QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi287Slice : ChiSlice :=
  { lo := (39/128), hi := (79/256) }

noncomputable def chi287LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (39/32) }, upper := { exponent := -2, mantissa := (79/64) } }

private noncomputable def chi287QChiValue : RationalEnclosure :=
  { lower := (-21600883782682327869643568324219254429933/76842797190499665530958422895122053987740), upper := (-2343817547647480990312269011783705945976397075520682447237511558334961434042717/8562729776759257039256214792657010178987053675834527333854027896806787874534400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi287QChiValue_eq :
    chi287QChiValue =
      (chi287Slice.qChiAD 8 chi287LogChiCertificate).value := by
  norm_num [chi287QChiValue, chi287LogChiCertificate, chi287Slice,
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
private theorem chi287LogChi_valid :
    (if chi287Slice.lo = 0 then
      if chi287Slice.hi = 0 then true
      else decide (chi287Slice.hi ≤ 1 / 4) &&
        chi287LogChiCertificate.check
          (IntervalAD.const chi287Slice.hi).value
    else chi287LogChiCertificate.check
      chi287Slice.chiAD.value) = true := by
  norm_num [chi287Slice, chi287LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi287ValidityFacts :
    ChiFacts chi287Slice chi287LogChiCertificate :=
  { domain := by norm_num [chi287Slice]
    onePlusPositive := by
      norm_num [chi287Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi287LogChi_valid }

noncomputable def chi287InputQChi : RationalEnclosure :=
  { lower := (-4716157/16777216), upper := (-574039/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi287InputQChi_eq :
    chi287InputQChi = outerEnclosure 24 chi287QChiValue := by
  rfl'

theorem chi287RoundedFacts :
    ChiRoundedFacts 8 chi287Slice chi287LogChiCertificate
      chi287InputQChi :=
  { coversQChi := by
      rw [chi287InputQChi_eq, chi287QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi288Slice : ChiSlice :=
  { lo := (79/256), hi := (5/16) }

noncomputable def chi288LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (79/64) }, upper := { exponent := -2, mantissa := (5/4) } }

private noncomputable def chi288QChiValue : RationalEnclosure :=
  { lower := (-6060048860005666880330621782069452018189368/21583580157585277047748973070175481807086215), upper := (-1517606140561262424784266690069043264257006041884787059/5549838056595597809898731564815788121370890957104729600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi288QChiValue_eq :
    chi288QChiValue =
      (chi288Slice.qChiAD 8 chi288LogChiCertificate).value := by
  norm_num [chi288QChiValue, chi288LogChiCertificate, chi288Slice,
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
private theorem chi288LogChi_valid :
    (if chi288Slice.lo = 0 then
      if chi288Slice.hi = 0 then true
      else decide (chi288Slice.hi ≤ 1 / 4) &&
        chi288LogChiCertificate.check
          (IntervalAD.const chi288Slice.hi).value
    else chi288LogChiCertificate.check
      chi288Slice.chiAD.value) = true := by
  norm_num [chi288Slice, chi288LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi288ValidityFacts :
    ChiFacts chi288Slice chi288LogChiCertificate :=
  { domain := by norm_num [chi288Slice]
    onePlusPositive := by
      norm_num [chi288Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi288LogChi_valid }

noncomputable def chi288InputQChi : RationalEnclosure :=
  { lower := (-147205/524288), upper := (-2293869/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi288InputQChi_eq :
    chi288InputQChi = outerEnclosure 24 chi288QChiValue := by
  rfl'

theorem chi288RoundedFacts :
    ChiRoundedFacts 8 chi288Slice chi288LogChiCertificate
      chi288InputQChi :=
  { coversQChi := by
      rw [chi288InputQChi_eq, chi288QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi289Slice : ChiSlice :=
  { lo := (5/16), hi := (81/256) }

noncomputable def chi289LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (5/4) }, upper := { exponent := -2, mantissa := (81/64) } }

private noncomputable def chi289QChiValue : RationalEnclosure :=
  { lower := (-7191657786880100557/25647629557105876320), upper := (-12891710244228994523443346420207313492059254986196470041489/47197842956062486683526959394863017546588913750000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi289QChiValue_eq :
    chi289QChiValue =
      (chi289Slice.qChiAD 8 chi289LogChiCertificate).value := by
  norm_num [chi289QChiValue, chi289LogChiCertificate, chi289Slice,
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
private theorem chi289LogChi_valid :
    (if chi289Slice.lo = 0 then
      if chi289Slice.hi = 0 then true
      else decide (chi289Slice.hi ≤ 1 / 4) &&
        chi289LogChiCertificate.check
          (IntervalAD.const chi289Slice.hi).value
    else chi289LogChiCertificate.check
      chi289Slice.chiAD.value) = true := by
  norm_num [chi289Slice, chi289LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi289ValidityFacts :
    ChiFacts chi289Slice chi289LogChiCertificate :=
  { domain := by norm_num [chi289Slice]
    onePlusPositive := by
      norm_num [chi289Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi289LogChi_valid }

noncomputable def chi289InputQChi : RationalEnclosure :=
  { lower := (-4704373/16777216), upper := (-4582561/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi289InputQChi_eq :
    chi289InputQChi = outerEnclosure 24 chi289QChiValue := by
  rfl'

theorem chi289RoundedFacts :
    ChiRoundedFacts 8 chi289Slice chi289LogChiCertificate
      chi289InputQChi :=
  { coversQChi := by
      rw [chi289InputQChi_eq, chi289QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi290Slice : ChiSlice :=
  { lo := (81/256), hi := (41/128) }

noncomputable def chi290LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (81/64) }, upper := { exponent := -2, mantissa := (41/32) } }

private noncomputable def chi290QChiValue : RationalEnclosure :=
  { lower := (-5353660728399434255401019638140991018024997711/19120273126270246557008287860418117218017578125), upper := (-164861405495524004075361483522774737419948564108907871719979023451085518187426579/604334678200404967463211058766123491511002225596329139820737937224140625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi290QChiValue_eq :
    chi290QChiValue =
      (chi290Slice.qChiAD 8 chi290LogChiCertificate).value := by
  norm_num [chi290QChiValue, chi290LogChiCertificate, chi290Slice,
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
private theorem chi290LogChi_valid :
    (if chi290Slice.lo = 0 then
      if chi290Slice.hi = 0 then true
      else decide (chi290Slice.hi ≤ 1 / 4) &&
        chi290LogChiCertificate.check
          (IntervalAD.const chi290Slice.hi).value
    else chi290LogChiCertificate.check
      chi290Slice.chiAD.value) = true := by
  norm_num [chi290Slice, chi290LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi290ValidityFacts :
    ChiFacts chi290Slice chi290LogChiCertificate :=
  { domain := by norm_num [chi290Slice]
    onePlusPositive := by
      norm_num [chi290Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi290LogChi_valid }

noncomputable def chi290InputQChi : RationalEnclosure :=
  { lower := (-4697607/16777216), upper := (-2288397/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi290InputQChi_eq :
    chi290InputQChi = outerEnclosure 24 chi290QChiValue := by
  rfl'

theorem chi290RoundedFacts :
    ChiRoundedFacts 8 chi290Slice chi290LogChiCertificate
      chi290InputQChi :=
  { coversQChi := by
      rw [chi290InputQChi_eq, chi290QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi291Slice : ChiSlice :=
  { lo := (41/128), hi := (83/256) }

noncomputable def chi291LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (41/32) }, upper := { exponent := -2, mantissa := (83/64) } }

private noncomputable def chi291QChiValue : RationalEnclosure :=
  { lower := (-51822004556635344205901630794327838140763/185368405851513570582053104630498182775980), upper := (-390404164769245868211249149036753361633090795284766877798876194462854761/1433096306321358857330015828110764330383348189755691393984422478030576640) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi291QChiValue_eq :
    chi291QChiValue =
      (chi291Slice.qChiAD 8 chi291LogChiCertificate).value := by
  norm_num [chi291QChiValue, chi291LogChiCertificate, chi291Slice,
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
private theorem chi291LogChi_valid :
    (if chi291Slice.lo = 0 then
      if chi291Slice.hi = 0 then true
      else decide (chi291Slice.hi ≤ 1 / 4) &&
        chi291LogChiCertificate.check
          (IntervalAD.const chi291Slice.hi).value
    else chi291LogChiCertificate.check
      chi291Slice.chiAD.value) = true := by
  norm_num [chi291Slice, chi291LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi291ValidityFacts :
    ChiFacts chi291Slice chi291LogChiCertificate :=
  { domain := by norm_num [chi291Slice]
    onePlusPositive := by
      norm_num [chi291Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi291LogChi_valid }

noncomputable def chi291InputQChi : RationalEnclosure :=
  { lower := (-1172569/4194304), upper := (-4570449/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi291InputQChi_eq :
    chi291InputQChi = outerEnclosure 24 chi291QChiValue := by
  rfl'

theorem chi291RoundedFacts :
    ChiRoundedFacts 8 chi291Slice chi291LogChiCertificate
      chi291InputQChi :=
  { coversQChi := by
      rw [chi291InputQChi_eq, chi291QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi292Slice : ChiSlice :=
  { lo := (83/256), hi := (21/64) }

noncomputable def chi292LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (83/64) }, upper := { exponent := -2, mantissa := (21/16) } }

private noncomputable def chi292QChiValue : RationalEnclosure :=
  { lower := (-3125471978736426522990702706383887458/11198702853192569406202882038196894365), upper := (-3400331135999990262273014824013032490939565261635703047352596581/12500837696802055410077034234671489142139395374961909775106572800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi292QChiValue_eq :
    chi292QChiValue =
      (chi292Slice.qChiAD 8 chi292LogChiCertificate).value := by
  norm_num [chi292QChiValue, chi292LogChiCertificate, chi292Slice,
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
private theorem chi292LogChi_valid :
    (if chi292Slice.lo = 0 then
      if chi292Slice.hi = 0 then true
      else decide (chi292Slice.hi ≤ 1 / 4) &&
        chi292LogChiCertificate.check
          (IntervalAD.const chi292Slice.hi).value
    else chi292LogChiCertificate.check
      chi292Slice.chiAD.value) = true := by
  norm_num [chi292Slice, chi292LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi292ValidityFacts :
    ChiFacts chi292Slice chi292LogChiCertificate :=
  { domain := by norm_num [chi292Slice]
    onePlusPositive := by
      norm_num [chi292Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi292LogChi_valid }

noncomputable def chi292InputQChi : RationalEnclosure :=
  { lower := (-4682393/16777216), upper := (-4563541/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi292InputQChi_eq :
    chi292InputQChi = outerEnclosure 24 chi292QChiValue := by
  rfl'

theorem chi292RoundedFacts :
    ChiRoundedFacts 8 chi292Slice chi292LogChiCertificate
      chi292InputQChi :=
  { coversQChi := by
      rw [chi292InputQChi_eq, chi292QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi293Slice : ChiSlice :=
  { lo := (21/64), hi := (85/256) }

noncomputable def chi293LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (21/16) }, upper := { exponent := -2, mantissa := (85/64) } }

private noncomputable def chi293QChiValue : RationalEnclosure :=
  { lower := (-160112704402761404621382924688357147/574724889339121920109417926477378120), upper := (-210758931270692288595282399267854602749384108678773836910239091638343407819/776094309033365670057562288755957052010723621994635378588203582798006732800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi293QChiValue_eq :
    chi293QChiValue =
      (chi293Slice.qChiAD 8 chi293LogChiCertificate).value := by
  norm_num [chi293QChiValue, chi293LogChiCertificate, chi293Slice,
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
private theorem chi293LogChi_valid :
    (if chi293Slice.lo = 0 then
      if chi293Slice.hi = 0 then true
      else decide (chi293Slice.hi ≤ 1 / 4) &&
        chi293LogChiCertificate.check
          (IntervalAD.const chi293Slice.hi).value
    else chi293LogChiCertificate.check
      chi293Slice.chiAD.value) = true := by
  norm_num [chi293Slice, chi293LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi293ValidityFacts :
    ChiFacts chi293Slice chi293LogChiCertificate :=
  { domain := by norm_num [chi293Slice]
    onePlusPositive := by
      norm_num [chi293Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi293LogChi_valid }

noncomputable def chi293InputQChi : RationalEnclosure :=
  { lower := (-292123/1048576), upper := (-284755/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi293InputQChi_eq :
    chi293InputQChi = outerEnclosure 24 chi293QChiValue := by
  rfl'

theorem chi293RoundedFacts :
    ChiRoundedFacts 8 chi293Slice chi293LogChiCertificate
      chi293InputQChi :=
  { coversQChi := by
      rw [chi293InputQChi_eq, chi293QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi294Slice : ChiSlice :=
  { lo := (85/256), hi := (43/128) }

noncomputable def chi294LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (85/64) }, upper := { exponent := -2, mantissa := (43/32) } }

private noncomputable def chi294QChiValue : RationalEnclosure :=
  { lower := (-8091435221917846300731709226001640545100628057/29099971423667870969671488052876901394967034445), upper := (-5217681111706039257269350050778960554841984534829464744619378983947667/19247282262274810601755480401342249839284073631763458251953125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi294QChiValue_eq :
    chi294QChiValue =
      (chi294Slice.qChiAD 8 chi294LogChiCertificate).value := by
  norm_num [chi294QChiValue, chi294LogChiCertificate, chi294Slice,
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
private theorem chi294LogChi_valid :
    (if chi294Slice.lo = 0 then
      if chi294Slice.hi = 0 then true
      else decide (chi294Slice.hi ≤ 1 / 4) &&
        chi294LogChiCertificate.check
          (IntervalAD.const chi294Slice.hi).value
    else chi294LogChiCertificate.check
      chi294Slice.chiAD.value) = true := by
  norm_num [chi294Slice, chi294LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi294ValidityFacts :
    ChiFacts chi294Slice chi294LogChiCertificate :=
  { domain := by norm_num [chi294Slice]
    onePlusPositive := by
      norm_num [chi294Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi294LogChi_valid }

noncomputable def chi294InputQChi : RationalEnclosure :=
  { lower := (-2332507/8388608), upper := (-4548079/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi294InputQChi_eq :
    chi294InputQChi = outerEnclosure 24 chi294QChiValue := by
  rfl'

theorem chi294RoundedFacts :
    ChiRoundedFacts 8 chi294Slice chi294LogChiCertificate
      chi294InputQChi :=
  { coversQChi := by
      rw [chi294InputQChi_eq, chi294QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi295Slice : ChiSlice :=
  { lo := (43/128), hi := (87/256) }

noncomputable def chi295LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (43/32) }, upper := { exponent := -2, mantissa := (87/64) } }

private noncomputable def chi295QChiValue : RationalEnclosure :=
  { lower := (-36167818113881830738657592779709/130338289719074964523315429687500), upper := (-45748777635689894042147314777887792421342701265389192893977874828918943991/169077836410468191812606501930827146167513482047686576843261718750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi295QChiValue_eq :
    chi295QChiValue =
      (chi295Slice.qChiAD 8 chi295LogChiCertificate).value := by
  norm_num [chi295QChiValue, chi295LogChiCertificate, chi295Slice,
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
private theorem chi295LogChi_valid :
    (if chi295Slice.lo = 0 then
      if chi295Slice.hi = 0 then true
      else decide (chi295Slice.hi ≤ 1 / 4) &&
        chi295LogChiCertificate.check
          (IntervalAD.const chi295Slice.hi).value
    else chi295LogChiCertificate.check
      chi295Slice.chiAD.value) = true := by
  norm_num [chi295Slice, chi295LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi295ValidityFacts :
    ChiFacts chi295Slice chi295LogChiCertificate :=
  { domain := by norm_num [chi295Slice]
    onePlusPositive := by
      norm_num [chi295Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi295LogChi_valid }

noncomputable def chi295InputQChi : RationalEnclosure :=
  { lower := (-2327771/8388608), upper := (-4539549/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi295InputQChi_eq :
    chi295InputQChi = outerEnclosure 24 chi295QChiValue := by
  rfl'

theorem chi295RoundedFacts :
    ChiRoundedFacts 8 chi295Slice chi295LogChiCertificate
      chi295InputQChi :=
  { coversQChi := by
      rw [chi295InputQChi_eq, chi295QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi296Slice : ChiSlice :=
  { lo := (87/256), hi := (11/32) }

noncomputable def chi296LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (87/64) }, upper := { exponent := -2, mantissa := (11/8) } }

private noncomputable def chi296QChiValue : RationalEnclosure :=
  { lower := (-899949626331693887416165158935745569533256644/3250123034188401156723233704900529901918396615), upper := (-3226720019539505471751178331935942811223339634410005582307643854228869/11949092349419641231751436211976351228867165208338642521844851855157760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi296QChiValue_eq :
    chi296QChiValue =
      (chi296Slice.qChiAD 8 chi296LogChiCertificate).value := by
  norm_num [chi296QChiValue, chi296LogChiCertificate, chi296Slice,
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
private theorem chi296LogChi_valid :
    (if chi296Slice.lo = 0 then
      if chi296Slice.hi = 0 then true
      else decide (chi296Slice.hi ≤ 1 / 4) &&
        chi296LogChiCertificate.check
          (IntervalAD.const chi296Slice.hi).value
    else chi296LogChiCertificate.check
      chi296Slice.chiAD.value) = true := by
  norm_num [chi296Slice, chi296LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi296ValidityFacts :
    ChiFacts chi296Slice chi296LogChiCertificate :=
  { domain := by norm_num [chi296Slice]
    onePlusPositive := by
      norm_num [chi296Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi296LogChi_valid }

noncomputable def chi296InputQChi : RationalEnclosure :=
  { lower := (-4645563/16777216), upper := (-4530501/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi296InputQChi_eq :
    chi296InputQChi = outerEnclosure 24 chi296QChiValue := by
  rfl'

theorem chi296RoundedFacts :
    ChiRoundedFacts 8 chi296Slice chi296LogChiCertificate
      chi296InputQChi :=
  { coversQChi := by
      rw [chi296InputQChi_eq, chi296QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi297Slice : ChiSlice :=
  { lo := (11/32), hi := (89/256) }

noncomputable def chi297LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (11/8) }, upper := { exponent := -2, mantissa := (89/64) } }

private noncomputable def chi297QChiValue : RationalEnclosure :=
  { lower := (-621691068986993846375683617327317/2250280256863430921269787518631760), upper := (-65256923257310350334495054232392375965935702516730459285698308249/242168172062108456964280613363259975414406347251638706352323481600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi297QChiValue_eq :
    chi297QChiValue =
      (chi297Slice.qChiAD 8 chi297LogChiCertificate).value := by
  norm_num [chi297QChiValue, chi297LogChiCertificate, chi297Slice,
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
private theorem chi297LogChi_valid :
    (if chi297Slice.lo = 0 then
      if chi297Slice.hi = 0 then true
      else decide (chi297Slice.hi ≤ 1 / 4) &&
        chi297LogChiCertificate.check
          (IntervalAD.const chi297Slice.hi).value
    else chi297LogChiCertificate.check
      chi297Slice.chiAD.value) = true := by
  norm_num [chi297Slice, chi297LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi297ValidityFacts :
    ChiFacts chi297Slice chi297LogChiCertificate :=
  { domain := by norm_num [chi297Slice]
    onePlusPositive := by
      norm_num [chi297Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi297LogChi_valid }

noncomputable def chi297InputQChi : RationalEnclosure :=
  { lower := (-289693/1048576), upper := (-4520947/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi297InputQChi_eq :
    chi297InputQChi = outerEnclosure 24 chi297QChiValue := by
  rfl'

theorem chi297RoundedFacts :
    ChiRoundedFacts 8 chi297Slice chi297LogChiCertificate
      chi297InputQChi :=
  { coversQChi := by
      rw [chi297InputQChi_eq, chi297QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi298Slice : ChiSlice :=
  { lo := (89/256), hi := (45/128) }

noncomputable def chi298LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (89/64) }, upper := { exponent := -2, mantissa := (45/32) } }

private noncomputable def chi298QChiValue : RationalEnclosure :=
  { lower := (-242841254869614614449508929846443377/881074546300717764391227345332527215), upper := (-2675143554900749814711365632917987605499586672304130289593474955054603/9949564468274032545875836800163207995654848779028638106537630207347200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi298QChiValue_eq :
    chi298QChiValue =
      (chi298Slice.qChiAD 8 chi298LogChiCertificate).value := by
  norm_num [chi298QChiValue, chi298LogChiCertificate, chi298Slice,
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
private theorem chi298LogChi_valid :
    (if chi298Slice.lo = 0 then
      if chi298Slice.hi = 0 then true
      else decide (chi298Slice.hi ≤ 1 / 4) &&
        chi298LogChiCertificate.check
          (IntervalAD.const chi298Slice.hi).value
    else chi298LogChiCertificate.check
      chi298Slice.chiAD.value) = true := by
  norm_num [chi298Slice, chi298LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi298ValidityFacts :
    ChiFacts chi298Slice chi298LogChiCertificate :=
  { domain := by norm_num [chi298Slice]
    onePlusPositive := by
      norm_num [chi298Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi298LogChi_valid }

noncomputable def chi298InputQChi : RationalEnclosure :=
  { lower := (-4624127/16777216), upper := (-4510897/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi298InputQChi_eq :
    chi298InputQChi = outerEnclosure 24 chi298QChiValue := by
  rfl'

theorem chi298RoundedFacts :
    ChiRoundedFacts 8 chi298Slice chi298LogChiCertificate
      chi298InputQChi :=
  { coversQChi := by
      rw [chi298InputQChi_eq, chi298QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi299Slice : ChiSlice :=
  { lo := (45/128), hi := (91/256) }

noncomputable def chi299LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (45/32) }, upper := { exponent := -2, mantissa := (91/64) } }

private noncomputable def chi299QChiValue : RationalEnclosure :=
  { lower := (-116014808338514569223870004641397746959/421967508799528739891275562883883547340), upper := (-93604084452479139102208084338418029893340933068186768889489344447073823478789/348953273568184849623761588523566909184644022362358225692716513593750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi299QChiValue_eq :
    chi299QChiValue =
      (chi299Slice.qChiAD 8 chi299LogChiCertificate).value := by
  norm_num [chi299QChiValue, chi299LogChiCertificate, chi299Slice,
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
private theorem chi299LogChi_valid :
    (if chi299Slice.lo = 0 then
      if chi299Slice.hi = 0 then true
      else decide (chi299Slice.hi ≤ 1 / 4) &&
        chi299LogChiCertificate.check
          (IntervalAD.const chi299Slice.hi).value
    else chi299LogChiCertificate.check
      chi299Slice.chiAD.value) = true := by
  norm_num [chi299Slice, chi299LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi299ValidityFacts :
    ChiFacts chi299Slice chi299LogChiCertificate :=
  { domain := by norm_num [chi299Slice]
    onePlusPositive := by
      norm_num [chi299Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi299LogChi_valid }

noncomputable def chi299InputQChi : RationalEnclosure :=
  { lower := (-4612691/16777216), upper := (-4500361/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi299InputQChi_eq :
    chi299InputQChi = outerEnclosure 24 chi299QChiValue := by
  rfl'

theorem chi299RoundedFacts :
    ChiRoundedFacts 8 chi299Slice chi299LogChiCertificate
      chi299InputQChi :=
  { coversQChi := by
      rw [chi299InputQChi_eq, chi299QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi300Slice : ChiSlice :=
  { lo := (91/256), hi := (23/64) }

noncomputable def chi300LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (91/64) }, upper := { exponent := -2, mantissa := (23/16) } }

private noncomputable def chi300QChiValue : RationalEnclosure :=
  { lower := (-14681199073752382335045309817006527726823033766/53536392668628855533040703890739416046142578125), upper := (-19262626895567499566554598358639298006711731782588420072588267372219/71986628175571042473479840573190658546578447198332080546875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi300QChiValue_eq :
    chi300QChiValue =
      (chi300Slice.qChiAD 8 chi300LogChiCertificate).value := by
  norm_num [chi300QChiValue, chi300LogChiCertificate, chi300Slice,
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
private theorem chi300LogChi_valid :
    (if chi300Slice.lo = 0 then
      if chi300Slice.hi = 0 then true
      else decide (chi300Slice.hi ≤ 1 / 4) &&
        chi300LogChiCertificate.check
          (IntervalAD.const chi300Slice.hi).value
    else chi300LogChiCertificate.check
      chi300Slice.chiAD.value) = true := by
  norm_num [chi300Slice, chi300LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi300ValidityFacts :
    ChiFacts chi300Slice chi300LogChiCertificate :=
  { domain := by norm_num [chi300Slice]
    onePlusPositive := by
      norm_num [chi300Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi300LogChi_valid }

noncomputable def chi300InputQChi : RationalEnclosure :=
  { lower := (-2300395/8388608), upper := (-4489351/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi300InputQChi_eq :
    chi300InputQChi = outerEnclosure 24 chi300QChiValue := by
  rfl'

theorem chi300RoundedFacts :
    ChiRoundedFacts 8 chi300Slice chi300LogChiCertificate
      chi300InputQChi :=
  { coversQChi := by
      rw [chi300InputQChi_eq, chi300QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi301Slice : ChiSlice :=
  { lo := (23/64), hi := (93/256) }

noncomputable def chi301LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (23/16) }, upper := { exponent := -2, mantissa := (93/64) } }

private noncomputable def chi301QChiValue : RationalEnclosure :=
  { lower := (-53824930955181983000222029649/196806335312322128231226428040), upper := (-126273744100920337244286128650125404011345498715642481109623504194887/473108713500989774342909012771772472294498332271178321339228390062080) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi301QChiValue_eq :
    chi301QChiValue =
      (chi301Slice.qChiAD 8 chi301LogChiCertificate).value := by
  norm_num [chi301QChiValue, chi301LogChiCertificate, chi301Slice,
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
private theorem chi301LogChi_valid :
    (if chi301Slice.lo = 0 then
      if chi301Slice.hi = 0 then true
      else decide (chi301Slice.hi ≤ 1 / 4) &&
        chi301LogChiCertificate.check
          (IntervalAD.const chi301Slice.hi).value
    else chi301LogChiCertificate.check
      chi301Slice.chiAD.value) = true := by
  norm_num [chi301Slice, chi301LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi301ValidityFacts :
    ChiFacts chi301Slice chi301LogChiCertificate :=
  { domain := by norm_num [chi301Slice]
    onePlusPositive := by
      norm_num [chi301Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi301LogChi_valid }

noncomputable def chi301InputQChi : RationalEnclosure :=
  { lower := (-4588433/16777216), upper := (-4477875/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi301InputQChi_eq :
    chi301InputQChi = outerEnclosure 24 chi301QChiValue := by
  rfl'

theorem chi301RoundedFacts :
    ChiRoundedFacts 8 chi301Slice chi301LogChiCertificate
      chi301InputQChi :=
  { coversQChi := by
      rw [chi301InputQChi_eq, chi301QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi302Slice : ChiSlice :=
  { lo := (93/256), hi := (47/128) }

noncomputable def chi302LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (93/64) }, upper := { exponent := -2, mantissa := (47/32) } }

private noncomputable def chi302QChiValue : RationalEnclosure :=
  { lower := (-17798986662700301639367813068347986766392885437/65262599812373981522891875609793105288500129485), upper := (-2131424751680587613244261600792120600585566831752475372622650913023967670255528729/8007124981728605314202411243646762775418394614983902679239748415756884746207168000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi302QChiValue_eq :
    chi302QChiValue =
      (chi302Slice.qChiAD 8 chi302LogChiCertificate).value := by
  norm_num [chi302QChiValue, chi302LogChiCertificate, chi302Slice,
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
private theorem chi302LogChi_valid :
    (if chi302Slice.lo = 0 then
      if chi302Slice.hi = 0 then true
      else decide (chi302Slice.hi ≤ 1 / 4) &&
        chi302LogChiCertificate.check
          (IntervalAD.const chi302Slice.hi).value
    else chi302LogChiCertificate.check
      chi302Slice.chiAD.value) = true := by
  norm_num [chi302Slice, chi302LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi302ValidityFacts :
    ChiFacts chi302Slice chi302LogChiCertificate :=
  { domain := by norm_num [chi302Slice]
    onePlusPositive := by
      norm_num [chi302Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi302LogChi_valid }

noncomputable def chi302InputQChi : RationalEnclosure :=
  { lower := (-4575629/16777216), upper := (-558243/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi302InputQChi_eq :
    chi302InputQChi = outerEnclosure 24 chi302QChiValue := by
  rfl'

theorem chi302RoundedFacts :
    ChiRoundedFacts 8 chi302Slice chi302LogChiCertificate
      chi302InputQChi :=
  { coversQChi := by
      rw [chi302InputQChi_eq, chi302QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi303Slice : ChiSlice :=
  { lo := (47/128), hi := (95/256) }

noncomputable def chi303LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (47/32) }, upper := { exponent := -2, mantissa := (95/64) } }

private noncomputable def chi303QChiValue : RationalEnclosure :=
  { lower := (-238974190219350780505484923295285951794699/878776758486417563687198217131665001835300), upper := (-599334273330513207702841425583095148174161147966759161678471065010593199/2257776871496025221340851013673736856630847743441896093727893943736704000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi303QChiValue_eq :
    chi303QChiValue =
      (chi303Slice.qChiAD 8 chi303LogChiCertificate).value := by
  norm_num [chi303QChiValue, chi303LogChiCertificate, chi303Slice,
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
private theorem chi303LogChi_valid :
    (if chi303Slice.lo = 0 then
      if chi303Slice.hi = 0 then true
      else decide (chi303Slice.hi ≤ 1 / 4) &&
        chi303LogChiCertificate.check
          (IntervalAD.const chi303Slice.hi).value
    else chi303LogChiCertificate.check
      chi303Slice.chiAD.value) = true := by
  norm_num [chi303Slice, chi303LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi303ValidityFacts :
    ChiFacts chi303Slice chi303LogChiCertificate :=
  { domain := by norm_num [chi303Slice]
    onePlusPositive := by
      norm_num [chi303Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi303LogChi_valid }

noncomputable def chi303InputQChi : RationalEnclosure :=
  { lower := (-2281195/8388608), upper := (-2226783/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi303InputQChi_eq :
    chi303InputQChi = outerEnclosure 24 chi303QChiValue := by
  rfl'

theorem chi303RoundedFacts :
    ChiRoundedFacts 8 chi303Slice chi303LogChiCertificate
      chi303InputQChi :=
  { coversQChi := by
      rw [chi303InputQChi_eq, chi303QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi304Slice : ChiSlice :=
  { lo := (95/256), hi := (3/8) }

noncomputable def chi304LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (95/64) }, upper := { exponent := -2, mantissa := (3/2) } }

private noncomputable def chi304QChiValue : RationalEnclosure :=
  { lower := (-55538613428914847877350705874191141168/204845087633793073496213190548449712805), upper := (-251616289935887937115143024059754599679683776650850699/950609234800570981693364337388899448485703125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi304QChiValue_eq :
    chi304QChiValue =
      (chi304Slice.qChiAD 8 chi304LogChiCertificate).value := by
  norm_num [chi304QChiValue, chi304LogChiCertificate, chi304Slice,
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
private theorem chi304LogChi_valid :
    (if chi304Slice.lo = 0 then
      if chi304Slice.hi = 0 then true
      else decide (chi304Slice.hi ≤ 1 / 4) &&
        chi304LogChiCertificate.check
          (IntervalAD.const chi304Slice.hi).value
    else chi304LogChiCertificate.check
      chi304Slice.chiAD.value) = true := by
  norm_num [chi304Slice, chi304LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi304ValidityFacts :
    ChiFacts chi304Slice chi304LogChiCertificate :=
  { domain := by norm_num [chi304Slice]
    onePlusPositive := by
      norm_num [chi304Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi304LogChi_valid }

noncomputable def chi304InputQChi : RationalEnclosure :=
  { lower := (-2274361/8388608), upper := (-4440753/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi304InputQChi_eq :
    chi304InputQChi = outerEnclosure 24 chi304QChiValue := by
  rfl'

theorem chi304RoundedFacts :
    ChiRoundedFacts 8 chi304Slice chi304LogChiCertificate
      chi304InputQChi :=
  { coversQChi := by
      rw [chi304InputQChi_eq, chi304QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi305Slice : ChiSlice :=
  { lo := (3/8), hi := (97/256) }

noncomputable def chi305LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (3/2) }, upper := { exponent := -2, mantissa := (97/64) } }

private noncomputable def chi305QChiValue : RationalEnclosure :=
  { lower := (-178727482027497455218637/661254805986328125000000), upper := (-21278537895389773447078693021616516467873357988289369074000323/80630990455325768759885744836292696220473866957500000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi305QChiValue_eq :
    chi305QChiValue =
      (chi305Slice.qChiAD 8 chi305LogChiCertificate).value := by
  norm_num [chi305QChiValue, chi305LogChiCertificate, chi305Slice,
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
private theorem chi305LogChi_valid :
    (if chi305Slice.lo = 0 then
      if chi305Slice.hi = 0 then true
      else decide (chi305Slice.hi ≤ 1 / 4) &&
        chi305LogChiCertificate.check
          (IntervalAD.const chi305Slice.hi).value
    else chi305LogChiCertificate.check
      chi305Slice.chiAD.value) = true := by
  norm_num [chi305Slice, chi305LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi305ValidityFacts :
    ChiFacts chi305Slice chi305LogChiCertificate :=
  { domain := by norm_num [chi305Slice]
    onePlusPositive := by
      norm_num [chi305Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi305LogChi_valid }

noncomputable def chi305InputQChi : RationalEnclosure :=
  { lower := (-1133659/4194304), upper := (-4427511/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi305InputQChi_eq :
    chi305InputQChi = outerEnclosure 24 chi305QChiValue := by
  rfl'

theorem chi305RoundedFacts :
    ChiRoundedFacts 8 chi305Slice chi305LogChiCertificate
      chi305InputQChi :=
  { coversQChi := by
      rw [chi305InputQChi_eq, chi305QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi306Slice : ChiSlice :=
  { lo := (97/256), hi := (49/128) }

noncomputable def chi306LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (97/64) }, upper := { exponent := -2, mantissa := (49/32) } }

private noncomputable def chi306QChiValue : RationalEnclosure :=
  { lower := (-75621415317307084620238857937028557708545473/280680914692525102123045838230500749997632955), upper := (-46130388365028428207329656534651226545690758960085384165853270678202651/175343373624773983747235194636441364214041766034581118910663462178224640) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi306QChiValue_eq :
    chi306QChiValue =
      (chi306Slice.qChiAD 8 chi306LogChiCertificate).value := by
  norm_num [chi306QChiValue, chi306LogChiCertificate, chi306Slice,
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
private theorem chi306LogChi_valid :
    (if chi306Slice.lo = 0 then
      if chi306Slice.hi = 0 then true
      else decide (chi306Slice.hi ≤ 1 / 4) &&
        chi306LogChiCertificate.check
          (IntervalAD.const chi306Slice.hi).value
    else chi306LogChiCertificate.check
      chi306Slice.chiAD.value) = true := by
  norm_num [chi306Slice, chi306LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi306ValidityFacts :
    ChiFacts chi306Slice chi306LogChiCertificate :=
  { domain := by norm_num [chi306Slice]
    onePlusPositive := by
      norm_num [chi306Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi306LogChi_valid }

noncomputable def chi306InputQChi : RationalEnclosure :=
  { lower := (-1130035/4194304), upper := (-2206925/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi306InputQChi_eq :
    chi306InputQChi = outerEnclosure 24 chi306QChiValue := by
  rfl'

theorem chi306RoundedFacts :
    ChiRoundedFacts 8 chi306Slice chi306LogChiCertificate
      chi306InputQChi :=
  { coversQChi := by
      rw [chi306InputQChi_eq, chi306QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi307Slice : ChiSlice :=
  { lo := (49/128), hi := (99/256) }

noncomputable def chi307LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (49/32) }, upper := { exponent := -2, mantissa := (99/64) } }

private noncomputable def chi307QChiValue : RationalEnclosure :=
  { lower := (-1222353553304264737253213480522021/4551962575592715933364936237123380), upper := (-16361658474329930389060514933759908691794292196446799549163900422041791777/62390183337037814677491969374805489917668485952005043700048243399982259200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi307QChiValue_eq :
    chi307QChiValue =
      (chi307Slice.qChiAD 8 chi307LogChiCertificate).value := by
  norm_num [chi307QChiValue, chi307LogChiCertificate, chi307Slice,
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
private theorem chi307LogChi_valid :
    (if chi307Slice.lo = 0 then
      if chi307Slice.hi = 0 then true
      else decide (chi307Slice.hi ≤ 1 / 4) &&
        chi307LogChiCertificate.check
          (IntervalAD.const chi307Slice.hi).value
    else chi307LogChiCertificate.check
      chi307Slice.chiAD.value) = true := by
  norm_num [chi307Slice, chi307LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi307ValidityFacts :
    ChiFacts chi307Slice chi307LogChiCertificate :=
  { domain := by norm_num [chi307Slice]
    onePlusPositive := by
      norm_num [chi307Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi307LogChi_valid }

noncomputable def chi307InputQChi : RationalEnclosure :=
  { lower := (-2252621/8388608), upper := (-4399779/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi307InputQChi_eq :
    chi307InputQChi = outerEnclosure 24 chi307QChiValue := by
  rfl'

theorem chi307RoundedFacts :
    ChiRoundedFacts 8 chi307Slice chi307LogChiCertificate
      chi307InputQChi :=
  { coversQChi := by
      rw [chi307InputQChi_eq, chi307QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi308Slice : ChiSlice :=
  { lo := (99/256), hi := (25/64) }

noncomputable def chi308LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (99/64) }, upper := { exponent := -2, mantissa := (25/16) } }

private noncomputable def chi308QChiValue : RationalEnclosure :=
  { lower := (-95945544372053479183060820799846775803418562/358511602644681894067449532894232759617465449), upper := (-10790822065663303010957931308785501114344253374203445838166493543878301548773/41283299397027412112224682780813632715011962699960667380494734931328274752000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi308QChiValue_eq :
    chi308QChiValue =
      (chi308Slice.qChiAD 8 chi308LogChiCertificate).value := by
  norm_num [chi308QChiValue, chi308LogChiCertificate, chi308Slice,
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
private theorem chi308LogChi_valid :
    (if chi308Slice.lo = 0 then
      if chi308Slice.hi = 0 then true
      else decide (chi308Slice.hi ≤ 1 / 4) &&
        chi308LogChiCertificate.check
          (IntervalAD.const chi308Slice.hi).value
    else chi308LogChiCertificate.check
      chi308Slice.chiAD.value) = true := by
  norm_num [chi308Slice, chi308LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi308ValidityFacts :
    ChiFacts chi308Slice chi308LogChiCertificate :=
  { domain := by norm_num [chi308Slice]
    onePlusPositive := by
      norm_num [chi308Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi308LogChi_valid }

noncomputable def chi308InputQChi : RationalEnclosure :=
  { lower := (-2244975/8388608), upper := (-4385307/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi308InputQChi_eq :
    chi308InputQChi = outerEnclosure 24 chi308QChiValue := by
  rfl'

theorem chi308RoundedFacts :
    ChiRoundedFacts 8 chi308Slice chi308LogChiCertificate
      chi308InputQChi :=
  { coversQChi := by
      rw [chi308InputQChi_eq, chi308QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi309Slice : ChiSlice :=
  { lo := (25/64), hi := (101/256) }

noncomputable def chi309LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (25/16) }, upper := { exponent := -2, mantissa := (101/64) } }

private noncomputable def chi309QChiValue : RationalEnclosure :=
  { lower := (-5783515644603611816243377068454044641/21686492511603794904753570283278911160), upper := (-2215865101981263983124997219802384971040735255819448727043680285972357/8506246414870904923123713468769424550231949083256958265937500000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi309QChiValue_eq :
    chi309QChiValue =
      (chi309Slice.qChiAD 8 chi309LogChiCertificate).value := by
  norm_num [chi309QChiValue, chi309LogChiCertificate, chi309Slice,
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
private theorem chi309LogChi_valid :
    (if chi309Slice.lo = 0 then
      if chi309Slice.hi = 0 then true
      else decide (chi309Slice.hi ≤ 1 / 4) &&
        chi309LogChiCertificate.check
          (IntervalAD.const chi309Slice.hi).value
    else chi309LogChiCertificate.check
      chi309Slice.chiAD.value) = true := by
  norm_num [chi309Slice, chi309LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi309ValidityFacts :
    ChiFacts chi309Slice chi309LogChiCertificate :=
  { domain := by norm_num [chi309Slice]
    onePlusPositive := by
      norm_num [chi309Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi309LogChi_valid }

noncomputable def chi309InputQChi : RationalEnclosure :=
  { lower := (-2237137/8388608), upper := (-546305/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi309InputQChi_eq :
    chi309InputQChi = outerEnclosure 24 chi309QChiValue := by
  rfl'

theorem chi309RoundedFacts :
    ChiRoundedFacts 8 chi309Slice chi309LogChiCertificate
      chi309InputQChi :=
  { coversQChi := by
      rw [chi309InputQChi_eq, chi309QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi310Slice : ChiSlice :=
  { lo := (101/256), hi := (51/128) }

noncomputable def chi310LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (101/64) }, upper := { exponent := -2, mantissa := (51/32) } }

private noncomputable def chi310QChiValue : RationalEnclosure :=
  { lower := (-4644418620502479663460690252528163923/17477924323781100259177601165771484375), upper := (-7344617511705912519644973933184348341061689680873180844804079019193922093/28293200352597984937567207812932419897810284487367855829621796875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi310QChiValue_eq :
    chi310QChiValue =
      (chi310Slice.qChiAD 8 chi310LogChiCertificate).value := by
  norm_num [chi310QChiValue, chi310LogChiCertificate, chi310Slice,
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
private theorem chi310LogChi_valid :
    (if chi310Slice.lo = 0 then
      if chi310Slice.hi = 0 then true
      else decide (chi310Slice.hi ≤ 1 / 4) &&
        chi310LogChiCertificate.check
          (IntervalAD.const chi310Slice.hi).value
    else chi310LogChiCertificate.check
      chi310Slice.chiAD.value) = true := by
  norm_num [chi310Slice, chi310LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi310ValidityFacts :
    ChiFacts chi310Slice chi310LogChiCertificate :=
  { domain := by norm_num [chi310Slice]
    onePlusPositive := by
      norm_num [chi310Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi310LogChi_valid }

noncomputable def chi310InputQChi : RationalEnclosure :=
  { lower := (-1114555/4194304), upper := (-1088797/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi310InputQChi_eq :
    chi310InputQChi = outerEnclosure 24 chi310QChiValue := by
  rfl'

theorem chi310RoundedFacts :
    ChiRoundedFacts 8 chi310Slice chi310LogChiCertificate
      chi310InputQChi :=
  { coversQChi := by
      rw [chi310InputQChi_eq, chi310QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi311Slice : ChiSlice :=
  { lo := (51/128), hi := (103/256) }

noncomputable def chi311LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (51/32) }, upper := { exponent := -2, mantissa := (103/64) } }

private noncomputable def chi311QChiValue : RationalEnclosure :=
  { lower := (-2496129962943138603418369478082217582837931/9428195194853239166691448902707796385774260), upper := (-50590969357490635128939201401396847885654594313287909683726180709809895183880209439/195590281205884712252054917146281527750556440384507690791100492153425124425673436160) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi311QChiValue_eq :
    chi311QChiValue =
      (chi311Slice.qChiAD 8 chi311LogChiCertificate).value := by
  norm_num [chi311QChiValue, chi311LogChiCertificate, chi311Slice,
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
private theorem chi311LogChi_valid :
    (if chi311Slice.lo = 0 then
      if chi311Slice.hi = 0 then true
      else decide (chi311Slice.hi ≤ 1 / 4) &&
        chi311LogChiCertificate.check
          (IntervalAD.const chi311Slice.hi).value
    else chi311LogChiCertificate.check
      chi311Slice.chiAD.value) = true := by
  norm_num [chi311Slice, chi311LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi311ValidityFacts :
    ChiFacts chi311Slice chi311LogChiCertificate :=
  { domain := by norm_num [chi311Slice]
    onePlusPositive := by
      norm_num [chi311Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi311LogChi_valid }

noncomputable def chi311InputQChi : RationalEnclosure :=
  { lower := (-1110449/4194304), upper := (-4339559/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi311InputQChi_eq :
    chi311InputQChi = outerEnclosure 24 chi311QChiValue := by
  rfl'

theorem chi311RoundedFacts :
    ChiRoundedFacts 8 chi311Slice chi311LogChiCertificate
      chi311InputQChi :=
  { coversQChi := by
      rw [chi311InputQChi_eq, chi311QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi312Slice : ChiSlice :=
  { lo := (103/256), hi := (13/32) }

noncomputable def chi312LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (103/64) }, upper := { exponent := -2, mantissa := (13/8) } }

private noncomputable def chi312QChiValue : RationalEnclosure :=
  { lower := (-491290708940543622362998223949694040060219612/1862705859826772143665104527563262733488071735), upper := (-833447696436802149090152558358577017238901692853663536477907/3234125035687813289250565329553250481537554811390573626918400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi312QChiValue_eq :
    chi312QChiValue =
      (chi312Slice.qChiAD 8 chi312LogChiCertificate).value := by
  norm_num [chi312QChiValue, chi312LogChiCertificate, chi312Slice,
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
private theorem chi312LogChi_valid :
    (if chi312Slice.lo = 0 then
      if chi312Slice.hi = 0 then true
      else decide (chi312Slice.hi ≤ 1 / 4) &&
        chi312LogChiCertificate.check
          (IntervalAD.const chi312Slice.hi).value
    else chi312LogChiCertificate.check
      chi312Slice.chiAD.value) = true := by
  norm_num [chi312Slice, chi312LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi312ValidityFacts :
    ChiFacts chi312Slice chi312LogChiCertificate :=
  { domain := by norm_num [chi312Slice]
    onePlusPositive := by
      norm_num [chi312Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi312LogChi_valid }

noncomputable def chi312InputQChi : RationalEnclosure :=
  { lower := (-2212505/8388608), upper := (-4323559/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi312InputQChi_eq :
    chi312InputQChi = outerEnclosure 24 chi312QChiValue := by
  rfl'

theorem chi312RoundedFacts :
    ChiRoundedFacts 8 chi312Slice chi312LogChiCertificate
      chi312InputQChi :=
  { coversQChi := by
      rw [chi312InputQChi_eq, chi312QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi313Slice : ChiSlice :=
  { lo := (13/32), hi := (105/256) }

noncomputable def chi313LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (13/8) }, upper := { exponent := -2, mantissa := (105/64) } }

private noncomputable def chi313QChiValue : RationalEnclosure :=
  { lower := (-29250016153892124618719/111331332084138177931920), upper := (-540354497541609527566667867199588166144292237205717481925093/2104766472395985902637318262460166123917820878518728247603200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi313QChiValue_eq :
    chi313QChiValue =
      (chi313Slice.qChiAD 8 chi313LogChiCertificate).value := by
  norm_num [chi313QChiValue, chi313LogChiCertificate, chi313Slice,
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
private theorem chi313LogChi_valid :
    (if chi313Slice.lo = 0 then
      if chi313Slice.hi = 0 then true
      else decide (chi313Slice.hi ≤ 1 / 4) &&
        chi313LogChiCertificate.check
          (IntervalAD.const chi313Slice.hi).value
    else chi313LogChiCertificate.check
      chi313Slice.chiAD.value) = true := by
  norm_num [chi313Slice, chi313LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi313ValidityFacts :
    ChiFacts chi313Slice chi313LogChiCertificate :=
  { domain := by norm_num [chi313Slice]
    onePlusPositive := by
      norm_num [chi313Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi313LogChi_valid }

noncomputable def chi313InputQChi : RationalEnclosure :=
  { lower := (-4407869/16777216), upper := (-4307197/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi313InputQChi_eq :
    chi313InputQChi = outerEnclosure 24 chi313QChiValue := by
  rfl'

theorem chi313RoundedFacts :
    ChiRoundedFacts 8 chi313Slice chi313LogChiCertificate
      chi313InputQChi :=
  { coversQChi := by
      rw [chi313InputQChi_eq, chi313QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi314Slice : ChiSlice :=
  { lo := (105/256), hi := (53/128) }

noncomputable def chi314LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (105/64) }, upper := { exponent := -2, mantissa := (53/32) } }

private noncomputable def chi314QChiValue : RationalEnclosure :=
  { lower := (-4101953789733543924236101763685300354993536519/15675037054262228511069590673618385766145496065), upper := (-1719898447332620865489339053460110250565762640515908667102668906466342445152835083/6725380607862018709992215144369684923415117961346769188422620455471640625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi314QChiValue_eq :
    chi314QChiValue =
      (chi314Slice.qChiAD 8 chi314LogChiCertificate).value := by
  norm_num [chi314QChiValue, chi314LogChiCertificate, chi314Slice,
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
private theorem chi314LogChi_valid :
    (if chi314Slice.lo = 0 then
      if chi314Slice.hi = 0 then true
      else decide (chi314Slice.hi ≤ 1 / 4) &&
        chi314LogChiCertificate.check
          (IntervalAD.const chi314Slice.hi).value
    else chi314LogChiCertificate.check
      chi314Slice.chiAD.value) = true := by
  norm_num [chi314Slice, chi314LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi314ValidityFacts :
    ChiFacts chi314Slice chi314LogChiCertificate :=
  { domain := by norm_num [chi314Slice]
    onePlusPositive := by
      norm_num [chi314Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi314LogChi_valid }

noncomputable def chi314InputQChi : RationalEnclosure :=
  { lower := (-1097595/4194304), upper := (-4290479/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi314InputQChi_eq :
    chi314InputQChi = outerEnclosure 24 chi314QChiValue := by
  rfl'

theorem chi314RoundedFacts :
    ChiRoundedFacts 8 chi314Slice chi314LogChiCertificate
      chi314InputQChi :=
  { coversQChi := by
      rw [chi314InputQChi_eq, chi314QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi315Slice : ChiSlice :=
  { lo := (53/128), hi := (107/256) }

noncomputable def chi315LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (53/32) }, upper := { exponent := -2, mantissa := (107/64) } }

private noncomputable def chi315QChiValue : RationalEnclosure :=
  { lower := (-3551252586066165357094367984040182265431129/13625944298090643638798829720027465820312500), upper := (-2505841581275985233491889739336185010746296882817986676866029925971235408421/9837812876225758695285182524215637554535695582499504463140922343750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi315QChiValue_eq :
    chi315QChiValue =
      (chi315Slice.qChiAD 8 chi315LogChiCertificate).value := by
  norm_num [chi315QChiValue, chi315LogChiCertificate, chi315Slice,
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
private theorem chi315LogChi_valid :
    (if chi315Slice.lo = 0 then
      if chi315Slice.hi = 0 then true
      else decide (chi315Slice.hi ≤ 1 / 4) &&
        chi315LogChiCertificate.check
          (IntervalAD.const chi315Slice.hi).value
    else chi315LogChiCertificate.check
      chi315Slice.chiAD.value) = true := by
  norm_num [chi315Slice, chi315LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi315ValidityFacts :
    ChiFacts chi315Slice chi315LogChiCertificate :=
  { domain := by norm_num [chi315Slice]
    onePlusPositive := by
      norm_num [chi315Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi315LogChi_valid }

noncomputable def chi315InputQChi : RationalEnclosure :=
  { lower := (-4372551/16777216), upper := (-4273413/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi315InputQChi_eq :
    chi315InputQChi = outerEnclosure 24 chi315QChiValue := by
  rfl'

theorem chi315RoundedFacts :
    ChiRoundedFacts 8 chi315Slice chi315LogChiCertificate
      chi315InputQChi :=
  { coversQChi := by
      rw [chi315InputQChi_eq, chi315QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi316Slice : ChiSlice :=
  { lo := (107/256), hi := (27/64) }

noncomputable def chi316LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (107/64) }, upper := { exponent := -2, mantissa := (27/16) } }

private noncomputable def chi316QChiValue : RationalEnclosure :=
  { lower := (-163763485625906440395853720047374227646/630971659833657513051867710718274365285), upper := (-14877357214849406225665463096954794040519193790299100251012316381169/58646668820464184693794287396382852532823784935259963679543951362560) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi316QChiValue_eq :
    chi316QChiValue =
      (chi316Slice.qChiAD 8 chi316LogChiCertificate).value := by
  norm_num [chi316QChiValue, chi316LogChiCertificate, chi316Slice,
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
private theorem chi316LogChi_valid :
    (if chi316Slice.lo = 0 then
      if chi316Slice.hi = 0 then true
      else decide (chi316Slice.hi ≤ 1 / 4) &&
        chi316LogChiCertificate.check
          (IntervalAD.const chi316Slice.hi).value
    else chi316LogChiCertificate.check
      chi316Slice.chiAD.value) = true := by
  norm_num [chi316Slice, chi316LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi316ValidityFacts :
    ChiFacts chi316Slice chi316LogChiCertificate :=
  { domain := by norm_num [chi316Slice]
    onePlusPositive := by
      norm_num [chi316Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi316LogChi_valid }

noncomputable def chi316InputQChi : RationalEnclosure :=
  { lower := (-1088597/4194304), upper := (-4256007/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi316InputQChi_eq :
    chi316InputQChi = outerEnclosure 24 chi316QChiValue := by
  rfl'

theorem chi316RoundedFacts :
    ChiRoundedFacts 8 chi316Slice chi316LogChiCertificate
      chi316InputQChi :=
  { coversQChi := by
      rw [chi316InputQChi_eq, chi316QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi317Slice : ChiSlice :=
  { lo := (27/64), hi := (109/256) }

noncomputable def chi317LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (27/16) }, upper := { exponent := -2, mantissa := (109/64) } }

private noncomputable def chi317QChiValue : RationalEnclosure :=
  { lower := (-128783894590189763431390707376411420561/498313175707643340730301233205531023080), upper := (-4771133454553703383946646630933308133243313189483810367834522797335552656035157/18886576625212744940318036227891539893919615259726887513833913826168080459417600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi317QChiValue_eq :
    chi317QChiValue =
      (chi317Slice.qChiAD 8 chi317LogChiCertificate).value := by
  norm_num [chi317QChiValue, chi317LogChiCertificate, chi317Slice,
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
private theorem chi317LogChi_valid :
    (if chi317Slice.lo = 0 then
      if chi317Slice.hi = 0 then true
      else decide (chi317Slice.hi ≤ 1 / 4) &&
        chi317LogChiCertificate.check
          (IntervalAD.const chi317Slice.hi).value
    else chi317LogChiCertificate.check
      chi317Slice.chiAD.value) = true := by
  norm_num [chi317Slice, chi317LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi317ValidityFacts :
    ChiFacts chi317Slice chi317LogChiCertificate :=
  { domain := by norm_num [chi317Slice]
    onePlusPositive := by
      norm_num [chi317Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi317LogChi_valid }

noncomputable def chi317InputQChi : RationalEnclosure :=
  { lower := (-4335899/16777216), upper := (-2119133/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi317InputQChi_eq :
    chi317InputQChi = outerEnclosure 24 chi317QChiValue := by
  rfl'

theorem chi317RoundedFacts :
    ChiRoundedFacts 8 chi317Slice chi317LogChiCertificate
      chi317InputQChi :=
  { coversQChi := by
      rw [chi317InputQChi_eq, chi317QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi318Slice : ChiSlice :=
  { lo := (109/256), hi := (55/128) }

noncomputable def chi318LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (109/64) }, upper := { exponent := -2, mantissa := (55/32) } }

private noncomputable def chi318QChiValue : RationalEnclosure :=
  { lower := (-1369105464915444108346793829122684802082412003/5320664552968498723241401621073358939373091355), upper := (-1526046847128925401295758280784450285636045550641372071319857972905088867/6066734383485600858077580260746548459822290676217188704290893412459430400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi318QChiValue_eq :
    chi318QChiValue =
      (chi318Slice.qChiAD 8 chi318LogChiCertificate).value := by
  norm_num [chi318QChiValue, chi318LogChiCertificate, chi318Slice,
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
private theorem chi318LogChi_valid :
    (if chi318Slice.lo = 0 then
      if chi318Slice.hi = 0 then true
      else decide (chi318Slice.hi ≤ 1 / 4) &&
        chi318LogChiCertificate.check
          (IntervalAD.const chi318Slice.hi).value
    else chi318LogChiCertificate.check
      chi318Slice.chiAD.value) = true := by
  norm_num [chi318Slice, chi318LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi318ValidityFacts :
    ChiFacts chi318Slice chi318LogChiCertificate :=
  { domain := by norm_num [chi318Slice]
    onePlusPositive := by
      norm_num [chi318Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi318LogChi_valid }

noncomputable def chi318InputQChi : RationalEnclosure :=
  { lower := (-4317089/16777216), upper := (-4220197/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi318InputQChi_eq :
    chi318InputQChi = outerEnclosure 24 chi318QChiValue := by
  rfl'

theorem chi318RoundedFacts :
    ChiRoundedFacts 8 chi318Slice chi318LogChiCertificate
      chi318InputQChi :=
  { coversQChi := by
      rw [chi318InputQChi_eq, chi318QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi319Slice : ChiSlice :=
  { lo := (55/128), hi := (111/256) }

noncomputable def chi319LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (55/32) }, upper := { exponent := -2, mantissa := (111/64) } }

private noncomputable def chi319QChiValue : RationalEnclosure :=
  { lower := (-16601556761913077958110635767361609/64804611611528664332315221997831340), upper := (-35637126115404483041001228894895079685303211796337376668050341347095019473/142293924031103495035235898795785164855803101333413124084472656250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi319QChiValue_eq :
    chi319QChiValue =
      (chi319Slice.qChiAD 8 chi319LogChiCertificate).value := by
  norm_num [chi319QChiValue, chi319LogChiCertificate, chi319Slice,
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
private theorem chi319LogChi_valid :
    (if chi319Slice.lo = 0 then
      if chi319Slice.hi = 0 then true
      else decide (chi319Slice.hi ≤ 1 / 4) &&
        chi319LogChiCertificate.check
          (IntervalAD.const chi319Slice.hi).value
    else chi319LogChiCertificate.check
      chi319Slice.chiAD.value) = true := by
  norm_num [chi319Slice, chi319LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi319ValidityFacts :
    ChiFacts chi319Slice chi319LogChiCertificate :=
  { domain := by norm_num [chi319Slice]
    onePlusPositive := by
      norm_num [chi319Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi319LogChi_valid }

noncomputable def chi319InputQChi : RationalEnclosure :=
  { lower := (-4297965/16777216), upper := (-262613/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi319InputQChi_eq :
    chi319InputQChi = outerEnclosure 24 chi319QChiValue := by
  rfl'

theorem chi319RoundedFacts :
    ChiRoundedFacts 8 chi319Slice chi319LogChiCertificate
      chi319InputQChi :=
  { coversQChi := by
      rw [chi319InputQChi_eq, chi319QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
