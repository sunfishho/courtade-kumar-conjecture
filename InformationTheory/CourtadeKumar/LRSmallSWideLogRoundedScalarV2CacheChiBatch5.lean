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

noncomputable def chi320Slice : ChiSlice :=
  { lo := (111/256), hi := (7/16) }

noncomputable def chi320LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (111/64) }, upper := { exponent := -2, mantissa := (7/4) } }

private noncomputable def chi320QChiValue : RationalEnclosure :=
  { lower := (-165412051113367275556142120952326135461402984/648622764193178439761786721646785736083984375), upper := (-7955345385562085976148300131181458199820626169216460468211044871/31906580403429019805661061831249111167447566986083984375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi320QChiValue_eq :
    chi320QChiValue =
      (chi320Slice.qChiAD 8 chi320LogChiCertificate).value := by
  norm_num [chi320QChiValue, chi320LogChiCertificate, chi320Slice,
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
private theorem chi320LogChi_valid :
    (if chi320Slice.lo = 0 then
      if chi320Slice.hi = 0 then true
      else decide (chi320Slice.hi ≤ 1 / 4) &&
        chi320LogChiCertificate.check
          (IntervalAD.const chi320Slice.hi).value
    else chi320LogChiCertificate.check
      chi320Slice.chiAD.value) = true := by
  norm_num [chi320Slice, chi320LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi320ValidityFacts :
    ChiFacts chi320Slice chi320LogChiCertificate :=
  { domain := by norm_num [chi320Slice]
    onePlusPositive := by
      norm_num [chi320Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi320LogChi_valid }

noncomputable def chi320InputQChi : RationalEnclosure :=
  { lower := (-4278533/16777216), upper := (-65361/262144) }

set_option maxRecDepth 1000000 in
private theorem chi320InputQChi_eq :
    chi320InputQChi = outerEnclosure 24 chi320QChiValue := by
  rfl'

theorem chi320RoundedFacts :
    ChiRoundedFacts 8 chi320Slice chi320LogChiCertificate
      chi320InputQChi :=
  { coversQChi := by
      rw [chi320InputQChi_eq, chi320QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi321Slice : ChiSlice :=
  { lo := (19/32), hi := (39/64) }

noncomputable def chi321LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (19/16) }, upper := { exponent := -1, mantissa := (39/32) } }

private noncomputable def chi321QChiValue : RationalEnclosure :=
  { lower := (-9298479749125314234724566767181419/46651148345991081263258056640625000), upper := (-12858220464821792719616626344783622861545096406641745675183838206543/70440004515425891541335788474362937927734938145196014609375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi321QChiValue_eq :
    chi321QChiValue =
      (chi321Slice.qChiAD 8 chi321LogChiCertificate).value := by
  norm_num [chi321QChiValue, chi321LogChiCertificate, chi321Slice,
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
private theorem chi321LogChi_valid :
    (if chi321Slice.lo = 0 then
      if chi321Slice.hi = 0 then true
      else decide (chi321Slice.hi ≤ 1 / 4) &&
        chi321LogChiCertificate.check
          (IntervalAD.const chi321Slice.hi).value
    else chi321LogChiCertificate.check
      chi321Slice.chiAD.value) = true := by
  norm_num [chi321Slice, chi321LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi321ValidityFacts :
    ChiFacts chi321Slice chi321LogChiCertificate :=
  { domain := by norm_num [chi321Slice]
    onePlusPositive := by
      norm_num [chi321Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi321LogChi_valid }

noncomputable def chi321InputQChi : RationalEnclosure :=
  { lower := (-3344025/16777216), upper := (-3062537/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi321InputQChi_eq :
    chi321InputQChi = outerEnclosure 24 chi321QChiValue := by
  rfl'

theorem chi321RoundedFacts :
    ChiRoundedFacts 8 chi321Slice chi321LogChiCertificate
      chi321InputQChi :=
  { coversQChi := by
      rw [chi321InputQChi_eq, chi321QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi322Slice : ChiSlice :=
  { lo := (39/64), hi := (5/8) }

noncomputable def chi322LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (39/32) }, upper := { exponent := -1, mantissa := (5/4) } }

private noncomputable def chi322QChiValue : RationalEnclosure :=
  { lower := (-5014140671483110133626668294858790526530/26066733298453928457058650640770445259913), upper := (-121752124345061790315954391993424221192542971638273/691538306078313617321933501250669775072721357679360) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi322QChiValue_eq :
    chi322QChiValue =
      (chi322Slice.qChiAD 8 chi322LogChiCertificate).value := by
  norm_num [chi322QChiValue, chi322LogChiCertificate, chi322Slice,
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
private theorem chi322LogChi_valid :
    (if chi322Slice.lo = 0 then
      if chi322Slice.hi = 0 then true
      else decide (chi322Slice.hi ≤ 1 / 4) &&
        chi322LogChiCertificate.check
          (IntervalAD.const chi322Slice.hi).value
    else chi322LogChiCertificate.check
      chi322Slice.chiAD.value) = true := by
  norm_num [chi322Slice, chi322LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi322ValidityFacts :
    ChiFacts chi322Slice chi322LogChiCertificate :=
  { domain := by norm_num [chi322Slice]
    onePlusPositive := by
      norm_num [chi322Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi322LogChi_valid }

noncomputable def chi322InputQChi : RationalEnclosure :=
  { lower := (-1613615/8388608), upper := (-2953793/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi322InputQChi_eq :
    chi322InputQChi = outerEnclosure 24 chi322QChiValue := by
  rfl'

theorem chi322RoundedFacts :
    ChiRoundedFacts 8 chi322Slice chi322LogChiCertificate
      chi322InputQChi :=
  { coversQChi := by
      rw [chi322InputQChi_eq, chi322QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi323Slice : ChiSlice :=
  { lo := (5/8), hi := (41/64) }

noncomputable def chi323LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (5/4) }, upper := { exponent := -1, mantissa := (41/32) } }

private noncomputable def chi323QChiValue : RationalEnclosure :=
  { lower := (-238291226598017740501/1286045424934880369760), upper := (-178316535598932885604373626523783047942650132382187267/1052279441476915728411827215284226789757631322073548800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi323QChiValue_eq :
    chi323QChiValue =
      (chi323Slice.qChiAD 8 chi323LogChiCertificate).value := by
  norm_num [chi323QChiValue, chi323LogChiCertificate, chi323Slice,
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
private theorem chi323LogChi_valid :
    (if chi323Slice.lo = 0 then
      if chi323Slice.hi = 0 then true
      else decide (chi323Slice.hi ≤ 1 / 4) &&
        chi323LogChiCertificate.check
          (IntervalAD.const chi323Slice.hi).value
    else chi323LogChiCertificate.check
      chi323Slice.chiAD.value) = true := by
  norm_num [chi323Slice, chi323LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi323ValidityFacts :
    ChiFacts chi323Slice chi323LogChiCertificate :=
  { domain := by norm_num [chi323Slice]
    onePlusPositive := by
      norm_num [chi323Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi323LogChi_valid }

noncomputable def chi323InputQChi : RationalEnclosure :=
  { lower := (-3108649/16777216), upper := (-2843023/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi323InputQChi_eq :
    chi323InputQChi = outerEnclosure 24 chi323QChiValue := by
  rfl'

theorem chi323RoundedFacts :
    ChiRoundedFacts 8 chi323Slice chi323LogChiCertificate
      chi323InputQChi :=
  { coversQChi := by
      rw [chi323InputQChi_eq, chi323QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi324Slice : ChiSlice :=
  { lo := (41/64), hi := (21/32) }

noncomputable def chi324LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (41/32) }, upper := { exponent := -1, mantissa := (21/16) } }

private noncomputable def chi324QChiValue : RationalEnclosure :=
  { lower := (-3419089787890597469663383762079319418351/19194953268647854941928575923276439044850), upper := (-21199416477261952864412381368685479471211225061958062832129160776493/130262681525693438406995921379562999266158744997836984173567981689600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi324QChiValue_eq :
    chi324QChiValue =
      (chi324Slice.qChiAD 8 chi324LogChiCertificate).value := by
  norm_num [chi324QChiValue, chi324LogChiCertificate, chi324Slice,
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
private theorem chi324LogChi_valid :
    (if chi324Slice.lo = 0 then
      if chi324Slice.hi = 0 then true
      else decide (chi324Slice.hi ≤ 1 / 4) &&
        chi324LogChiCertificate.check
          (IntervalAD.const chi324Slice.hi).value
    else chi324LogChiCertificate.check
      chi324Slice.chiAD.value) = true := by
  norm_num [chi324Slice, chi324LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi324ValidityFacts :
    ChiFacts chi324Slice chi324LogChiCertificate :=
  { domain := by norm_num [chi324Slice]
    onePlusPositive := by
      norm_num [chi324Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi324LogChi_valid }

noncomputable def chi324InputQChi : RationalEnclosure :=
  { lower := (-186777/1048576), upper := (-170649/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi324InputQChi_eq :
    chi324InputQChi = outerEnclosure 24 chi324QChiValue := by
  rfl'

theorem chi324RoundedFacts :
    ChiRoundedFacts 8 chi324Slice chi324LogChiCertificate
      chi324InputQChi :=
  { coversQChi := by
      rw [chi324InputQChi_eq, chi324QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi325Slice : ChiSlice :=
  { lo := (21/32), hi := (43/64) }

noncomputable def chi325LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (21/16) }, upper := { exponent := -1, mantissa := (43/32) } }

private noncomputable def chi325QChiValue : RationalEnclosure :=
  { lower := (-473160021638675879869857626621118011/2769129012270314705981740918481912760), upper := (-260507490524041122392267036444195948408799521290310741919916643/1670698981762086124234698887172795375542163848876953125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi325QChiValue_eq :
    chi325QChiValue =
      (chi325Slice.qChiAD 8 chi325LogChiCertificate).value := by
  norm_num [chi325QChiValue, chi325LogChiCertificate, chi325Slice,
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
private theorem chi325LogChi_valid :
    (if chi325Slice.lo = 0 then
      if chi325Slice.hi = 0 then true
      else decide (chi325Slice.hi ≤ 1 / 4) &&
        chi325LogChiCertificate.check
          (IntervalAD.const chi325Slice.hi).value
    else chi325LogChiCertificate.check
      chi325Slice.chiAD.value) = true := by
  norm_num [chi325Slice, chi325LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi325ValidityFacts :
    ChiFacts chi325Slice chi325LogChiCertificate :=
  { domain := by norm_num [chi325Slice]
    onePlusPositive := by
      norm_num [chi325Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi325LogChi_valid }

noncomputable def chi325InputQChi : RationalEnclosure :=
  { lower := (-2866717/16777216), upper := (-2616025/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi325InputQChi_eq :
    chi325InputQChi = outerEnclosure 24 chi325QChiValue := by
  rfl'

theorem chi325RoundedFacts :
    ChiRoundedFacts 8 chi325Slice chi325LogChiCertificate
      chi325InputQChi :=
  { coversQChi := by
      rw [chi325InputQChi_eq, chi325QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi326Slice : ChiSlice :=
  { lo := (43/64), hi := (11/16) }

noncomputable def chi326LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (43/32) }, upper := { exponent := -1, mantissa := (11/8) } }

private noncomputable def chi326QChiValue : RationalEnclosure :=
  { lower := (-45597732627196380096728104335881/278828613976947963237762451171875), upper := (-3391058210882213023213677696410590183743243446802079021/22756245702478690509299703729354143142700195312500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi326QChiValue_eq :
    chi326QChiValue =
      (chi326Slice.qChiAD 8 chi326LogChiCertificate).value := by
  norm_num [chi326QChiValue, chi326LogChiCertificate, chi326Slice,
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
private theorem chi326LogChi_valid :
    (if chi326Slice.lo = 0 then
      if chi326Slice.hi = 0 then true
      else decide (chi326Slice.hi ≤ 1 / 4) &&
        chi326LogChiCertificate.check
          (IntervalAD.const chi326Slice.hi).value
    else chi326LogChiCertificate.check
      chi326Slice.chiAD.value) = true := by
  norm_num [chi326Slice, chi326LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi326ValidityFacts :
    ChiFacts chi326Slice chi326LogChiCertificate :=
  { domain := by norm_num [chi326Slice]
    onePlusPositive := by
      norm_num [chi326Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi326LogChi_valid }

noncomputable def chi326InputQChi : RationalEnclosure :=
  { lower := (-171477/1048576), upper := (-2500083/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi326InputQChi_eq :
    chi326InputQChi = outerEnclosure 24 chi326QChiValue := by
  rfl'

theorem chi326RoundedFacts :
    ChiRoundedFacts 8 chi326Slice chi326LogChiCertificate
      chi326InputQChi :=
  { coversQChi := by
      rw [chi326InputQChi_eq, chi326QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi327Slice : ChiSlice :=
  { lo := (17/32), hi := (69/128) }

noncomputable def chi327LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (17/16) }, upper := { exponent := -1, mantissa := (69/64) } }

private noncomputable def chi327QChiValue : RationalEnclosure :=
  { lower := (-952216281369487878968904629/4276284127671054563252396208), upper := (-3889360493880405685730984048725749565033165672160437155989204479/18239760178954596299189066931573261973290891848198240178073896960) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi327QChiValue_eq :
    chi327QChiValue =
      (chi327Slice.qChiAD 8 chi327LogChiCertificate).value := by
  norm_num [chi327QChiValue, chi327LogChiCertificate, chi327Slice,
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
private theorem chi327LogChi_valid :
    (if chi327Slice.lo = 0 then
      if chi327Slice.hi = 0 then true
      else decide (chi327Slice.hi ≤ 1 / 4) &&
        chi327LogChiCertificate.check
          (IntervalAD.const chi327Slice.hi).value
    else chi327LogChiCertificate.check
      chi327Slice.chiAD.value) = true := by
  norm_num [chi327Slice, chi327LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi327ValidityFacts :
    ChiFacts chi327Slice chi327LogChiCertificate :=
  { domain := by norm_num [chi327Slice]
    onePlusPositive := by
      norm_num [chi327Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi327LogChi_valid }

noncomputable def chi327InputQChi : RationalEnclosure :=
  { lower := (-1867923/8388608), upper := (-1788747/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi327InputQChi_eq :
    chi327InputQChi = outerEnclosure 24 chi327QChiValue := by
  rfl'

theorem chi327RoundedFacts :
    ChiRoundedFacts 8 chi327Slice chi327LogChiCertificate
      chi327InputQChi :=
  { coversQChi := by
      rw [chi327InputQChi_eq, chi327QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi328Slice : ChiSlice :=
  { lo := (69/128), hi := (35/64) }

noncomputable def chi328LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (69/64) }, upper := { exponent := -1, mantissa := (35/32) } }

private noncomputable def chi328QChiValue : RationalEnclosure :=
  { lower := (-5482966961130137468328667363668807820706029/24971746025292904399186573248741910642455282), upper := (-16031590784797647228525046098509415937237154379131811738216330725794887307/76244428290781175981960654835052410573332700935552595040071416885660729856) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi328QChiValue_eq :
    chi328QChiValue =
      (chi328Slice.qChiAD 8 chi328LogChiCertificate).value := by
  norm_num [chi328QChiValue, chi328LogChiCertificate, chi328Slice,
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
private theorem chi328LogChi_valid :
    (if chi328Slice.lo = 0 then
      if chi328Slice.hi = 0 then true
      else decide (chi328Slice.hi ≤ 1 / 4) &&
        chi328LogChiCertificate.check
          (IntervalAD.const chi328Slice.hi).value
    else chi328LogChiCertificate.check
      chi328Slice.chiAD.value) = true := by
  norm_num [chi328Slice, chi328LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi328ValidityFacts :
    ChiFacts chi328Slice chi328LogChiCertificate :=
  { domain := by norm_num [chi328Slice]
    onePlusPositive := by
      norm_num [chi328Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi328LogChi_valid }

noncomputable def chi328InputQChi : RationalEnclosure :=
  { lower := (-3683721/16777216), upper := (-3527673/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi328InputQChi_eq :
    chi328InputQChi = outerEnclosure 24 chi328QChiValue := by
  rfl'

theorem chi328RoundedFacts :
    ChiRoundedFacts 8 chi328Slice chi328LogChiCertificate
      chi328InputQChi :=
  { coversQChi := by
      rw [chi328InputQChi_eq, chi328QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi329Slice : ChiSlice :=
  { lo := (1/2), hi := (65/128) }

noncomputable def chi329LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (1) }, upper := { exponent := -1, mantissa := (65/64) } }

private noncomputable def chi329QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2545610893056), upper := (-13569468795370621511473202041514331480175/60403350600431158935984192172272225189888) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi329QChiValue_eq :
    chi329QChiValue =
      (chi329Slice.qChiAD 8 chi329LogChiCertificate).value := by
  norm_num [chi329QChiValue, chi329LogChiCertificate, chi329Slice,
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
private theorem chi329LogChi_valid :
    (if chi329Slice.lo = 0 then
      if chi329Slice.hi = 0 then true
      else decide (chi329Slice.hi ≤ 1 / 4) &&
        chi329LogChiCertificate.check
          (IntervalAD.const chi329Slice.hi).value
    else chi329LogChiCertificate.check
      chi329Slice.chiAD.value) = true := by
  norm_num [chi329Slice, chi329LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi329ValidityFacts :
    ChiFacts chi329Slice chi329LogChiCertificate :=
  { domain := by norm_num [chi329Slice]
    onePlusPositive := by
      norm_num [chi329Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi329LogChi_valid }

noncomputable def chi329InputQChi : RationalEnclosure :=
  { lower := (-3936929/16777216), upper := (-3768961/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi329InputQChi_eq :
    chi329InputQChi = outerEnclosure 24 chi329QChiValue := by
  rfl'

theorem chi329RoundedFacts :
    ChiRoundedFacts 8 chi329Slice chi329LogChiCertificate
      chi329InputQChi :=
  { coversQChi := by
      rw [chi329InputQChi_eq, chi329QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi330Slice : ChiSlice :=
  { lo := (65/128), hi := (33/64) }

noncomputable def chi330LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (65/64) }, upper := { exponent := -1, mantissa := (33/32) } }

private noncomputable def chi330QChiValue : RationalEnclosure :=
  { lower := (-88351240326021755689235879984526241/381263351377095780255253230930448470), upper := (-6478258426265571978910736000652310921288097266057482157891453737551/29198680668035985679046064065178884970979657220831906953125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi330QChiValue_eq :
    chi330QChiValue =
      (chi330Slice.qChiAD 8 chi330LogChiCertificate).value := by
  norm_num [chi330QChiValue, chi330LogChiCertificate, chi330Slice,
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
private theorem chi330LogChi_valid :
    (if chi330Slice.lo = 0 then
      if chi330Slice.hi = 0 then true
      else decide (chi330Slice.hi ≤ 1 / 4) &&
        chi330LogChiCertificate.check
          (IntervalAD.const chi330Slice.hi).value
    else chi330LogChiCertificate.check
      chi330Slice.chiAD.value) = true := by
  norm_num [chi330Slice, chi330LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi330ValidityFacts :
    ChiFacts chi330Slice chi330LogChiCertificate :=
  { domain := by norm_num [chi330Slice]
    onePlusPositive := by
      norm_num [chi330Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi330LogChi_valid }

noncomputable def chi330InputQChi : RationalEnclosure :=
  { lower := (-485979/2097152), upper := (-1861165/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi330InputQChi_eq :
    chi330InputQChi = outerEnclosure 24 chi330QChiValue := by
  rfl'

theorem chi330RoundedFacts :
    ChiRoundedFacts 8 chi330Slice chi330LogChiCertificate
      chi330InputQChi :=
  { coversQChi := by
      rw [chi330InputQChi_eq, chi330QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi331Slice : ChiSlice :=
  { lo := (33/64), hi := (67/128) }

noncomputable def chi331LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (33/32) }, upper := { exponent := -1, mantissa := (67/64) } }

private noncomputable def chi331QChiValue : RationalEnclosure :=
  { lower := (-4595578978288677694560619716733056518921/20089210799955430064685651602783203125000), upper := (-422543944052159379487264241221263168770285988989865373244719599770239970090069/1929086467487449925868806794686818903938937895448844177445175905468750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi331QChiValue_eq :
    chi331QChiValue =
      (chi331Slice.qChiAD 8 chi331LogChiCertificate).value := by
  norm_num [chi331QChiValue, chi331LogChiCertificate, chi331Slice,
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
private theorem chi331LogChi_valid :
    (if chi331Slice.lo = 0 then
      if chi331Slice.hi = 0 then true
      else decide (chi331Slice.hi ≤ 1 / 4) &&
        chi331LogChiCertificate.check
          (IntervalAD.const chi331Slice.hi).value
    else chi331LogChiCertificate.check
      chi331Slice.chiAD.value) = true := by
  norm_num [chi331Slice, chi331LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi331ValidityFacts :
    ChiFacts chi331Slice chi331LogChiCertificate :=
  { domain := by norm_num [chi331Slice]
    onePlusPositive := by
      norm_num [chi331Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi331LogChi_valid }

noncomputable def chi331InputQChi : RationalEnclosure :=
  { lower := (-959483/4194304), upper := (-3674853/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi331InputQChi_eq :
    chi331InputQChi = outerEnclosure 24 chi331QChiValue := by
  rfl'

theorem chi331RoundedFacts :
    ChiRoundedFacts 8 chi331Slice chi331LogChiCertificate
      chi331InputQChi :=
  { coversQChi := by
      rw [chi331InputQChi_eq, chi331QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi332Slice : ChiSlice :=
  { lo := (67/128), hi := (17/32) }

noncomputable def chi332LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (67/64) }, upper := { exponent := -1, mantissa := (17/16) } }

private noncomputable def chi332QChiValue : RationalEnclosure :=
  { lower := (-544569581728881031498576820264581194377457181/2412393799400195516268988262249298790470091725), upper := (-4968066170342892636124383717510545883493430340626887078968292417/22983270937146301056971191772081278849240303306692575204482828800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi332QChiValue_eq :
    chi332QChiValue =
      (chi332Slice.qChiAD 8 chi332LogChiCertificate).value := by
  norm_num [chi332QChiValue, chi332LogChiCertificate, chi332Slice,
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
private theorem chi332LogChi_valid :
    (if chi332Slice.lo = 0 then
      if chi332Slice.hi = 0 then true
      else decide (chi332Slice.hi ≤ 1 / 4) &&
        chi332LogChiCertificate.check
          (IntervalAD.const chi332Slice.hi).value
    else chi332LogChiCertificate.check
      chi332Slice.chiAD.value) = true := by
  norm_num [chi332Slice, chi332LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi332ValidityFacts :
    ChiFacts chi332Slice chi332LogChiCertificate :=
  { domain := by norm_num [chi332Slice]
    onePlusPositive := by
      norm_num [chi332Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi332LogChi_valid }

noncomputable def chi332InputQChi : RationalEnclosure :=
  { lower := (-946815/4194304), upper := (-906641/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi332InputQChi_eq :
    chi332InputQChi = outerEnclosure 24 chi332QChiValue := by
  rfl'

theorem chi332RoundedFacts :
    ChiRoundedFacts 8 chi332Slice chi332LogChiCertificate
      chi332InputQChi :=
  { coversQChi := by
      rw [chi332InputQChi_eq, chi332QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi333Slice : ChiSlice :=
  { lo := (35/64), hi := (71/128) }

noncomputable def chi333LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (35/32) }, upper := { exponent := -1, mantissa := (71/64) } }

private noncomputable def chi333QChiValue : RationalEnclosure :=
  { lower := (-90883914836261101019679202570985631281819/419943998864391438954200477807144783531880), upper := (-329670779672015480551846575255314150426513564844854977449183880402492399/1590666834563538777731812496104289335458748348457118530059218750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi333QChiValue_eq :
    chi333QChiValue =
      (chi333Slice.qChiAD 8 chi333LogChiCertificate).value := by
  norm_num [chi333QChiValue, chi333LogChiCertificate, chi333Slice,
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
private theorem chi333LogChi_valid :
    (if chi333Slice.lo = 0 then
      if chi333Slice.hi = 0 then true
      else decide (chi333Slice.hi ≤ 1 / 4) &&
        chi333LogChiCertificate.check
          (IntervalAD.const chi333Slice.hi).value
    else chi333LogChiCertificate.check
      chi333Slice.chiAD.value) = true := by
  norm_num [chi333Slice, chi333LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi333ValidityFacts :
    ChiFacts chi333Slice chi333LogChiCertificate :=
  { domain := by norm_num [chi333Slice]
    onePlusPositive := by
      norm_num [chi333Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi333LogChi_valid }

noncomputable def chi333InputQChi : RationalEnclosure :=
  { lower := (-3630911/16777216), upper := (-3477131/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi333InputQChi_eq :
    chi333InputQChi = outerEnclosure 24 chi333QChiValue := by
  rfl'

theorem chi333RoundedFacts :
    ChiRoundedFacts 8 chi333Slice chi333LogChiCertificate
      chi333InputQChi :=
  { coversQChi := by
      rw [chi333InputQChi_eq, chi333QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi334Slice : ChiSlice :=
  { lo := (71/128), hi := (9/16) }

noncomputable def chi334LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (71/64) }, upper := { exponent := -1, mantissa := (9/8) } }

private noncomputable def chi334QChiValue : RationalEnclosure :=
  { lower := (-6382567787234468049379593557826110662/29932461386729915463052722015380859375), upper := (-671833734094798964578052483584748435477617568582652890920433/3290087710533241999527976007183636509219945119140625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi334QChiValue_eq :
    chi334QChiValue =
      (chi334Slice.qChiAD 8 chi334LogChiCertificate).value := by
  norm_num [chi334QChiValue, chi334LogChiCertificate, chi334Slice,
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
private theorem chi334LogChi_valid :
    (if chi334Slice.lo = 0 then
      if chi334Slice.hi = 0 then true
      else decide (chi334Slice.hi ≤ 1 / 4) &&
        chi334LogChiCertificate.check
          (IntervalAD.const chi334Slice.hi).value
    else chi334LogChiCertificate.check
      chi334Slice.chiAD.value) = true := by
  norm_num [chi334Slice, chi334LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi334ValidityFacts :
    ChiFacts chi334Slice chi334LogChiCertificate :=
  { domain := by norm_num [chi334Slice]
    onePlusPositive := by
      norm_num [chi334Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi334LogChi_valid }

noncomputable def chi334InputQChi : RationalEnclosure :=
  { lower := (-3577445/16777216), upper := (-428237/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi334InputQChi_eq :
    chi334InputQChi = outerEnclosure 24 chi334QChiValue := by
  rfl'

theorem chi334RoundedFacts :
    ChiRoundedFacts 8 chi334Slice chi334LogChiCertificate
      chi334InputQChi :=
  { coversQChi := by
      rw [chi334InputQChi_eq, chi334QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi335Slice : ChiSlice :=
  { lo := (9/16), hi := (73/128) }

noncomputable def chi335LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (9/8) }, upper := { exponent := -1, mantissa := (73/64) } }

private noncomputable def chi335QChiValue : RationalEnclosure :=
  { lower := (-14801495456888989113537404647961/70480653947882274783924238716000), upper := (-20947390878664962709415639704320963438073732248797651054900937929405531/104161052484807610372950681591417761626307185057719628690692167483904000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi335QChiValue_eq :
    chi335QChiValue =
      (chi335Slice.qChiAD 8 chi335LogChiCertificate).value := by
  norm_num [chi335QChiValue, chi335LogChiCertificate, chi335Slice,
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
private theorem chi335LogChi_valid :
    (if chi335Slice.lo = 0 then
      if chi335Slice.hi = 0 then true
      else decide (chi335Slice.hi ≤ 1 / 4) &&
        chi335LogChiCertificate.check
          (IntervalAD.const chi335Slice.hi).value
    else chi335LogChiCertificate.check
      chi335Slice.chiAD.value) = true := by
  norm_num [chi335Slice, chi335LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi335ValidityFacts :
    ChiFacts chi335Slice chi335LogChiCertificate :=
  { domain := by norm_num [chi335Slice]
    onePlusPositive := by
      norm_num [chi335Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi335LogChi_valid }

noncomputable def chi335InputQChi : RationalEnclosure :=
  { lower := (-3523349/16777216), upper := (-3373995/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi335InputQChi_eq :
    chi335InputQChi = outerEnclosure 24 chi335QChiValue := by
  rfl'

theorem chi335RoundedFacts :
    ChiRoundedFacts 8 chi335Slice chi335LogChiCertificate
      chi335InputQChi :=
  { coversQChi := by
      rw [chi335InputQChi_eq, chi335QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi336Slice : ChiSlice :=
  { lo := (73/128), hi := (37/64) }

noncomputable def chi336LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (73/64) }, upper := { exponent := -1, mantissa := (37/32) } }

private noncomputable def chi336QChiValue : RationalEnclosure :=
  { lower := (-36597906103773704273541113110689410145863693/177017428795535110051584624757447906447550646), upper := (-491663216634446296593427463585454766903331496627718160776525148372795053/2483472304772634211814957663285372936443804473344471748139321409022789120) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi336QChiValue_eq :
    chi336QChiValue =
      (chi336Slice.qChiAD 8 chi336LogChiCertificate).value := by
  norm_num [chi336QChiValue, chi336LogChiCertificate, chi336Slice,
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
private theorem chi336LogChi_valid :
    (if chi336Slice.lo = 0 then
      if chi336Slice.hi = 0 then true
      else decide (chi336Slice.hi ≤ 1 / 4) &&
        chi336LogChiCertificate.check
          (IntervalAD.const chi336Slice.hi).value
    else chi336LogChiCertificate.check
      chi336Slice.chiAD.value) = true := by
  norm_num [chi336Slice, chi336LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi336ValidityFacts :
    ChiFacts chi336Slice chi336LogChiCertificate :=
  { domain := by norm_num [chi336Slice]
    onePlusPositive := by
      norm_num [chi336Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi336LogChi_valid }

noncomputable def chi336InputQChi : RationalEnclosure :=
  { lower := (-433581/2097152), upper := (-1660727/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi336InputQChi_eq :
    chi336InputQChi = outerEnclosure 24 chi336QChiValue := by
  rfl'

theorem chi336RoundedFacts :
    ChiRoundedFacts 8 chi336Slice chi336LogChiCertificate
      chi336InputQChi :=
  { coversQChi := by
      rw [chi336InputQChi_eq, chi336QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi337Slice : ChiSlice :=
  { lo := (37/64), hi := (75/128) }

noncomputable def chi337LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (37/32) }, upper := { exponent := -1, mantissa := (75/64) } }

private noncomputable def chi337QChiValue : RationalEnclosure :=
  { lower := (-209856974159161448079181953841255/1031479365868329594957351694947864), upper := (-3647207118927456315924737616137790621041206826989045701865388312694421/18722272424760694979502302395149020914806030392788031307852937414917120) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi337QChiValue_eq :
    chi337QChiValue =
      (chi337Slice.qChiAD 8 chi337LogChiCertificate).value := by
  norm_num [chi337QChiValue, chi337LogChiCertificate, chi337Slice,
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
private theorem chi337LogChi_valid :
    (if chi337Slice.lo = 0 then
      if chi337Slice.hi = 0 then true
      else decide (chi337Slice.hi ≤ 1 / 4) &&
        chi337LogChiCertificate.check
          (IntervalAD.const chi337Slice.hi).value
    else chi337LogChiCertificate.check
      chi337Slice.chiAD.value) = true := by
  norm_num [chi337Slice, chi337LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi337ValidityFacts :
    ChiFacts chi337Slice chi337LogChiCertificate :=
  { domain := by norm_num [chi337Slice]
    onePlusPositive := by
      norm_num [chi337Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi337LogChi_valid }

noncomputable def chi337InputQChi : RationalEnclosure :=
  { lower := (-1706683/8388608), upper := (-1634149/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi337InputQChi_eq :
    chi337InputQChi = outerEnclosure 24 chi337QChiValue := by
  rfl'

theorem chi337RoundedFacts :
    ChiRoundedFacts 8 chi337Slice chi337LogChiCertificate
      chi337InputQChi :=
  { coversQChi := by
      rw [chi337InputQChi_eq, chi337QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi338Slice : ChiSlice :=
  { lo := (75/128), hi := (19/32) }

noncomputable def chi338LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (75/64) }, upper := { exponent := -1, mantissa := (19/16) } }

private noncomputable def chi338QChiValue : RationalEnclosure :=
  { lower := (-1222817719060408144154759333739153162804667663/6110295294427419341199148977082731363853604685), upper := (-132110660000803085018488242604154791862872099276212238195014529587631039/689504603336659975293598448074529671322611652046870984536484375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi338QChiValue_eq :
    chi338QChiValue =
      (chi338Slice.qChiAD 8 chi338LogChiCertificate).value := by
  norm_num [chi338QChiValue, chi338LogChiCertificate, chi338Slice,
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
private theorem chi338LogChi_valid :
    (if chi338Slice.lo = 0 then
      if chi338Slice.hi = 0 then true
      else decide (chi338Slice.hi ≤ 1 / 4) &&
        chi338LogChiCertificate.check
          (IntervalAD.const chi338Slice.hi).value
    else chi338LogChiCertificate.check
      chi338Slice.chiAD.value) = true := by
  norm_num [chi338Slice, chi338LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi338ValidityFacts :
    ChiFacts chi338Slice chi338LogChiCertificate :=
  { domain := by norm_num [chi338Slice]
    onePlusPositive := by
      norm_num [chi338Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi338LogChi_valid }

noncomputable def chi338InputQChi : RationalEnclosure :=
  { lower := (-3357527/16777216), upper := (-401819/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi338InputQChi_eq :
    chi338InputQChi = outerEnclosure 24 chi338QChiValue := by
  rfl'

theorem chi338RoundedFacts :
    ChiRoundedFacts 8 chi338Slice chi338LogChiCertificate
      chi338InputQChi :=
  { coversQChi := by
      rw [chi338InputQChi_eq, chi338QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi339Slice : ChiSlice :=
  { lo := (19/32), hi := (77/128) }

noncomputable def chi339LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (19/16) }, upper := { exponent := -1, mantissa := (77/64) } }

private noncomputable def chi339QChiValue : RationalEnclosure :=
  { lower := (-715267673009639556517274366706263/3635154416570733604929199218750000), upper := (-216964575174053824695030927491902424258354226025452609437051559653/1151830677104789872152969887249901577042757164838245312500000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi339QChiValue_eq :
    chi339QChiValue =
      (chi339Slice.qChiAD 8 chi339LogChiCertificate).value := by
  norm_num [chi339QChiValue, chi339LogChiCertificate, chi339Slice,
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
private theorem chi339LogChi_valid :
    (if chi339Slice.lo = 0 then
      if chi339Slice.hi = 0 then true
      else decide (chi339Slice.hi ≤ 1 / 4) &&
        chi339LogChiCertificate.check
          (IntervalAD.const chi339Slice.hi).value
    else chi339LogChiCertificate.check
      chi339Slice.chiAD.value) = true := by
  norm_num [chi339Slice, chi339LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi339ValidityFacts :
    ChiFacts chi339Slice chi339LogChiCertificate :=
  { domain := by norm_num [chi339Slice]
    onePlusPositive := by
      norm_num [chi339Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi339LogChi_valid }

noncomputable def chi339InputQChi : RationalEnclosure :=
  { lower := (-3301153/16777216), upper := (-197515/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi339InputQChi_eq :
    chi339InputQChi = outerEnclosure 24 chi339QChiValue := by
  rfl'

theorem chi339RoundedFacts :
    ChiRoundedFacts 8 chi339Slice chi339LogChiCertificate
      chi339InputQChi :=
  { coversQChi := by
      rw [chi339InputQChi_eq, chi339QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi340Slice : ChiSlice :=
  { lo := (77/128), hi := (39/64) }

noncomputable def chi340LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (77/64) }, upper := { exponent := -1, mantissa := (39/32) } }

private noncomputable def chi340QChiValue : RationalEnclosure :=
  { lower := (-5283575543945240538220074575136874249/27323182068395745609332218438028942850), upper := (-783211320979428321811187576038853697345902203223579195947433029228723/4231396250267674779908024391716104935551625328747670393810410256908800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi340QChiValue_eq :
    chi340QChiValue =
      (chi340Slice.qChiAD 8 chi340LogChiCertificate).value := by
  norm_num [chi340QChiValue, chi340LogChiCertificate, chi340Slice,
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
private theorem chi340LogChi_valid :
    (if chi340Slice.lo = 0 then
      if chi340Slice.hi = 0 then true
      else decide (chi340Slice.hi ≤ 1 / 4) &&
        chi340LogChiCertificate.check
          (IntervalAD.const chi340Slice.hi).value
    else chi340LogChiCertificate.check
      chi340Slice.chiAD.value) = true := by
  norm_num [chi340Slice, chi340LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi340ValidityFacts :
    ChiFacts chi340Slice chi340LogChiCertificate :=
  { domain := by norm_num [chi340Slice]
    onePlusPositive := by
      norm_num [chi340Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi340LogChi_valid }

noncomputable def chi340InputQChi : RationalEnclosure :=
  { lower := (-3244267/16777216), upper := (-1552691/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi340InputQChi_eq :
    chi340InputQChi = outerEnclosure 24 chi340QChiValue := by
  rfl'

theorem chi340RoundedFacts :
    ChiRoundedFacts 8 chi340Slice chi340LogChiCertificate
      chi340InputQChi :=
  { coversQChi := by
      rw [chi340InputQChi_eq, chi340QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi341Slice : ChiSlice :=
  { lo := (11/16), hi := (45/64) }

noncomputable def chi341LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (11/8) }, upper := { exponent := -1, mantissa := (45/32) } }

private noncomputable def chi341QChiValue : RationalEnclosure :=
  { lower := (-4902123887115851890186258475485/31399259398094384947950523515792), upper := (-7358001469251714393448046214957846393839479949999943266198293/51809865249624752426446215329981517013725750668617892590986240) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi341QChiValue_eq :
    chi341QChiValue =
      (chi341Slice.qChiAD 8 chi341LogChiCertificate).value := by
  norm_num [chi341QChiValue, chi341LogChiCertificate, chi341Slice,
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
private theorem chi341LogChi_valid :
    (if chi341Slice.lo = 0 then
      if chi341Slice.hi = 0 then true
      else decide (chi341Slice.hi ≤ 1 / 4) &&
        chi341LogChiCertificate.check
          (IntervalAD.const chi341Slice.hi).value
    else chi341LogChiCertificate.check
      chi341Slice.chiAD.value) = true := by
  norm_num [chi341Slice, chi341LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi341ValidityFacts :
    ChiFacts chi341Slice chi341LogChiCertificate :=
  { domain := by norm_num [chi341Slice]
    onePlusPositive := by
      norm_num [chi341Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi341LogChi_valid }

noncomputable def chi341InputQChi : RationalEnclosure :=
  { lower := (-1309649/8388608), upper := (-74459/524288) }

set_option maxRecDepth 1000000 in
private theorem chi341InputQChi_eq :
    chi341InputQChi = outerEnclosure 24 chi341QChiValue := by
  rfl'

theorem chi341RoundedFacts :
    ChiRoundedFacts 8 chi341Slice chi341LogChiCertificate
      chi341InputQChi :=
  { coversQChi := by
      rw [chi341InputQChi_eq, chi341QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi342Slice : ChiSlice :=
  { lo := (45/64), hi := (23/32) }

noncomputable def chi342LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (45/32) }, upper := { exponent := -1, mantissa := (23/16) } }

private noncomputable def chi342QChiValue : RationalEnclosure :=
  { lower := (-1798112673185706489010882587327201123161/12096808438677819569310873723252141347010), upper := (-80054154510011934346275964373568486792611826562300485775567/593246081765455601986847010889098884618388103404435534777600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi342QChiValue_eq :
    chi342QChiValue =
      (chi342Slice.qChiAD 8 chi342LogChiCertificate).value := by
  norm_num [chi342QChiValue, chi342LogChiCertificate, chi342Slice,
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
private theorem chi342LogChi_valid :
    (if chi342Slice.lo = 0 then
      if chi342Slice.hi = 0 then true
      else decide (chi342Slice.hi ≤ 1 / 4) &&
        chi342LogChiCertificate.check
          (IntervalAD.const chi342Slice.hi).value
    else chi342LogChiCertificate.check
      chi342Slice.chiAD.value) = true := by
  norm_num [chi342Slice, chi342LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi342ValidityFacts :
    ChiFacts chi342Slice chi342LogChiCertificate :=
  { domain := by norm_num [chi342Slice]
    onePlusPositive := by
      norm_num [chi342Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi342LogChi_valid }

noncomputable def chi342InputQChi : RationalEnclosure :=
  { lower := (-1246913/8388608), upper := (-282995/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi342InputQChi_eq :
    chi342InputQChi = outerEnclosure 24 chi342QChiValue := by
  rfl'

theorem chi342RoundedFacts :
    ChiRoundedFacts 8 chi342Slice chi342LogChiCertificate
      chi342InputQChi :=
  { coversQChi := by
      rw [chi342InputQChi_eq, chi342QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi343Slice : ChiSlice :=
  { lo := (23/32), hi := (47/64) }

noncomputable def chi343LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (23/16) }, upper := { exponent := -1, mantissa := (47/32) } }

private noncomputable def chi343QChiValue : RationalEnclosure :=
  { lower := (-17555758570914962650139260523/124417798185950770720890270600), upper := (-154666778788651906443036372708148776231933531840229095905277103/1210290686952673909538115039615537983502604095510747349767667200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi343QChiValue_eq :
    chi343QChiValue =
      (chi343Slice.qChiAD 8 chi343LogChiCertificate).value := by
  norm_num [chi343QChiValue, chi343LogChiCertificate, chi343Slice,
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
private theorem chi343LogChi_valid :
    (if chi343Slice.lo = 0 then
      if chi343Slice.hi = 0 then true
      else decide (chi343Slice.hi ≤ 1 / 4) &&
        chi343LogChiCertificate.check
          (IntervalAD.const chi343Slice.hi).value
    else chi343LogChiCertificate.check
      chi343Slice.chiAD.value) = true := by
  norm_num [chi343Slice, chi343LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi343ValidityFacts :
    ChiFacts chi343Slice chi343LogChiCertificate :=
  { domain := by norm_num [chi343Slice]
    onePlusPositive := by
      norm_num [chi343Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi343LogChi_valid }

noncomputable def chi343InputQChi : RationalEnclosure :=
  { lower := (-2367321/16777216), upper := (-536003/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi343InputQChi_eq :
    chi343InputQChi = outerEnclosure 24 chi343QChiValue := by
  rfl'

theorem chi343RoundedFacts :
    ChiRoundedFacts 8 chi343Slice chi343LogChiCertificate
      chi343InputQChi :=
  { coversQChi := by
      rw [chi343InputQChi_eq, chi343QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi344Slice : ChiSlice :=
  { lo := (47/64), hi := (3/4) }

noncomputable def chi344LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (47/32) }, upper := { exponent := -1, mantissa := (3/2) } }

private noncomputable def chi344QChiValue : RationalEnclosure :=
  { lower := (-31006809167503056715948220341896375787684/232248143314267498974473814527654321913615), upper := (-229718735405762818261649611513943642702868282623781673/1905160550624850577524980509797164359447623046875000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi344QChiValue_eq :
    chi344QChiValue =
      (chi344Slice.qChiAD 8 chi344LogChiCertificate).value := by
  norm_num [chi344QChiValue, chi344LogChiCertificate, chi344Slice,
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
private theorem chi344LogChi_valid :
    (if chi344Slice.lo = 0 then
      if chi344Slice.hi = 0 then true
      else decide (chi344Slice.hi ≤ 1 / 4) &&
        chi344LogChiCertificate.check
          (IntervalAD.const chi344Slice.hi).value
    else chi344LogChiCertificate.check
      chi344Slice.chiAD.value) = true := by
  norm_num [chi344Slice, chi344LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi344ValidityFacts :
    ChiFacts chi344Slice chi344LogChiCertificate :=
  { domain := by norm_num [chi344Slice]
    onePlusPositive := by
      norm_num [chi344Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi344LogChi_valid }

noncomputable def chi344InputQChi : RationalEnclosure :=
  { lower := (-279985/2097152), upper := (-505737/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi344InputQChi_eq :
    chi344InputQChi = outerEnclosure 24 chi344QChiValue := by
  rfl'

theorem chi344RoundedFacts :
    ChiRoundedFacts 8 chi344Slice chi344LogChiCertificate
      chi344InputQChi :=
  { coversQChi := by
      rw [chi344InputQChi_eq, chi344QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi345Slice : ChiSlice :=
  { lo := (3/4), hi := (49/64) }

noncomputable def chi345LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (3/2) }, upper := { exponent := -1, mantissa := (49/32) } }

private noncomputable def chi345QChiValue : RationalEnclosure :=
  { lower := (-7566012198856161082619/60114073271484375000000), upper := (-5545930601320588109843728103592802304246040368987/48948867336092081453647276023035611875000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi345QChiValue_eq :
    chi345QChiValue =
      (chi345Slice.qChiAD 8 chi345LogChiCertificate).value := by
  norm_num [chi345QChiValue, chi345LogChiCertificate, chi345Slice,
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
private theorem chi345LogChi_valid :
    (if chi345Slice.lo = 0 then
      if chi345Slice.hi = 0 then true
      else decide (chi345Slice.hi ≤ 1 / 4) &&
        chi345LogChiCertificate.check
          (IntervalAD.const chi345Slice.hi).value
    else chi345LogChiCertificate.check
      chi345Slice.chiAD.value) = true := by
  norm_num [chi345Slice, chi345LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi345ValidityFacts :
    ChiFacts chi345Slice chi345LogChiCertificate :=
  { domain := by norm_num [chi345Slice]
    onePlusPositive := by
      norm_num [chi345Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi345LogChi_valid }

noncomputable def chi345InputQChi : RationalEnclosure :=
  { lower := (-527899/4194304), upper := (-950433/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi345InputQChi_eq :
    chi345InputQChi = outerEnclosure 24 chi345QChiValue := by
  rfl'

theorem chi345RoundedFacts :
    ChiRoundedFacts 8 chi345Slice chi345LogChiCertificate
      chi345InputQChi :=
  { coversQChi := by
      rw [chi345InputQChi_eq, chi345QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi346Slice : ChiSlice :=
  { lo := (49/64), hi := (25/32) }

noncomputable def chi346LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (49/32) }, upper := { exponent := -1, mantissa := (25/16) } }

private noncomputable def chi346QChiValue : RationalEnclosure :=
  { lower := (-3399726778833985729661519561303225/28769946515907182568674317335988278), upper := (-288255919264919980441282173846375579106246743390332268448669423/2720197797236462728633936784709712499725364595911086388999942400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi346QChiValue_eq :
    chi346QChiValue =
      (chi346Slice.qChiAD 8 chi346LogChiCertificate).value := by
  norm_num [chi346QChiValue, chi346LogChiCertificate, chi346Slice,
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
private theorem chi346LogChi_valid :
    (if chi346Slice.lo = 0 then
      if chi346Slice.hi = 0 then true
      else decide (chi346Slice.hi ≤ 1 / 4) &&
        chi346LogChiCertificate.check
          (IntervalAD.const chi346Slice.hi).value
    else chi346LogChiCertificate.check
      chi346Slice.chiAD.value) = true := by
  norm_num [chi346Slice, chi346LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi346ValidityFacts :
    ChiFacts chi346Slice chi346LogChiCertificate :=
  { domain := by norm_num [chi346Slice]
    onePlusPositive := by
      norm_num [chi346Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi346LogChi_valid }

noncomputable def chi346InputQChi : RationalEnclosure :=
  { lower := (-991277/8388608), upper := (-444465/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi346InputQChi_eq :
    chi346InputQChi = outerEnclosure 24 chi346QChiValue := by
  rfl'

theorem chi346RoundedFacts :
    ChiRoundedFacts 8 chi346Slice chi346LogChiCertificate
      chi346InputQChi :=
  { coversQChi := by
      rw [chi346InputQChi_eq, chi346QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi347Slice : ChiSlice :=
  { lo := (39/64), hi := (79/128) }

noncomputable def chi347LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (39/32) }, upper := { exponent := -1, mantissa := (79/64) } }

private noncomputable def chi347QChiValue : RationalEnclosure :=
  { lower := (-39611711304716570055650679529384445159587/208533866387631427656469205126163562079304), upper := (-593251569727153792173765526073620538616046910919431972798007269590195816312573/3263311494687355783966069453825008741195512939895753995622517272103271503672320) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi347QChiValue_eq :
    chi347QChiValue =
      (chi347Slice.qChiAD 8 chi347LogChiCertificate).value := by
  norm_num [chi347QChiValue, chi347LogChiCertificate, chi347Slice,
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
private theorem chi347LogChi_valid :
    (if chi347Slice.lo = 0 then
      if chi347Slice.hi = 0 then true
      else decide (chi347Slice.hi ≤ 1 / 4) &&
        chi347LogChiCertificate.check
          (IntervalAD.const chi347Slice.hi).value
    else chi347LogChiCertificate.check
      chi347Slice.chiAD.value) = true := by
  norm_num [chi347Slice, chi347LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi347ValidityFacts :
    ChiFacts chi347Slice chi347LogChiCertificate :=
  { domain := by norm_num [chi347Slice]
    onePlusPositive := by
      norm_num [chi347Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi347LogChi_valid }

noncomputable def chi347InputQChi : RationalEnclosure :=
  { lower := (-3186889/16777216), upper := (-1525001/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi347InputQChi_eq :
    chi347InputQChi = outerEnclosure 24 chi347QChiValue := by
  rfl'

theorem chi347RoundedFacts :
    ChiRoundedFacts 8 chi347Slice chi347LogChiCertificate
      chi347InputQChi :=
  { coversQChi := by
      rw [chi347InputQChi_eq, chi347QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi348Slice : ChiSlice :=
  { lo := (79/128), hi := (5/8) }

noncomputable def chi348LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (79/64) }, upper := { exponent := -1, mantissa := (5/4) } }

private noncomputable def chi348QChiValue : RationalEnclosure :=
  { lower := (-355338388552355021753246319037638722923012/1905245668494734477136050074851311187235329), upper := (-75772113807093674394905500212462753751066748747612689/424580361344669614966239847645182255425986284735432192) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi348QChiValue_eq :
    chi348QChiValue =
      (chi348Slice.qChiAD 8 chi348LogChiCertificate).value := by
  norm_num [chi348QChiValue, chi348LogChiCertificate, chi348Slice,
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
private theorem chi348LogChi_valid :
    (if chi348Slice.lo = 0 then
      if chi348Slice.hi = 0 then true
      else decide (chi348Slice.hi ≤ 1 / 4) &&
        chi348LogChiCertificate.check
          (IntervalAD.const chi348Slice.hi).value
    else chi348LogChiCertificate.check
      chi348Slice.chiAD.value) = true := by
  norm_num [chi348Slice, chi348LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi348ValidityFacts :
    ChiFacts chi348Slice chi348LogChiCertificate :=
  { domain := by norm_num [chi348Slice]
    onePlusPositive := by
      norm_num [chi348Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi348LogChi_valid }

noncomputable def chi348InputQChi : RationalEnclosure :=
  { lower := (-195565/1048576), upper := (-2994121/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi348InputQChi_eq :
    chi348InputQChi = outerEnclosure 24 chi348QChiValue := by
  rfl'

theorem chi348RoundedFacts :
    ChiRoundedFacts 8 chi348Slice chi348LogChiCertificate
      chi348InputQChi :=
  { coversQChi := by
      rw [chi348InputQChi_eq, chi348QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi349Slice : ChiSlice :=
  { lo := (5/8), hi := (81/128) }

noncomputable def chi349LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (5/4) }, upper := { exponent := -1, mantissa := (81/64) } }

private noncomputable def chi349QChiValue : RationalEnclosure :=
  { lower := (-5811981136537018061/31754208023083465920), upper := (-96149008953349102237749126663512885177172242685115615057/549096472617749244540113935779339896095683750000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi349QChiValue_eq :
    chi349QChiValue =
      (chi349Slice.qChiAD 8 chi349LogChiCertificate).value := by
  norm_num [chi349QChiValue, chi349LogChiCertificate, chi349Slice,
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
private theorem chi349LogChi_valid :
    (if chi349Slice.lo = 0 then
      if chi349Slice.hi = 0 then true
      else decide (chi349Slice.hi ≤ 1 / 4) &&
        chi349LogChiCertificate.check
          (IntervalAD.const chi349Slice.hi).value
    else chi349LogChiCertificate.check
      chi349Slice.chiAD.value) = true := by
  norm_num [chi349Slice, chi349LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi349ValidityFacts :
    ChiFacts chi349Slice chi349LogChiCertificate :=
  { domain := by norm_num [chi349Slice]
    onePlusPositive := by
      norm_num [chi349Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi349LogChi_valid }

noncomputable def chi349InputQChi : RationalEnclosure :=
  { lower := (-3070739/16777216), upper := (-1468879/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi349InputQChi_eq :
    chi349InputQChi = outerEnclosure 24 chi349QChiValue := by
  rfl'

theorem chi349RoundedFacts :
    ChiRoundedFacts 8 chi349Slice chi349LogChiCertificate
      chi349InputQChi :=
  { coversQChi := by
      rw [chi349InputQChi_eq, chi349QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi350Slice : ChiSlice :=
  { lo := (81/128), hi := (41/64) }

noncomputable def chi350LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (81/64) }, upper := { exponent := -1, mantissa := (41/32) } }

private noncomputable def chi350QChiValue : RationalEnclosure :=
  { lower := (-224090032859978080497208622088440545906928213/1248207741180846956243864489404150085449218750), upper := (-39986168314550974379724595730647519598792503395341108006407767556540095134819363/232860859184026952240973551606106439014783134175749178680071182069140625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi350QChiValue_eq :
    chi350QChiValue =
      (chi350Slice.qChiAD 8 chi350LogChiCertificate).value := by
  norm_num [chi350QChiValue, chi350LogChiCertificate, chi350Slice,
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
private theorem chi350LogChi_valid :
    (if chi350Slice.lo = 0 then
      if chi350Slice.hi = 0 then true
      else decide (chi350Slice.hi ≤ 1 / 4) &&
        chi350LogChiCertificate.check
          (IntervalAD.const chi350Slice.hi).value
    else chi350LogChiCertificate.check
      chi350Slice.chiAD.value) = true := by
  norm_num [chi350Slice, chi350LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi350ValidityFacts :
    ChiFacts chi350Slice chi350LogChiCertificate :=
  { domain := by norm_num [chi350Slice]
    onePlusPositive := by
      norm_num [chi350Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi350LogChi_valid }

noncomputable def chi350InputQChi : RationalEnclosure :=
  { lower := (-3012005/16777216), upper := (-2880933/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi350InputQChi_eq :
    chi350InputQChi = outerEnclosure 24 chi350QChiValue := by
  rfl'

theorem chi350RoundedFacts :
    ChiRoundedFacts 8 chi350Slice chi350LogChiCertificate
      chi350InputQChi :=
  { coversQChi := by
      rw [chi350InputQChi_eq, chi350QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi351Slice : ChiSlice :=
  { lo := (41/64), hi := (83/128) }

noncomputable def chi351LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (41/32) }, upper := { exponent := -1, mantissa := (83/64) } }

private noncomputable def chi351QChiValue : RationalEnclosure :=
  { lower := (-283784452394919589982060852252583511723133/1612376074566419815122000377555220879767400), upper := (-21524442719294732599255063287539021775425888862963656487313957008517831/127890601691565350514766719991436366322713108962089667058961657291187200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi351QChiValue_eq :
    chi351QChiValue =
      (chi351Slice.qChiAD 8 chi351LogChiCertificate).value := by
  norm_num [chi351QChiValue, chi351LogChiCertificate, chi351Slice,
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
private theorem chi351LogChi_valid :
    (if chi351Slice.lo = 0 then
      if chi351Slice.hi = 0 then true
      else decide (chi351Slice.hi ≤ 1 / 4) &&
        chi351LogChiCertificate.check
          (IntervalAD.const chi351Slice.hi).value
    else chi351LogChiCertificate.check
      chi351Slice.chiAD.value) = true := by
  norm_num [chi351Slice, chi351LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi351ValidityFacts :
    ChiFacts chi351Slice chi351LogChiCertificate :=
  { domain := by norm_num [chi351Slice]
    onePlusPositive := by
      norm_num [chi351Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi351LogChi_valid }

noncomputable def chi351InputQChi : RationalEnclosure :=
  { lower := (-369107/2097152), upper := (-2823665/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi351InputQChi_eq :
    chi351InputQChi = outerEnclosure 24 chi351QChiValue := by
  rfl'

theorem chi351RoundedFacts :
    ChiRoundedFacts 8 chi351Slice chi351LogChiCertificate
      chi351InputQChi :=
  { coversQChi := by
      rw [chi351InputQChi_eq, chi351QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi352Slice : ChiSlice :=
  { lo := (83/128), hi := (21/32) }

noncomputable def chi352LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (83/64) }, upper := { exponent := -1, mantissa := (21/16) } }

private noncomputable def chi352QChiValue : RationalEnclosure :=
  { lower := (-80137196348034559764302898070703807/464685605117725102204288713876016659), upper := (-24262013528254899819383572564754748040056279287587185273562020133/147163109314173197920424826421610792295281185973926917327393477120) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi352QChiValue_eq :
    chi352QChiValue =
      (chi352Slice.qChiAD 8 chi352LogChiCertificate).value := by
  norm_num [chi352QChiValue, chi352LogChiCertificate, chi352Slice,
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
private theorem chi352LogChi_valid :
    (if chi352Slice.lo = 0 then
      if chi352Slice.hi = 0 then true
      else decide (chi352Slice.hi ≤ 1 / 4) &&
        chi352LogChiCertificate.check
          (IntervalAD.const chi352Slice.hi).value
    else chi352LogChiCertificate.check
      chi352Slice.chiAD.value) = true := by
  norm_num [chi352Slice, chi352LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi352ValidityFacts :
    ChiFacts chi352Slice chi352LogChiCertificate :=
  { domain := by norm_num [chi352Slice]
    onePlusPositive := by
      norm_num [chi352Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi352LogChi_valid }

noncomputable def chi352InputQChi : RationalEnclosure :=
  { lower := (-1446655/8388608), upper := (-691493/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi352InputQChi_eq :
    chi352InputQChi = outerEnclosure 24 chi352QChiValue := by
  rfl'

theorem chi352RoundedFacts :
    ChiRoundedFacts 8 chi352Slice chi352LogChiCertificate
      chi352InputQChi :=
  { coversQChi := by
      rw [chi352InputQChi_eq, chi352QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi353Slice : ChiSlice :=
  { lo := (21/32), hi := (85/128) }

noncomputable def chi353LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (21/16) }, upper := { exponent := -1, mantissa := (85/64) } }

private noncomputable def chi353QChiValue : RationalEnclosure :=
  { lower := (-187063264368778836227618131454860609/1107651604908125882392696367392765104), upper := (-21236729562202613640547936323852255879128799443854666923830494493211570971/131576844097078045164680865387712495885504746610033682813074721858018985984) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi353QChiValue_eq :
    chi353QChiValue =
      (chi353Slice.qChiAD 8 chi353LogChiCertificate).value := by
  norm_num [chi353QChiValue, chi353LogChiCertificate, chi353Slice,
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
private theorem chi353LogChi_valid :
    (if chi353Slice.lo = 0 then
      if chi353Slice.hi = 0 then true
      else decide (chi353Slice.hi ≤ 1 / 4) &&
        chi353LogChiCertificate.check
          (IntervalAD.const chi353Slice.hi).value
    else chi353LogChiCertificate.check
      chi353Slice.chiAD.value) = true := by
  norm_num [chi353Slice, chi353LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi353ValidityFacts :
    ChiFacts chi353Slice chi353LogChiCertificate :=
  { domain := by norm_num [chi353Slice]
    onePlusPositive := by
      norm_num [chi353Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi353LogChi_valid }

noncomputable def chi353InputQChi : RationalEnclosure :=
  { lower := (-2833383/16777216), upper := (-2707871/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi353InputQChi_eq :
    chi353InputQChi = outerEnclosure 24 chi353QChiValue := by
  rfl'

theorem chi353RoundedFacts :
    ChiRoundedFacts 8 chi353Slice chi353LogChiCertificate
      chi353InputQChi :=
  { coversQChi := by
      rw [chi353InputQChi_eq, chi353QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi354Slice : ChiSlice :=
  { lo := (85/128), hi := (43/64) }

noncomputable def chi354LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (85/64) }, upper := { exponent := -1, mantissa := (43/32) } }

private noncomputable def chi354QChiValue : RationalEnclosure :=
  { lower := (-6008861812245870561046347857073181034122774361/36353629989684788953313941086585219924504271770), upper := (-6297448105379881349834252506675221448708662458000635931220970533234102623/39878619094500473493146286711544656007920302012865543365478515625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi354QChiValue_eq :
    chi354QChiValue =
      (chi354Slice.qChiAD 8 chi354LogChiCertificate).value := by
  norm_num [chi354QChiValue, chi354LogChiCertificate, chi354Slice,
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
private theorem chi354LogChi_valid :
    (if chi354Slice.lo = 0 then
      if chi354Slice.hi = 0 then true
      else decide (chi354Slice.hi ≤ 1 / 4) &&
        chi354LogChiCertificate.check
          (IntervalAD.const chi354Slice.hi).value
    else chi354LogChiCertificate.check
      chi354Slice.chiAD.value) = true := by
  norm_num [chi354Slice, chi354LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi354ValidityFacts :
    ChiFacts chi354Slice chi354LogChiCertificate :=
  { domain := by norm_num [chi354Slice]
    onePlusPositive := by
      norm_num [chi354Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi354LogChi_valid }

noncomputable def chi354InputQChi : RationalEnclosure :=
  { lower := (-2773093/16777216), upper := (-662345/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi354InputQChi_eq :
    chi354InputQChi = outerEnclosure 24 chi354QChiValue := by
  rfl'

theorem chi354RoundedFacts :
    ChiRoundedFacts 8 chi354Slice chi354LogChiCertificate
      chi354InputQChi :=
  { coversQChi := by
      rw [chi354InputQChi_eq, chi354QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi355Slice : ChiSlice :=
  { lo := (43/64), hi := (87/128) }

noncomputable def chi355LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (43/32) }, upper := { exponent := -1, mantissa := (87/64) } }

private noncomputable def chi355QChiValue : RationalEnclosure :=
  { lower := (-1322334246188695022805115025740549/8178972676657140254974365234375000), upper := (-3413216283864796371495931505504104708154722862479374902964076351257153949/22105351966212701553481280167076867324681588634324073791503906250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi355QChiValue_eq :
    chi355QChiValue =
      (chi355Slice.qChiAD 8 chi355LogChiCertificate).value := by
  norm_num [chi355QChiValue, chi355LogChiCertificate, chi355Slice,
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
private theorem chi355LogChi_valid :
    (if chi355Slice.lo = 0 then
      if chi355Slice.hi = 0 then true
      else decide (chi355Slice.hi ≤ 1 / 4) &&
        chi355LogChiCertificate.check
          (IntervalAD.const chi355Slice.hi).value
    else chi355LogChiCertificate.check
      chi355Slice.chiAD.value) = true := by
  norm_num [chi355Slice, chi355LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi355ValidityFacts :
    ChiFacts chi355Slice chi355LogChiCertificate :=
  { domain := by norm_num [chi355Slice]
    onePlusPositive := by
      norm_num [chi355Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi355LogChi_valid }

noncomputable def chi355InputQChi : RationalEnclosure :=
  { lower := (-2712455/16777216), upper := (-2590515/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi355InputQChi_eq :
    chi355InputQChi = outerEnclosure 24 chi355QChiValue := by
  rfl'

theorem chi355RoundedFacts :
    ChiRoundedFacts 8 chi355Slice chi355LogChiCertificate
      chi355InputQChi :=
  { coversQChi := by
      rw [chi355InputQChi_eq, chi355QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi356Slice : ChiSlice :=
  { lo := (87/128), hi := (11/16) }

noncomputable def chi356LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (87/64) }, upper := { exponent := -1, mantissa := (11/8) } }

private noncomputable def chi356QChiValue : RationalEnclosure :=
  { lower := (-321968276348010862631074174697401257767407586/2037249132217219383951881185287504165925525575), upper := (-709572987738365082591700524223286533258365883743582926715068986442329/4702995531112686782176221249611683428271333245264480292854387756403200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi356QChiValue_eq :
    chi356QChiValue =
      (chi356Slice.qChiAD 8 chi356LogChiCertificate).value := by
  norm_num [chi356QChiValue, chi356LogChiCertificate, chi356Slice,
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
private theorem chi356LogChi_valid :
    (if chi356Slice.lo = 0 then
      if chi356Slice.hi = 0 then true
      else decide (chi356Slice.hi ≤ 1 / 4) &&
        chi356LogChiCertificate.check
          (IntervalAD.const chi356Slice.hi).value
    else chi356LogChiCertificate.check
      chi356Slice.chiAD.value) = true := by
  norm_num [chi356Slice, chi356LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi356ValidityFacts :
    ChiFacts chi356Slice chi356LogChiCertificate :=
  { domain := by norm_num [chi356Slice]
    onePlusPositive := by
      norm_num [chi356Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi356LogChi_valid }

noncomputable def chi356InputQChi : RationalEnclosure :=
  { lower := (-2651483/16777216), upper := (-632823/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi356InputQChi_eq :
    chi356InputQChi = outerEnclosure 24 chi356QChiValue := by
  rfl'

theorem chi356RoundedFacts :
    ChiRoundedFacts 8 chi356Slice chi356LogChiCertificate
      chi356InputQChi :=
  { coversQChi := by
      rw [chi356InputQChi_eq, chi356QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi357Slice : ChiSlice :=
  { lo := (11/16), hi := (89/128) }

noncomputable def chi357LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (11/8) }, upper := { exponent := -1, mantissa := (89/64) } }

private noncomputable def chi357QChiValue : RationalEnclosure :=
  { lower := (-87257805190662163645315400863633/565186669165698929063109423284256), upper := (-1083902605435352431517206789448058571629924802802409248314827037/7357150813367003444835343204455887562951475401453688939971809280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi357QChiValue_eq :
    chi357QChiValue =
      (chi357Slice.qChiAD 8 chi357LogChiCertificate).value := by
  norm_num [chi357QChiValue, chi357LogChiCertificate, chi357Slice,
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
private theorem chi357LogChi_valid :
    (if chi357Slice.lo = 0 then
      if chi357Slice.hi = 0 then true
      else decide (chi357Slice.hi ≤ 1 / 4) &&
        chi357LogChiCertificate.check
          (IntervalAD.const chi357Slice.hi).value
    else chi357LogChiCertificate.check
      chi357Slice.chiAD.value) = true := by
  norm_num [chi357Slice, chi357LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi357ValidityFacts :
    ChiFacts chi357Slice chi357LogChiCertificate :=
  { domain := by norm_num [chi357Slice]
    onePlusPositive := by
      norm_num [chi357Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi357LogChi_valid }

noncomputable def chi357InputQChi : RationalEnclosure :=
  { lower := (-1295097/8388608), upper := (-1235863/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi357InputQChi_eq :
    chi357InputQChi = outerEnclosure 24 chi357QChiValue := by
  rfl'

theorem chi357RoundedFacts :
    ChiRoundedFacts 8 chi357Slice chi357LogChiCertificate
      chi357InputQChi :=
  { coversQChi := by
      rw [chi357InputQChi_eq, chi357QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi358Slice : ChiSlice :=
  { lo := (89/128), hi := (45/64) }

noncomputable def chi358LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (89/64) }, upper := { exponent := -1, mantissa := (45/32) } }

private noncomputable def chi358QChiValue : RationalEnclosure :=
  { lower := (-989443690354853643041805746707917233/6564938503517811873004690173093064542), upper := (-37788631425162033103980590149711014999974776440622516572188938414325/262865653981274682982995356548837350223366159191716932935617064359424) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi358QChiValue_eq :
    chi358QChiValue =
      (chi358Slice.qChiAD 8 chi358LogChiCertificate).value := by
  norm_num [chi358QChiValue, chi358LogChiCertificate, chi358Slice,
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
private theorem chi358LogChi_valid :
    (if chi358Slice.lo = 0 then
      if chi358Slice.hi = 0 then true
      else decide (chi358Slice.hi ≤ 1 / 4) &&
        chi358LogChiCertificate.check
          (IntervalAD.const chi358Slice.hi).value
    else chi358LogChiCertificate.check
      chi358Slice.chiAD.value) = true := by
  norm_num [chi358Slice, chi358LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi358ValidityFacts :
    ChiFacts chi358Slice chi358LogChiCertificate :=
  { domain := by norm_num [chi358Slice]
    onePlusPositive := by
      norm_num [chi358Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi358LogChi_valid }

noncomputable def chi358InputQChi : RationalEnclosure :=
  { lower := (-1264301/8388608), upper := (-301479/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi358InputQChi_eq :
    chi358InputQChi = outerEnclosure 24 chi358QChiValue := by
  rfl'

theorem chi358RoundedFacts :
    ChiRoundedFacts 8 chi358Slice chi358LogChiCertificate
      chi358InputQChi :=
  { coversQChi := by
      rw [chi358InputQChi_eq, chi358QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi359Slice : ChiSlice :=
  { lo := (45/64), hi := (91/128) }

noncomputable def chi359LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (45/32) }, upper := { exponent := -1, mantissa := (91/64) } }

private noncomputable def chi359QChiValue : RationalEnclosure :=
  { lower := (-78178811877639412565690547275095701007/531727843458365695354324119703390828440), upper := (-136147138113461207991506325199483825994054846764151810219210294636177903259907/971315572844413450010522732546891769652787096744731429404405245156250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi359QChiValue_eq :
    chi359QChiValue =
      (chi359Slice.qChiAD 8 chi359LogChiCertificate).value := by
  norm_num [chi359QChiValue, chi359LogChiCertificate, chi359Slice,
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
private theorem chi359LogChi_valid :
    (if chi359Slice.lo = 0 then
      if chi359Slice.hi = 0 then true
      else decide (chi359Slice.hi ≤ 1 / 4) &&
        chi359LogChiCertificate.check
          (IntervalAD.const chi359Slice.hi).value
    else chi359LogChiCertificate.check
      chi359Slice.chiAD.value) = true := by
  norm_num [chi359Slice, chi359LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi359ValidityFacts :
    ChiFacts chi359Slice chi359LogChiCertificate :=
  { domain := by norm_num [chi359Slice]
    onePlusPositive := by
      norm_num [chi359Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi359LogChi_valid }

noncomputable def chi359InputQChi : RationalEnclosure :=
  { lower := (-2466719/16777216), upper := (-293953/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi359InputQChi_eq :
    chi359InputQChi = outerEnclosure 24 chi359QChiValue := by
  rfl'

theorem chi359RoundedFacts :
    ChiRoundedFacts 8 chi359Slice chi359LogChiCertificate
      chi359InputQChi :=
  { coversQChi := by
      rw [chi359InputQChi_eq, chi359QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi360Slice : ChiSlice :=
  { lo := (91/128), hi := (23/32) }

noncomputable def chi360LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (91/64) }, upper := { exponent := -1, mantissa := (23/16) } }

private noncomputable def chi360QChiValue : RationalEnclosure :=
  { lower := (-4842607582953706539211526178786997483903111891/33788097966656251762927706490120841827392578125), upper := (-1069709476816678601833161881832916797245053298059256186585879429419/7833186708958590033634147414055825410762535991471094921875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi360QChiValue_eq :
    chi360QChiValue =
      (chi360Slice.qChiAD 8 chi360LogChiCertificate).value := by
  norm_num [chi360QChiValue, chi360LogChiCertificate, chi360Slice,
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
private theorem chi360LogChi_valid :
    (if chi360Slice.lo = 0 then
      if chi360Slice.hi = 0 then true
      else decide (chi360Slice.hi ≤ 1 / 4) &&
        chi360LogChiCertificate.check
          (IntervalAD.const chi360Slice.hi).value
    else chi360LogChiCertificate.check
      chi360Slice.chiAD.value) = true := by
  norm_num [chi360Slice, chi360LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi360ValidityFacts :
    ChiFacts chi360Slice chi360LogChiCertificate :=
  { domain := by norm_num [chi360Slice]
    onePlusPositive := by
      norm_num [chi360Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi360LogChi_valid }

noncomputable def chi360InputQChi : RationalEnclosure :=
  { lower := (-2404559/16777216), upper := (-572779/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi360InputQChi_eq :
    chi360InputQChi = outerEnclosure 24 chi360QChiValue := by
  rfl'

theorem chi360RoundedFacts :
    ChiRoundedFacts 8 chi360Slice chi360LogChiCertificate
      chi360InputQChi :=
  { coversQChi := by
      rw [chi360InputQChi_eq, chi360QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi361Slice : ChiSlice :=
  { lo := (25/32), hi := (51/64) }

noncomputable def chi361LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (25/16) }, upper := { exponent := -1, mantissa := (51/32) } }

private noncomputable def chi361QChiValue : RationalEnclosure :=
  { lower := (-42287320809446919928083116158221427/382907572436022060918602364552276120), upper := (-115181974984194298635958641024332009687444559561653400152202429246168611/1168328503285606700944267888847974749818159170983439769822578244208499200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi361QChiValue_eq :
    chi361QChiValue =
      (chi361Slice.qChiAD 8 chi361LogChiCertificate).value := by
  norm_num [chi361QChiValue, chi361LogChiCertificate, chi361Slice,
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
private theorem chi361LogChi_valid :
    (if chi361Slice.lo = 0 then
      if chi361Slice.hi = 0 then true
      else decide (chi361Slice.hi ≤ 1 / 4) &&
        chi361LogChiCertificate.check
          (IntervalAD.const chi361Slice.hi).value
    else chi361LogChiCertificate.check
      chi361Slice.chiAD.value) = true := by
  norm_num [chi361Slice, chi361LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi361ValidityFacts :
    ChiFacts chi361Slice chi361LogChiCertificate :=
  { domain := by norm_num [chi361Slice]
    onePlusPositive := by
      norm_num [chi361Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi361LogChi_valid }

noncomputable def chi361InputQChi : RationalEnclosure :=
  { lower := (-1852833/16777216), upper := (-1654015/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi361InputQChi_eq :
    chi361InputQChi = outerEnclosure 24 chi361QChiValue := by
  rfl'

theorem chi361RoundedFacts :
    ChiRoundedFacts 8 chi361Slice chi361LogChiCertificate
      chi361InputQChi :=
  { coversQChi := by
      rw [chi361InputQChi_eq, chi361QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi362Slice : ChiSlice :=
  { lo := (51/64), hi := (13/16) }

noncomputable def chi362LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (51/32) }, upper := { exponent := -1, mantissa := (13/8) } }

private noncomputable def chi362QChiValue : RationalEnclosure :=
  { lower := (-11959453183123940725241703840890331151901/116485007241955576296682061002513599523425), upper := (-14185096015137172669936772263168214927884102544466270641/155606533074462708405504853740694541605077081951526713600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi362QChiValue_eq :
    chi362QChiValue =
      (chi362Slice.qChiAD 8 chi362LogChiCertificate).value := by
  norm_num [chi362QChiValue, chi362LogChiCertificate, chi362Slice,
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
private theorem chi362LogChi_valid :
    (if chi362Slice.lo = 0 then
      if chi362Slice.hi = 0 then true
      else decide (chi362Slice.hi ≤ 1 / 4) &&
        chi362LogChiCertificate.check
          (IntervalAD.const chi362Slice.hi).value
    else chi362LogChiCertificate.check
      chi362Slice.chiAD.value) = true := by
  norm_num [chi362Slice, chi362LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi362ValidityFacts :
    ChiFacts chi362Slice chi362LogChiCertificate :=
  { domain := by norm_num [chi362Slice]
    onePlusPositive := by
      norm_num [chi362Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi362LogChi_valid }

noncomputable def chi362InputQChi : RationalEnclosure :=
  { lower := (-430627/4194304), upper := (-1529411/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi362InputQChi_eq :
    chi362InputQChi = outerEnclosure 24 chi362QChiValue := by
  rfl'

theorem chi362RoundedFacts :
    ChiRoundedFacts 8 chi362Slice chi362LogChiCertificate
      chi362InputQChi :=
  { coversQChi := by
      rw [chi362InputQChi_eq, chi362QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi363Slice : ChiSlice :=
  { lo := (13/16), hi := (53/64) }

noncomputable def chi363LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (13/8) }, upper := { exponent := -1, mantissa := (53/32) } }

private noncomputable def chi363QChiValue : RationalEnclosure :=
  { lower := (-6432240946786806087141763/67800781239240150360539280), upper := (-4371533538919073946720692600988984471794444834259104915611/52233337375108341775890256012229587859470698656250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi363QChiValue_eq :
    chi363QChiValue =
      (chi363Slice.qChiAD 8 chi363LogChiCertificate).value := by
  norm_num [chi363QChiValue, chi363LogChiCertificate, chi363Slice,
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
private theorem chi363LogChi_valid :
    (if chi363Slice.lo = 0 then
      if chi363Slice.hi = 0 then true
      else decide (chi363Slice.hi ≤ 1 / 4) &&
        chi363LogChiCertificate.check
          (IntervalAD.const chi363Slice.hi).value
    else chi363LogChiCertificate.check
      chi363Slice.chiAD.value) = true := by
  norm_num [chi363Slice, chi363LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi363ValidityFacts :
    ChiFacts chi363Slice chi363LogChiCertificate :=
  { domain := by norm_num [chi363Slice]
    onePlusPositive := by
      norm_num [chi363Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi363LogChi_valid }

noncomputable def chi363InputQChi : RationalEnclosure :=
  { lower := (-795825/8388608), upper := (-1404125/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi363InputQChi_eq :
    chi363InputQChi = outerEnclosure 24 chi363QChiValue := by
  rfl'

theorem chi363RoundedFacts :
    ChiRoundedFacts 8 chi363Slice chi363LogChiCertificate
      chi363InputQChi :=
  { coversQChi := by
      rw [chi363InputQChi_eq, chi363QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi364Slice : ChiSlice :=
  { lo := (53/64), hi := (27/32) }

noncomputable def chi364LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (53/32) }, upper := { exponent := -1, mantissa := (27/16) } }

private noncomputable def chi364QChiValue : RationalEnclosure :=
  { lower := (-1290674534710495238851241959114130062529/14828166405087758856888061808166503906250), upper := (-8050469034408478245790309863767568395661651840640681139186785332277223/105665379082006826791782064098623714899000635738608025641132812500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi364QChiValue_eq :
    chi364QChiValue =
      (chi364Slice.qChiAD 8 chi364LogChiCertificate).value := by
  norm_num [chi364QChiValue, chi364LogChiCertificate, chi364Slice,
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
private theorem chi364LogChi_valid :
    (if chi364Slice.lo = 0 then
      if chi364Slice.hi = 0 then true
      else decide (chi364Slice.hi ≤ 1 / 4) &&
        chi364LogChiCertificate.check
          (IntervalAD.const chi364Slice.hi).value
    else chi364LogChiCertificate.check
      chi364Slice.chiAD.value) = true := by
  norm_num [chi364Slice, chi364LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi364ValidityFacts :
    ChiFacts chi364Slice chi364LogChiCertificate :=
  { domain := by norm_num [chi364Slice]
    onePlusPositive := by
      norm_num [chi364Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi364LogChi_valid }

noncomputable def chi364InputQChi : RationalEnclosure :=
  { lower := (-365081/4194304), upper := (-319557/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi364InputQChi_eq :
    chi364InputQChi = outerEnclosure 24 chi364QChiValue := by
  rfl'

theorem chi364RoundedFacts :
    ChiRoundedFacts 8 chi364Slice chi364LogChiCertificate
      chi364InputQChi :=
  { coversQChi := by
      rw [chi364InputQChi_eq, chi364QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi365Slice : ChiSlice :=
  { lo := (27/32), hi := (55/64) }

noncomputable def chi365LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (27/16) }, upper := { exponent := -1, mantissa := (55/32) } }

private noncomputable def chi365QChiValue : RationalEnclosure :=
  { lower := (-465180971200398454567497460379927605/5874221252098093327290264287537728344), upper := (-1457678449609975389188519881502683945000632830265501775376121203/21232928314791885807980516438383479601782259093705024854406049280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi365QChiValue_eq :
    chi365QChiValue =
      (chi365Slice.qChiAD 8 chi365LogChiCertificate).value := by
  norm_num [chi365QChiValue, chi365LogChiCertificate, chi365Slice,
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
private theorem chi365LogChi_valid :
    (if chi365Slice.lo = 0 then
      if chi365Slice.hi = 0 then true
      else decide (chi365Slice.hi ≤ 1 / 4) &&
        chi365LogChiCertificate.check
          (IntervalAD.const chi365Slice.hi).value
    else chi365LogChiCertificate.check
      chi365Slice.chiAD.value) = true := by
  norm_num [chi365Slice, chi365LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi365ValidityFacts :
    ChiFacts chi365Slice chi365LogChiCertificate :=
  { domain := by norm_num [chi365Slice]
    onePlusPositive := by
      norm_num [chi365Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi365LogChi_valid }

noncomputable def chi365InputQChi : RationalEnclosure :=
  { lower := (-83037/1048576), upper := (-1151785/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi365InputQChi_eq :
    chi365InputQChi = outerEnclosure 24 chi365QChiValue := by
  rfl'

theorem chi365RoundedFacts :
    ChiRoundedFacts 8 chi365Slice chi365LogChiCertificate
      chi365InputQChi :=
  { coversQChi := by
      rw [chi365InputQChi_eq, chi365QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi366Slice : ChiSlice :=
  { lo := (55/64), hi := (7/8) }

noncomputable def chi366LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (55/32) }, upper := { exponent := -1, mantissa := (7/4) } }

private noncomputable def chi366QChiValue : RationalEnclosure :=
  { lower := (-751343535175192392002157664546018/10535175931382392152384578439538155), upper := (-6569220111354727109529672170117057314663927476219869/107539657524435478927978229640086945680241343062342400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi366QChiValue_eq :
    chi366QChiValue =
      (chi366Slice.qChiAD 8 chi366LogChiCertificate).value := by
  norm_num [chi366QChiValue, chi366LogChiCertificate, chi366Slice,
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
private theorem chi366LogChi_valid :
    (if chi366Slice.lo = 0 then
      if chi366Slice.hi = 0 then true
      else decide (chi366Slice.hi ≤ 1 / 4) &&
        chi366LogChiCertificate.check
          (IntervalAD.const chi366Slice.hi).value
    else chi366LogChiCertificate.check
      chi366Slice.chiAD.value) = true := by
  norm_num [chi366Slice, chi366LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi366ValidityFacts :
    ChiFacts chi366Slice chi366LogChiCertificate :=
  { domain := by norm_num [chi366Slice]
    onePlusPositive := by
      norm_num [chi366Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi366LogChi_valid }

noncomputable def chi366InputQChi : RationalEnclosure :=
  { lower := (-1196511/16777216), upper := (-1024861/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi366InputQChi_eq :
    chi366InputQChi = outerEnclosure 24 chi366QChiValue := by
  rfl'

theorem chi366RoundedFacts :
    ChiRoundedFacts 8 chi366Slice chi366LogChiCertificate
      chi366InputQChi :=
  { coversQChi := by
      rw [chi366InputQChi_eq, chi366QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi367Slice : ChiSlice :=
  { lo := (7/8), hi := (57/64) }

noncomputable def chi367LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (7/4) }, upper := { exponent := -1, mantissa := (57/32) } }

private noncomputable def chi367QChiValue : RationalEnclosure :=
  { lower := (-830307142171976449556208397/13090665696952207846691008800), upper := (-53823612852490158594397393796338237682084563443534627782821217/1006125211856254481169358716018045510870418572874247527927449600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi367QChiValue_eq :
    chi367QChiValue =
      (chi367Slice.qChiAD 8 chi367LogChiCertificate).value := by
  norm_num [chi367QChiValue, chi367LogChiCertificate, chi367Slice,
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
private theorem chi367LogChi_valid :
    (if chi367Slice.lo = 0 then
      if chi367Slice.hi = 0 then true
      else decide (chi367Slice.hi ≤ 1 / 4) &&
        chi367LogChiCertificate.check
          (IntervalAD.const chi367Slice.hi).value
    else chi367LogChiCertificate.check
      chi367Slice.chiAD.value) = true := by
  norm_num [chi367Slice, chi367LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi367ValidityFacts :
    ChiFacts chi367Slice chi367LogChiCertificate :=
  { domain := by norm_num [chi367Slice]
    onePlusPositive := by
      norm_num [chi367Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi367LogChi_valid }

noncomputable def chi367InputQChi : RationalEnclosure :=
  { lower := (-133017/2097152), upper := (-112189/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi367InputQChi_eq :
    chi367InputQChi = outerEnclosure 24 chi367QChiValue := by
  rfl'

theorem chi367RoundedFacts :
    ChiRoundedFacts 8 chi367Slice chi367LogChiCertificate
      chi367InputQChi :=
  { coversQChi := by
      rw [chi367InputQChi_eq, chi367QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi368Slice : ChiSlice :=
  { lo := (57/64), hi := (29/32) }

noncomputable def chi368LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (57/32) }, upper := { exponent := -1, mantissa := (29/16) } }

private noncomputable def chi368QChiValue : RationalEnclosure :=
  { lower := (-72008229258059974695030271892507259012037/1296915208074277384974008228575416294150870), upper := (-33993494163459117111432169848720102415583526162872449789494851/740866629393359718512425010799485498340856414318195312500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi368QChiValue_eq :
    chi368QChiValue =
      (chi368Slice.qChiAD 8 chi368LogChiCertificate).value := by
  norm_num [chi368QChiValue, chi368LogChiCertificate, chi368Slice,
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
private theorem chi368LogChi_valid :
    (if chi368Slice.lo = 0 then
      if chi368Slice.hi = 0 then true
      else decide (chi368Slice.hi ≤ 1 / 4) &&
        chi368LogChiCertificate.check
          (IntervalAD.const chi368Slice.hi).value
    else chi368LogChiCertificate.check
      chi368Slice.chiAD.value) = true := by
  norm_num [chi368Slice, chi368LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi368ValidityFacts :
    ChiFacts chi368Slice chi368LogChiCertificate :=
  { domain := by norm_num [chi368Slice]
    onePlusPositive := by
      norm_num [chi368Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi368LogChi_valid }

noncomputable def chi368InputQChi : RationalEnclosure :=
  { lower := (-931517/16777216), upper := (-192449/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi368InputQChi_eq :
    chi368InputQChi = outerEnclosure 24 chi368QChiValue := by
  rfl'

theorem chi368RoundedFacts :
    ChiRoundedFacts 8 chi368Slice chi368LogChiCertificate
      chi368InputQChi :=
  { coversQChi := by
      rw [chi368InputQChi_eq, chi368QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi369Slice : ChiSlice :=
  { lo := (29/32), hi := (59/64) }

noncomputable def chi369LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (29/16) }, upper := { exponent := -1, mantissa := (59/32) } }

private noncomputable def chi369QChiValue : RationalEnclosure :=
  { lower := (-2191780431548239534564369083571/46039740296013290731201171875000), upper := (-163284529000649042422595002151457969429390734688721117833701/4268651774732930879445075288761651137638689856796875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi369QChiValue_eq :
    chi369QChiValue =
      (chi369Slice.qChiAD 8 chi369LogChiCertificate).value := by
  norm_num [chi369QChiValue, chi369LogChiCertificate, chi369Slice,
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
private theorem chi369LogChi_valid :
    (if chi369Slice.lo = 0 then
      if chi369Slice.hi = 0 then true
      else decide (chi369Slice.hi ≤ 1 / 4) &&
        chi369LogChiCertificate.check
          (IntervalAD.const chi369Slice.hi).value
    else chi369LogChiCertificate.check
      chi369Slice.chiAD.value) = true := by
  norm_num [chi369Slice, chi369LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi369ValidityFacts :
    ChiFacts chi369Slice chi369LogChiCertificate :=
  { domain := by norm_num [chi369Slice]
    onePlusPositive := by
      norm_num [chi369Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi369LogChi_valid }

noncomputable def chi369InputQChi : RationalEnclosure :=
  { lower := (-798701/16777216), upper := (-320881/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi369InputQChi_eq :
    chi369InputQChi = outerEnclosure 24 chi369QChiValue := by
  rfl'

theorem chi369RoundedFacts :
    ChiRoundedFacts 8 chi369Slice chi369LogChiCertificate
      chi369InputQChi :=
  { coversQChi := by
      rw [chi369InputQChi_eq, chi369QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi370Slice : ChiSlice :=
  { lo := (59/64), hi := (15/16) }

noncomputable def chi370LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (59/32) }, upper := { exponent := -1, mantissa := (15/8) } }

private noncomputable def chi370QChiValue : RationalEnclosure :=
  { lower := (-187205242675329419973740139693717540415/4717778014791917801423787801783332782521), upper := (-916568595984098007766849383625241599431655563948066379462457707/29948698680672698821605469124339438267848747531386975173139960576) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi370QChiValue_eq :
    chi370QChiValue =
      (chi370Slice.qChiAD 8 chi370LogChiCertificate).value := by
  norm_num [chi370QChiValue, chi370LogChiCertificate, chi370Slice,
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
private theorem chi370LogChi_valid :
    (if chi370Slice.lo = 0 then
      if chi370Slice.hi = 0 then true
      else decide (chi370Slice.hi ≤ 1 / 4) &&
        chi370LogChiCertificate.check
          (IntervalAD.const chi370Slice.hi).value
    else chi370LogChiCertificate.check
      chi370Slice.chiAD.value) = true := by
  norm_num [chi370Slice, chi370LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi370ValidityFacts :
    ChiFacts chi370Slice chi370LogChiCertificate :=
  { domain := by norm_num [chi370Slice]
    onePlusPositive := by
      norm_num [chi370Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi370LogChi_valid }

noncomputable def chi370InputQChi : RationalEnclosure :=
  { lower := (-332867/8388608), upper := (-128365/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi370InputQChi_eq :
    chi370InputQChi = outerEnclosure 24 chi370QChiValue := by
  rfl'

theorem chi370RoundedFacts :
    ChiRoundedFacts 8 chi370Slice chi370LogChiCertificate
      chi370InputQChi :=
  { coversQChi := by
      rw [chi370InputQChi_eq, chi370QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi371Slice : ChiSlice :=
  { lo := (15/16), hi := (61/64) }

noncomputable def chi371LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (15/8) }, upper := { exponent := -1, mantissa := (61/32) } }

private noncomputable def chi371QChiValue : RationalEnclosure :=
  { lower := (-904629290389324248868609130135021/28493340898739005642881299296084560), upper := (-7486124748260318682239289661498195796346087966168478163895923/326278610095384797430603654106479526201021902429285536401280000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi371QChiValue_eq :
    chi371QChiValue =
      (chi371Slice.qChiAD 8 chi371LogChiCertificate).value := by
  norm_num [chi371QChiValue, chi371LogChiCertificate, chi371Slice,
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
private theorem chi371LogChi_valid :
    (if chi371Slice.lo = 0 then
      if chi371Slice.hi = 0 then true
      else decide (chi371Slice.hi ≤ 1 / 4) &&
        chi371LogChiCertificate.check
          (IntervalAD.const chi371Slice.hi).value
    else chi371LogChiCertificate.check
      chi371Slice.chiAD.value) = true := by
  norm_num [chi371Slice, chi371LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi371ValidityFacts :
    ChiFacts chi371Slice chi371LogChiCertificate :=
  { domain := by norm_num [chi371Slice]
    onePlusPositive := by
      norm_num [chi371Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi371LogChi_valid }

noncomputable def chi371InputQChi : RationalEnclosure :=
  { lower := (-532657/16777216), upper := (-384935/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi371InputQChi_eq :
    chi371InputQChi = outerEnclosure 24 chi371QChiValue := by
  rfl'

theorem chi371RoundedFacts :
    ChiRoundedFacts 8 chi371Slice chi371LogChiCertificate
      chi371InputQChi :=
  { coversQChi := by
      rw [chi371InputQChi_eq, chi371QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi372Slice : ChiSlice :=
  { lo := (61/64), hi := (31/32) }

noncomputable def chi372LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (61/32) }, upper := { exponent := -1, mantissa := (31/16) } }

private noncomputable def chi372QChiValue : RationalEnclosure :=
  { lower := (-970854952283924953456497171926393/40770672933104730364104252698051250), upper := (-858602540394874492988332947501527431510770847341720977128039/56218490273923165592548068878317970157347130637786899935520000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi372QChiValue_eq :
    chi372QChiValue =
      (chi372Slice.qChiAD 8 chi372LogChiCertificate).value := by
  norm_num [chi372QChiValue, chi372LogChiCertificate, chi372Slice,
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
private theorem chi372LogChi_valid :
    (if chi372Slice.lo = 0 then
      if chi372Slice.hi = 0 then true
      else decide (chi372Slice.hi ≤ 1 / 4) &&
        chi372LogChiCertificate.check
          (IntervalAD.const chi372Slice.hi).value
    else chi372LogChiCertificate.check
      chi372Slice.chiAD.value) = true := by
  norm_num [chi372Slice, chi372LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi372ValidityFacts :
    ChiFacts chi372Slice chi372LogChiCertificate :=
  { domain := by norm_num [chi372Slice]
    onePlusPositive := by
      norm_num [chi372Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi372LogChi_valid }

noncomputable def chi372InputQChi : RationalEnclosure :=
  { lower := (-399509/16777216), upper := (-256231/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi372InputQChi_eq :
    chi372InputQChi = outerEnclosure 24 chi372QChiValue := by
  rfl'

theorem chi372RoundedFacts :
    ChiRoundedFacts 8 chi372Slice chi372LogChiCertificate
      chi372InputQChi :=
  { coversQChi := by
      rw [chi372InputQChi_eq, chi372QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi373Slice : ChiSlice :=
  { lo := (31/32), hi := (63/64) }

noncomputable def chi373LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (31/16) }, upper := { exponent := -1, mantissa := (63/32) } }

private noncomputable def chi373QChiValue : RationalEnclosure :=
  { lower := (-330064010856489900387449504245868297/20792275134974323488077200372353732120), upper := (-299626383052255942642132643854247759508976151521193284884637245299801/39461203291926298936601207642794964740745309975031034198498125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi373QChiValue_eq :
    chi373QChiValue =
      (chi373Slice.qChiAD 8 chi373LogChiCertificate).value := by
  norm_num [chi373QChiValue, chi373LogChiCertificate, chi373Slice,
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
private theorem chi373LogChi_valid :
    (if chi373Slice.lo = 0 then
      if chi373Slice.hi = 0 then true
      else decide (chi373Slice.hi ≤ 1 / 4) &&
        chi373LogChiCertificate.check
          (IntervalAD.const chi373Slice.hi).value
    else chi373LogChiCertificate.check
      chi373Slice.chiAD.value) = true := by
  norm_num [chi373Slice, chi373LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi373ValidityFacts :
    ChiFacts chi373Slice chi373LogChiCertificate :=
  { domain := by norm_num [chi373Slice]
    onePlusPositive := by
      norm_num [chi373Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi373LogChi_valid }

noncomputable def chi373InputQChi : RationalEnclosure :=
  { lower := (-33291/2097152), upper := (-31847/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi373InputQChi_eq :
    chi373InputQChi = outerEnclosure 24 chi373QChiValue := by
  rfl'

theorem chi373RoundedFacts :
    ChiRoundedFacts 8 chi373Slice chi373LogChiCertificate
      chi373InputQChi :=
  { coversQChi := by
      rw [chi373InputQChi_eq, chi373QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi374Slice : ChiSlice :=
  { lo := (63/64), hi := (1) }

noncomputable def chi374LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -1, mantissa := (63/32) }, upper := { exponent := 0, mantissa := (1) } }

private noncomputable def chi374QChiValue : RationalEnclosure :=
  { lower := (-100603695243345976418638752977700778146704/12676575799172677638974877950368194580078125), upper := (2408200954887594310521165149403712376886727/25961627236705643804620550042354062500000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi374QChiValue_eq :
    chi374QChiValue =
      (chi374Slice.qChiAD 8 chi374LogChiCertificate).value := by
  norm_num [chi374QChiValue, chi374LogChiCertificate, chi374Slice,
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
private theorem chi374LogChi_valid :
    (if chi374Slice.lo = 0 then
      if chi374Slice.hi = 0 then true
      else decide (chi374Slice.hi ≤ 1 / 4) &&
        chi374LogChiCertificate.check
          (IntervalAD.const chi374Slice.hi).value
    else chi374LogChiCertificate.check
      chi374Slice.chiAD.value) = true := by
  norm_num [chi374Slice, chi374LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi374ValidityFacts :
    ChiFacts chi374Slice chi374LogChiCertificate :=
  { domain := by norm_num [chi374Slice]
    onePlusPositive := by
      norm_num [chi374Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi374LogChi_valid }

noncomputable def chi374InputQChi : RationalEnclosure :=
  { lower := (-33287/4194304), upper := (1557/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi374InputQChi_eq :
    chi374InputQChi = outerEnclosure 24 chi374QChiValue := by
  rfl'

theorem chi374RoundedFacts :
    ChiRoundedFacts 8 chi374Slice chi374LogChiCertificate
      chi374InputQChi :=
  { coversQChi := by
      rw [chi374InputQChi_eq, chi374QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
