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

noncomputable def chi192Slice : ChiSlice :=
  { lo := (61/256), hi := (31/128) }

noncomputable def chi192LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (61/32) }, upper := { exponent := -3, mantissa := (31/16) } }

private noncomputable def chi192QChiValue : RationalEnclosure :=
  { lower := (-29004851993196186560228794759507051/103394426558353596203368384842257970), upper := (-5487837048788292761698224825834678238754047095892178316057086171/20177584684606636883011624225897381330734255953269997583600103680) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi192QChiValue_eq :
    chi192QChiValue =
      (chi192Slice.qChiAD 8 chi192LogChiCertificate).value := by
  norm_num [chi192QChiValue, chi192LogChiCertificate, chi192Slice,
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
private theorem chi192LogChi_valid :
    (if chi192Slice.lo = 0 then
      if chi192Slice.hi = 0 then true
      else decide (chi192Slice.hi ≤ 1 / 4) &&
        chi192LogChiCertificate.check
          (IntervalAD.const chi192Slice.hi).value
    else chi192LogChiCertificate.check
      chi192Slice.chiAD.value) = true := by
  norm_num [chi192Slice, chi192LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi192ValidityFacts :
    ChiFacts chi192Slice chi192LogChiCertificate :=
  { domain := by norm_num [chi192Slice]
    onePlusPositive := by
      norm_num [chi192Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi192LogChi_valid }

noncomputable def chi192InputQChi : RationalEnclosure :=
  { lower := (-2353225/8388608), upper := (-4563015/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi192InputQChi_eq :
    chi192InputQChi = outerEnclosure 24 chi192QChiValue := by
  rfl'

theorem chi192RoundedFacts :
    ChiRoundedFacts 8 chi192Slice chi192LogChiCertificate
      chi192InputQChi :=
  { coversQChi := by
      rw [chi192InputQChi_eq, chi192QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi193Slice : ChiSlice :=
  { lo := (25/128), hi := (51/256) }

noncomputable def chi193LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (25/16) }, upper := { exponent := -3, mantissa := (51/32) } }

private noncomputable def chi193QChiValue : RationalEnclosure :=
  { lower := (-729571757276296090692313249437048527/2680353007052154426430216551865932840), upper := (-733136867565246037281585673235362325921680793184537903907961935109877569/2790620804873034952964821103843286141556509250966852246546469499553390080) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi193QChiValue_eq :
    chi193QChiValue =
      (chi193Slice.qChiAD 8 chi193LogChiCertificate).value := by
  norm_num [chi193QChiValue, chi193LogChiCertificate, chi193Slice,
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
private theorem chi193LogChi_valid :
    (if chi193Slice.lo = 0 then
      if chi193Slice.hi = 0 then true
      else decide (chi193Slice.hi ≤ 1 / 4) &&
        chi193LogChiCertificate.check
          (IntervalAD.const chi193Slice.hi).value
    else chi193LogChiCertificate.check
      chi193Slice.chiAD.value) = true := by
  norm_num [chi193Slice, chi193LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi193ValidityFacts :
    ChiFacts chi193Slice chi193LogChiCertificate :=
  { domain := by norm_num [chi193Slice]
    onePlusPositive := by
      norm_num [chi193Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi193LogChi_valid }

noncomputable def chi193InputQChi : RationalEnclosure :=
  { lower := (-4566631/16777216), upper := (-4407619/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi193InputQChi_eq :
    chi193InputQChi = outerEnclosure 24 chi193QChiValue := by
  rfl'

theorem chi193RoundedFacts :
    ChiRoundedFacts 8 chi193Slice chi193LogChiCertificate
      chi193InputQChi :=
  { coversQChi := by
      rw [chi193InputQChi_eq, chi193QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi194Slice : ChiSlice :=
  { lo := (51/256), hi := (13/64) }

noncomputable def chi194LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (51/32) }, upper := { exponent := -3, mantissa := (13/8) } }

private noncomputable def chi194QChiValue : RationalEnclosure :=
  { lower := (-28325877585471807504768875135007010429469/103654774560232933110380848486294710300555), upper := (-679130095633830982916128016947249832513184397718267357797/2573581194145983782906956987809490043280051972190402786560) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi194QChiValue_eq :
    chi194QChiValue =
      (chi194Slice.qChiAD 8 chi194LogChiCertificate).value := by
  norm_num [chi194QChiValue, chi194LogChiCertificate, chi194Slice,
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
private theorem chi194LogChi_valid :
    (if chi194Slice.lo = 0 then
      if chi194Slice.hi = 0 then true
      else decide (chi194Slice.hi ≤ 1 / 4) &&
        chi194LogChiCertificate.check
          (IntervalAD.const chi194Slice.hi).value
    else chi194LogChiCertificate.check
      chi194Slice.chiAD.value) = true := by
  norm_num [chi194Slice, chi194LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi194ValidityFacts :
    ChiFacts chi194Slice chi194LogChiCertificate :=
  { domain := by norm_num [chi194Slice]
    onePlusPositive := by
      norm_num [chi194Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi194LogChi_valid }

noncomputable def chi194InputQChi : RationalEnclosure :=
  { lower := (-4584733/16777216), upper := (-4427259/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi194InputQChi_eq :
    chi194InputQChi = outerEnclosure 24 chi194QChiValue := by
  rfl'

theorem chi194RoundedFacts :
    ChiRoundedFacts 8 chi194Slice chi194LogChiCertificate
      chi194InputQChi :=
  { coversQChi := by
      rw [chi194InputQChi_eq, chi194QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi195Slice : ChiSlice :=
  { lo := (13/64), hi := (53/256) }

noncomputable def chi195LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (13/8) }, upper := { exponent := -3, mantissa := (53/32) } }

private noncomputable def chi195QChiValue : RationalEnclosure :=
  { lower := (-49376789874839367685374089/180022763980051433715914640), upper := (-26470533908628883533785995275867490017627521963985887538547/99894525855313300849912134177234835137077914406250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi195QChiValue_eq :
    chi195QChiValue =
      (chi195Slice.qChiAD 8 chi195LogChiCertificate).value := by
  norm_num [chi195QChiValue, chi195LogChiCertificate, chi195Slice,
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
private theorem chi195LogChi_valid :
    (if chi195Slice.lo = 0 then
      if chi195Slice.hi = 0 then true
      else decide (chi195Slice.hi ≤ 1 / 4) &&
        chi195LogChiCertificate.check
          (IntervalAD.const chi195Slice.hi).value
    else chi195LogChiCertificate.check
      chi195Slice.chiAD.value) = true := by
  norm_num [chi195Slice, chi195LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi195ValidityFacts :
    ChiFacts chi195Slice chi195LogChiCertificate :=
  { domain := by norm_num [chi195Slice]
    onePlusPositive := by
      norm_num [chi195Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi195LogChi_valid }

noncomputable def chi195InputQChi : RationalEnclosure :=
  { lower := (-4601669/16777216), upper := (-4445707/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi195InputQChi_eq :
    chi195InputQChi = outerEnclosure 24 chi195QChiValue := by
  rfl'

theorem chi195RoundedFacts :
    ChiRoundedFacts 8 chi195Slice chi195LogChiCertificate
      chi195InputQChi :=
  { coversQChi := by
      rw [chi195InputQChi_eq, chi195QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi196Slice : ChiSlice :=
  { lo := (53/256), hi := (27/128) }

noncomputable def chi196LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (53/32) }, upper := { exponent := -3, mantissa := (27/16) } }

private noncomputable def chi196QChiValue : RationalEnclosure :=
  { lower := (-39519895379783204150310156231412454760523/143592414845849835767984393407287597656250), upper := (-65008530775258692356361042671578777767725416617420012217979623598308349/244378933368714905074721230383098306296182116408355371484960937500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi196QChiValue_eq :
    chi196QChiValue =
      (chi196Slice.qChiAD 8 chi196LogChiCertificate).value := by
  norm_num [chi196QChiValue, chi196LogChiCertificate, chi196Slice,
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
private theorem chi196LogChi_valid :
    (if chi196Slice.lo = 0 then
      if chi196Slice.hi = 0 then true
      else decide (chi196Slice.hi ≤ 1 / 4) &&
        chi196LogChiCertificate.check
          (IntervalAD.const chi196Slice.hi).value
    else chi196LogChiCertificate.check
      chi196Slice.chiAD.value) = true := by
  norm_num [chi196Slice, chi196LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi196ValidityFacts :
    ChiFacts chi196Slice chi196LogChiCertificate :=
  { domain := by norm_num [chi196Slice]
    onePlusPositive := by
      norm_num [chi196Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi196LogChi_valid }

noncomputable def chi196InputQChi : RationalEnclosure :=
  { lower := (-18037/65536), upper := (-4462995/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi196InputQChi_eq :
    chi196InputQChi = outerEnclosure 24 chi196QChiValue := by
  rfl'

theorem chi196RoundedFacts :
    ChiRoundedFacts 8 chi196Slice chi196LogChiCertificate
      chi196InputQChi :=
  { coversQChi := by
      rw [chi196InputQChi_eq, chi196QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi197Slice : ChiSlice :=
  { lo := (27/128), hi := (55/256) }

noncomputable def chi197LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (27/16) }, upper := { exponent := -3, mantissa := (55/32) } }

private noncomputable def chi197QChiValue : RationalEnclosure :=
  { lower := (-1420277836391179272714696043804995637/5144092056922059128418028048408745160), upper := (-301709840371514535268239182139045016155771888043966133290785299/1130090690734598922362150309770881855213886358214449368513113600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi197QChiValue_eq :
    chi197QChiValue =
      (chi197Slice.qChiAD 8 chi197LogChiCertificate).value := by
  norm_num [chi197QChiValue, chi197LogChiCertificate, chi197Slice,
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
private theorem chi197LogChi_valid :
    (if chi197Slice.lo = 0 then
      if chi197Slice.hi = 0 then true
      else decide (chi197Slice.hi ≤ 1 / 4) &&
        chi197LogChiCertificate.check
          (IntervalAD.const chi197Slice.hi).value
    else chi197LogChiCertificate.check
      chi197Slice.chiAD.value) = true := by
  norm_num [chi197Slice, chi197LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi197ValidityFacts :
    ChiFacts chi197Slice chi197LogChiCertificate :=
  { domain := by norm_num [chi197Slice]
    onePlusPositive := by
      norm_num [chi197Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi197LogChi_valid }

noncomputable def chi197InputQChi : RationalEnclosure :=
  { lower := (-2316085/8388608), upper := (-2239577/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi197InputQChi_eq :
    chi197InputQChi = outerEnclosure 24 chi197QChiValue := by
  rfl'

theorem chi197RoundedFacts :
    ChiRoundedFacts 8 chi197Slice chi197LogChiCertificate
      chi197InputQChi :=
  { coversQChi := by
      rw [chi197InputQChi_eq, chi197QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi198Slice : ChiSlice :=
  { lo := (55/256), hi := (7/32) }

noncomputable def chi198LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (55/32) }, upper := { exponent := -3, mantissa := (7/4) } }

private noncomputable def chi198QChiValue : RationalEnclosure :=
  { lower := (-22872649898991513787620435194801138/82599320537645141833401778857891585), upper := (-27963483176174281170832801711710420203261167419415799/104389636343647692990592072613414530944829711885006080) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi198QChiValue_eq :
    chi198QChiValue =
      (chi198Slice.qChiAD 8 chi198LogChiCertificate).value := by
  norm_num [chi198QChiValue, chi198LogChiCertificate, chi198Slice,
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
private theorem chi198LogChi_valid :
    (if chi198Slice.lo = 0 then
      if chi198Slice.hi = 0 then true
      else decide (chi198Slice.hi ≤ 1 / 4) &&
        chi198LogChiCertificate.check
          (IntervalAD.const chi198Slice.hi).value
    else chi198LogChiCertificate.check
      chi198Slice.chiAD.value) = true := by
  norm_num [chi198Slice, chi198LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi198ValidityFacts :
    ChiFacts chi198Slice chi198LogChiCertificate :=
  { domain := by norm_num [chi198Slice]
    onePlusPositive := by
      norm_num [chi198Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi198LogChi_valid }

noncomputable def chi198InputQChi : RationalEnclosure :=
  { lower := (-2322897/8388608), upper := (-2247107/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi198InputQChi_eq :
    chi198InputQChi = outerEnclosure 24 chi198QChiValue := by
  rfl'

theorem chi198RoundedFacts :
    ChiRoundedFacts 8 chi198Slice chi198LogChiCertificate
      chi198InputQChi :=
  { coversQChi := by
      rw [chi198InputQChi_eq, chi198QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi199Slice : ChiSlice :=
  { lo := (29/128), hi := (59/256) }

noncomputable def chi199LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (29/16) }, upper := { exponent := -3, mantissa := (59/32) } }

private noncomputable def chi199QChiValue : RationalEnclosure :=
  { lower := (-33057791893716684366534583927321/118495725024165354832763671875000), upper := (-124169231149145105307514707325259862101553252111031108576794727/459558510038270813252692421781494752924792258053515625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi199QChiValue_eq :
    chi199QChiValue =
      (chi199Slice.qChiAD 8 chi199LogChiCertificate).value := by
  norm_num [chi199QChiValue, chi199LogChiCertificate, chi199Slice,
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
private theorem chi199LogChi_valid :
    (if chi199Slice.lo = 0 then
      if chi199Slice.hi = 0 then true
      else decide (chi199Slice.hi ≤ 1 / 4) &&
        chi199LogChiCertificate.check
          (IntervalAD.const chi199Slice.hi).value
    else chi199LogChiCertificate.check
      chi199Slice.chiAD.value) = true := by
  norm_num [chi199Slice, chi199LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi199ValidityFacts :
    ChiFacts chi199Slice chi199LogChiCertificate :=
  { domain := by norm_num [chi199Slice]
    onePlusPositive := by
      norm_num [chi199Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi199LogChi_valid }

noncomputable def chi199InputQChi : RationalEnclosure :=
  { lower := (-585061/2097152), upper := (-1133269/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi199InputQChi_eq :
    chi199InputQChi = outerEnclosure 24 chi199QChiValue := by
  rfl'

theorem chi199RoundedFacts :
    ChiRoundedFacts 8 chi199Slice chi199LogChiCertificate
      chi199InputQChi :=
  { coversQChi := by
      rw [chi199InputQChi_eq, chi199QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi200Slice : ChiSlice :=
  { lo := (59/256), hi := (15/64) }

noncomputable def chi200LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (59/32) }, upper := { exponent := -3, mantissa := (15/8) } }

private noncomputable def chi200QChiValue : RationalEnclosure :=
  { lower := (-1125853652236568113267893039542483173951/4027371476041881049995916416156503594835), upper := (-88230217373355935525540699594539665870460221322092001868373829109/325759842061605083563096467855226383991352426924803250801463379200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi200QChiValue_eq :
    chi200QChiValue =
      (chi200Slice.qChiAD 8 chi200LogChiCertificate).value := by
  norm_num [chi200QChiValue, chi200LogChiCertificate, chi200Slice,
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
private theorem chi200LogChi_valid :
    (if chi200Slice.lo = 0 then
      if chi200Slice.hi = 0 then true
      else decide (chi200Slice.hi ≤ 1 / 4) &&
        chi200LogChiCertificate.check
          (IntervalAD.const chi200Slice.hi).value
    else chi200LogChiCertificate.check
      chi200Slice.chiAD.value) = true := by
  norm_num [chi200Slice, chi200LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi200ValidityFacts :
    ChiFacts chi200Slice chi200LogChiCertificate :=
  { domain := by norm_num [chi200Slice]
    onePlusPositive := by
      norm_num [chi200Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi200LogChi_valid }

noncomputable def chi200InputQChi : RationalEnclosure :=
  { lower := (-4690079/16777216), upper := (-2272007/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi200InputQChi_eq :
    chi200InputQChi = outerEnclosure 24 chi200QChiValue := by
  rfl'

theorem chi200RoundedFacts :
    ChiRoundedFacts 8 chi200Slice chi200LogChiCertificate
      chi200InputQChi :=
  { coversQChi := by
      rw [chi200InputQChi_eq, chi200QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi201Slice : ChiSlice :=
  { lo := (7/32), hi := (57/256) }

noncomputable def chi201LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (7/4) }, upper := { exponent := -3, mantissa := (57/32) } }

private noncomputable def chi201QChiValue : RationalEnclosure :=
  { lower := (-3150125821594869256403700493/11345243604025246800465540960), upper := (-606103303150927654115167225687905291854977413003472453901908907/2255605227020991451172518245442108641174508635275654650764072960) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi201QChiValue_eq :
    chi201QChiValue =
      (chi201Slice.qChiAD 8 chi201LogChiCertificate).value := by
  norm_num [chi201QChiValue, chi201LogChiCertificate, chi201Slice,
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
private theorem chi201LogChi_valid :
    (if chi201Slice.lo = 0 then
      if chi201Slice.hi = 0 then true
      else decide (chi201Slice.hi ≤ 1 / 4) &&
        chi201LogChiCertificate.check
          (IntervalAD.const chi201Slice.hi).value
    else chi201LogChiCertificate.check
      chi201Slice.chiAD.value) = true := by
  norm_num [chi201Slice, chi201LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi201ValidityFacts :
    ChiFacts chi201Slice chi201LogChiCertificate :=
  { domain := by norm_num [chi201Slice]
    onePlusPositive := by
      norm_num [chi201Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi201LogChi_valid }

noncomputable def chi201InputQChi : RationalEnclosure :=
  { lower := (-2329185/8388608), upper := (-2254101/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi201InputQChi_eq :
    chi201InputQChi = outerEnclosure 24 chi201QChiValue := by
  rfl'

theorem chi201RoundedFacts :
    ChiRoundedFacts 8 chi201Slice chi201LogChiCertificate
      chi201InputQChi :=
  { coversQChi := by
      rw [chi201InputQChi_eq, chi201QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi202Slice : ChiSlice :=
  { lo := (57/256), hi := (29/128) }

noncomputable def chi202LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (57/32) }, upper := { exponent := -3, mantissa := (29/16) } }

private noncomputable def chi202QChiValue : RationalEnclosure :=
  { lower := (-2178900608332185349812011733745421629980259/7827937247632897384237057930602581544034590), upper := (-107667017518798830304497386933820984718944276760789737611473173859/399534086145040818875619194406110129628967623565485070312500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi202QChiValue_eq :
    chi202QChiValue =
      (chi202Slice.qChiAD 8 chi202LogChiCertificate).value := by
  norm_num [chi202QChiValue, chi202LogChiCertificate, chi202Slice,
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
private theorem chi202LogChi_valid :
    (if chi202Slice.lo = 0 then
      if chi202Slice.hi = 0 then true
      else decide (chi202Slice.hi ≤ 1 / 4) &&
        chi202LogChiCertificate.check
          (IntervalAD.const chi202Slice.hi).value
    else chi202LogChiCertificate.check
      chi202Slice.chiAD.value) = true := by
  norm_num [chi202Slice, chi202LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi202ValidityFacts :
    ChiFacts chi202Slice chi202LogChiCertificate :=
  { domain := by norm_num [chi202Slice]
    onePlusPositive := by
      norm_num [chi202Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi202LogChi_valid }

noncomputable def chi202InputQChi : RationalEnclosure :=
  { lower := (-2334963/8388608), upper := (-1130287/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi202InputQChi_eq :
    chi202InputQChi = outerEnclosure 24 chi202QChiValue := by
  rfl'

theorem chi202RoundedFacts :
    ChiRoundedFacts 8 chi202Slice chi202LogChiCertificate
      chi202InputQChi :=
  { coversQChi := by
      rw [chi202InputQChi_eq, chi202QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi203Slice : ChiSlice :=
  { lo := (33/256), hi := (67/512) }

noncomputable def chi203LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (33/32) }, upper := { exponent := -3, mantissa := (67/64) } }

private noncomputable def chi203QChiValue : RationalEnclosure :=
  { lower := (-278700511684372641935402478644821344121/1173596507213891103435244251708984375000), upper := (-119870603299129072344187654909565780108015614188582561295115797263618286372981/517139624141722512268687364944833095450951092180088826498255720468750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi203QChiValue_eq :
    chi203QChiValue =
      (chi203Slice.qChiAD 8 chi203LogChiCertificate).value := by
  norm_num [chi203QChiValue, chi203LogChiCertificate, chi203Slice,
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
private theorem chi203LogChi_valid :
    (if chi203Slice.lo = 0 then
      if chi203Slice.hi = 0 then true
      else decide (chi203Slice.hi ≤ 1 / 4) &&
        chi203LogChiCertificate.check
          (IntervalAD.const chi203Slice.hi).value
    else chi203LogChiCertificate.check
      chi203Slice.chiAD.value) = true := by
  norm_num [chi203Slice, chi203LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi203ValidityFacts :
    ChiFacts chi203Slice chi203LogChiCertificate :=
  { domain := by norm_num [chi203Slice]
    onePlusPositive := by
      norm_num [chi203Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi203LogChi_valid }

noncomputable def chi203InputQChi : RationalEnclosure :=
  { lower := (-996045/4194304), upper := (-1944441/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi203InputQChi_eq :
    chi203InputQChi = outerEnclosure 24 chi203QChiValue := by
  rfl'

theorem chi203RoundedFacts :
    ChiRoundedFacts 8 chi203Slice chi203LogChiCertificate
      chi203InputQChi :=
  { coversQChi := by
      rw [chi203InputQChi_eq, chi203QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi204Slice : ChiSlice :=
  { lo := (67/512), hi := (17/128) }

noncomputable def chi204LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (67/64) }, upper := { exponent := -3, mantissa := (17/16) } }

private noncomputable def chi204QChiValue : RationalEnclosure :=
  { lower := (-570260944347410913234816234165650880565045789/2387651298893526844307255049303152136208860015), upper := (-10673993079979304846235671647728686288742298604527345144194197315/45773631531104833056405063860214790187888343680345198077055712768) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi204QChiValue_eq :
    chi204QChiValue =
      (chi204Slice.qChiAD 8 chi204LogChiCertificate).value := by
  norm_num [chi204QChiValue, chi204LogChiCertificate, chi204Slice,
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
private theorem chi204LogChi_valid :
    (if chi204Slice.lo = 0 then
      if chi204Slice.hi = 0 then true
      else decide (chi204Slice.hi ≤ 1 / 4) &&
        chi204LogChiCertificate.check
          (IntervalAD.const chi204Slice.hi).value
    else chi204LogChiCertificate.check
      chi204Slice.chiAD.value) = true := by
  norm_num [chi204Slice, chi204LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi204ValidityFacts :
    ChiFacts chi204Slice chi204LogChiCertificate :=
  { domain := by norm_num [chi204Slice]
    onePlusPositive := by
      norm_num [chi204Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi204LogChi_valid }

noncomputable def chi204InputQChi : RationalEnclosure :=
  { lower := (-4007031/16777216), upper := (-3912293/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi204InputQChi_eq :
    chi204InputQChi = outerEnclosure 24 chi204QChiValue := by
  rfl'

theorem chi204RoundedFacts :
    ChiRoundedFacts 8 chi204Slice chi204LogChiCertificate
      chi204InputQChi :=
  { coversQChi := by
      rw [chi204InputQChi_eq, chi204QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi205Slice : ChiSlice :=
  { lo := (1/8), hi := (65/512) }

noncomputable def chi205LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -3, mantissa := (65/64) } }

private noncomputable def chi205QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2545610893056), upper := (-2551707636022776218628586558907343259433/11147167305203345073262610785965929103360) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi205QChiValue_eq :
    chi205QChiValue =
      (chi205Slice.qChiAD 8 chi205LogChiCertificate).value := by
  norm_num [chi205QChiValue, chi205LogChiCertificate, chi205Slice,
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
private theorem chi205LogChi_valid :
    (if chi205Slice.lo = 0 then
      if chi205Slice.hi = 0 then true
      else decide (chi205Slice.hi ≤ 1 / 4) &&
        chi205LogChiCertificate.check
          (IntervalAD.const chi205Slice.hi).value
    else chi205LogChiCertificate.check
      chi205Slice.chiAD.value) = true := by
  norm_num [chi205Slice, chi205LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi205ValidityFacts :
    ChiFacts chi205Slice chi205LogChiCertificate :=
  { domain := by norm_num [chi205Slice]
    onePlusPositive := by
      norm_num [chi205Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi205LogChi_valid }

noncomputable def chi205InputQChi : RationalEnclosure :=
  { lower := (-3936929/16777216), upper := (-1920243/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi205InputQChi_eq :
    chi205InputQChi = outerEnclosure 24 chi205QChiValue := by
  rfl'

theorem chi205RoundedFacts :
    ChiRoundedFacts 8 chi205Slice chi205LogChiCertificate
      chi205InputQChi :=
  { coversQChi := by
      rw [chi205InputQChi_eq, chi205QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi206Slice : ChiSlice :=
  { lo := (65/512), hi := (33/256) }

noncomputable def chi206LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (65/64) }, upper := { exponent := -3, mantissa := (33/32) } }

private noncomputable def chi206QChiValue : RationalEnclosure :=
  { lower := (-5651028584819596233050544150710110367/23936621910032484815300017612353596430), upper := (-3268062472906781117970362678693798516857164448668770054178005550299/14186210713599229023132898847849351303783609404738625015625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi206QChiValue_eq :
    chi206QChiValue =
      (chi206Slice.qChiAD 8 chi206LogChiCertificate).value := by
  norm_num [chi206QChiValue, chi206LogChiCertificate, chi206Slice,
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
private theorem chi206LogChi_valid :
    (if chi206Slice.lo = 0 then
      if chi206Slice.hi = 0 then true
      else decide (chi206Slice.hi ≤ 1 / 4) &&
        chi206LogChiCertificate.check
          (IntervalAD.const chi206Slice.hi).value
    else chi206LogChiCertificate.check
      chi206Slice.chiAD.value) = true := by
  norm_num [chi206Slice, chi206LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi206ValidityFacts :
    ChiFacts chi206Slice chi206LogChiCertificate :=
  { domain := by norm_num [chi206Slice]
    onePlusPositive := by
      norm_num [chi206Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi206LogChi_valid }

noncomputable def chi206InputQChi : RationalEnclosure :=
  { lower := (-3960815/16777216), upper := (-3864949/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi206InputQChi_eq :
    chi206InputQChi = outerEnclosure 24 chi206QChiValue := by
  rfl'

theorem chi206RoundedFacts :
    ChiRoundedFacts 8 chi206Slice chi206LogChiCertificate
      chi206InputQChi :=
  { coversQChi := by
      rw [chi206InputQChi_eq, chi206QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi207Slice : ChiSlice :=
  { lo := (17/128), hi := (69/512) }

noncomputable def chi207LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (17/16) }, upper := { exponent := -3, mantissa := (69/64) } }

private noncomputable def chi207QChiValue : RationalEnclosure :=
  { lower := (-15195903376325887834426762139/63271550868602337925673209200), upper := (-37337665581335567888564076383279315304672101375997822770044052927/159184563998345588441436128006877598149786717471403785745554278400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi207QChiValue_eq :
    chi207QChiValue =
      (chi207Slice.qChiAD 8 chi207LogChiCertificate).value := by
  norm_num [chi207QChiValue, chi207LogChiCertificate, chi207Slice,
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
private theorem chi207LogChi_valid :
    (if chi207Slice.lo = 0 then
      if chi207Slice.hi = 0 then true
      else decide (chi207Slice.hi ≤ 1 / 4) &&
        chi207LogChiCertificate.check
          (IntervalAD.const chi207Slice.hi).value
    else chi207LogChiCertificate.check
      chi207Slice.chiAD.value) = true := by
  norm_num [chi207Slice, chi207LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi207ValidityFacts :
    ChiFacts chi207Slice chi207LogChiCertificate :=
  { domain := by norm_num [chi207Slice]
    onePlusPositive := by
      norm_num [chi207Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi207LogChi_valid }

noncomputable def chi207InputQChi : RationalEnclosure :=
  { lower := (-2014689/8388608), upper := (-3935193/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi207InputQChi_eq :
    chi207InputQChi = outerEnclosure 24 chi207QChiValue := by
  rfl'

theorem chi207RoundedFacts :
    ChiRoundedFacts 8 chi207Slice chi207LogChiCertificate
      chi207InputQChi :=
  { coversQChi := by
      rw [chi207InputQChi_eq, chi207QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi208Slice : ChiSlice :=
  { lo := (69/512), hi := (35/256) }

noncomputable def chi208LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (69/64) }, upper := { exponent := -3, mantissa := (35/32) } }

private noncomputable def chi208QChiValue : RationalEnclosure :=
  { lower := (-5927949065769413983563611493102595148987629/24549212251599285035410150689541539904004262), upper := (-7431929900295405776596349365375516160745054858645861348669569860342728380759/31505806084256182488775880495774186765288800533628984085027051854781366487552) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi208QChiValue_eq :
    chi208QChiValue =
      (chi208Slice.qChiAD 8 chi208LogChiCertificate).value := by
  norm_num [chi208QChiValue, chi208LogChiCertificate, chi208Slice,
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
private theorem chi208LogChi_valid :
    (if chi208Slice.lo = 0 then
      if chi208Slice.hi = 0 then true
      else decide (chi208Slice.hi ≤ 1 / 4) &&
        chi208LogChiCertificate.check
          (IntervalAD.const chi208Slice.hi).value
    else chi208LogChiCertificate.check
      chi208Slice.chiAD.value) = true := by
  norm_num [chi208Slice, chi208LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi208ValidityFacts :
    ChiFacts chi208Slice chi208LogChiCertificate :=
  { domain := by norm_num [chi208Slice]
    onePlusPositive := by
      norm_num [chi208Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi208LogChi_valid }

noncomputable def chi208InputQChi : RationalEnclosure :=
  { lower := (-2025615/8388608), upper := (-1978795/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi208InputQChi_eq :
    chi208InputQChi = outerEnclosure 24 chi208QChiValue := by
  rfl'

theorem chi208RoundedFacts :
    ChiRoundedFacts 8 chi208Slice chi208LogChiCertificate
      chi208InputQChi :=
  { coversQChi := by
      rw [chi208InputQChi_eq, chi208QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi209Slice : ChiSlice :=
  { lo := (21/128), hi := (85/512) }

noncomputable def chi209LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (21/16) }, upper := { exponent := -3, mantissa := (85/64) } }

private noncomputable def chi209QChiValue : RationalEnclosure :=
  { lower := (-2943322663777069438583413144268273099/11417867801537222146173769472683911984), upper := (-1060211961236556121264420481737754699860779078004042615358899137153675309467/4196470968799073623630157661275076538698778906741065790626661593637678663680) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi209QChiValue_eq :
    chi209QChiValue =
      (chi209Slice.qChiAD 8 chi209LogChiCertificate).value := by
  norm_num [chi209QChiValue, chi209LogChiCertificate, chi209Slice,
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
private theorem chi209LogChi_valid :
    (if chi209Slice.lo = 0 then
      if chi209Slice.hi = 0 then true
      else decide (chi209Slice.hi ≤ 1 / 4) &&
        chi209LogChiCertificate.check
          (IntervalAD.const chi209Slice.hi).value
    else chi209LogChiCertificate.check
      chi209Slice.chiAD.value) = true := by
  norm_num [chi209Slice, chi209LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi209ValidityFacts :
    ChiFacts chi209Slice chi209LogChiCertificate :=
  { domain := by norm_num [chi209Slice]
    onePlusPositive := by
      norm_num [chi209Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi209LogChi_valid }

noncomputable def chi209InputQChi : RationalEnclosure :=
  { lower := (-1081217/4194304), upper := (-4238657/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi209InputQChi_eq :
    chi209InputQChi = outerEnclosure 24 chi209QChiValue := by
  rfl'

theorem chi209RoundedFacts :
    ChiRoundedFacts 8 chi209Slice chi209LogChiCertificate
      chi209InputQChi :=
  { coversQChi := by
      rw [chi209InputQChi_eq, chi209QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi210Slice : ChiSlice :=
  { lo := (85/512), hi := (43/256) }

noncomputable def chi210LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (85/64) }, upper := { exponent := -3, mantissa := (43/32) } }

private noncomputable def chi210QChiValue : RationalEnclosure :=
  { lower := (-8785626358475171547293496348977793715426579289/33964189520879215970467015381363656173597887710), upper := (-36921434779834693765452121895549454227885028936085082481179314833377759/145611257709804641527660882308997483494881330599308013916015625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi210QChiValue_eq :
    chi210QChiValue =
      (chi210Slice.qChiAD 8 chi210LogChiCertificate).value := by
  norm_num [chi210QChiValue, chi210LogChiCertificate, chi210Slice,
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
private theorem chi210LogChi_valid :
    (if chi210Slice.lo = 0 then
      if chi210Slice.hi = 0 then true
      else decide (chi210Slice.hi ≤ 1 / 4) &&
        chi210LogChiCertificate.check
          (IntervalAD.const chi210Slice.hi).value
    else chi210LogChiCertificate.check
      chi210Slice.chiAD.value) = true := by
  norm_num [chi210Slice, chi210LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi210ValidityFacts :
    ChiFacts chi210Slice chi210LogChiCertificate :=
  { domain := by norm_num [chi210Slice]
    onePlusPositive := by
      norm_num [chi210Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi210LogChi_valid }

noncomputable def chi210InputQChi : RationalEnclosure :=
  { lower := (-4339817/16777216), upper := (-4254059/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi210InputQChi_eq :
    chi210InputQChi = outerEnclosure 24 chi210QChiValue := by
  rfl'

theorem chi210RoundedFacts :
    ChiRoundedFacts 8 chi210Slice chi210LogChiCertificate
      chi210InputQChi :=
  { coversQChi := by
      rw [chi210InputQChi_eq, chi210QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi211Slice : ChiSlice :=
  { lo := (43/256), hi := (87/512) }

noncomputable def chi211LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (43/32) }, upper := { exponent := -3, mantissa := (87/64) } }

private noncomputable def chi211QChiValue : RationalEnclosure :=
  { lower := (-41523276908569225197439455082527593/159986820675171911716461181640625000), upper := (-43791267844310336589367358403925902759243062953245209256644082477967136093/172096963377555360179528396400940404899708637513413429260253906250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi211QChiValue_eq :
    chi211QChiValue =
      (chi211Slice.qChiAD 8 chi211LogChiCertificate).value := by
  norm_num [chi211QChiValue, chi211LogChiCertificate, chi211Slice,
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
private theorem chi211LogChi_valid :
    (if chi211Slice.lo = 0 then
      if chi211Slice.hi = 0 then true
      else decide (chi211Slice.hi ≤ 1 / 4) &&
        chi211LogChiCertificate.check
          (IntervalAD.const chi211Slice.hi).value
    else chi211LogChiCertificate.check
      chi211Slice.chiAD.value) = true := by
  norm_num [chi211Slice, chi211LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi211ValidityFacts :
    ChiFacts chi211Slice chi211LogChiCertificate :=
  { domain := by norm_num [chi211Slice]
    onePlusPositive := by
      norm_num [chi211Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi211LogChi_valid }

noncomputable def chi211InputQChi : RationalEnclosure :=
  { lower := (-2177195/8388608), upper := (-4269079/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi211InputQChi_eq :
    chi211InputQChi = outerEnclosure 24 chi211QChiValue := by
  rfl'

theorem chi211RoundedFacts :
    ChiRoundedFacts 8 chi211Slice chi211LogChiCertificate
      chi211InputQChi :=
  { coversQChi := by
      rw [chi211InputQChi_eq, chi211QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi212Slice : ChiSlice :=
  { lo := (87/512), hi := (11/64) }

noncomputable def chi212LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (87/64) }, upper := { exponent := -3, mantissa := (11/8) } }

private noncomputable def chi212QChiValue : RationalEnclosure :=
  { lower := (-492643658771792304067085381058029960433035234/1891956946043588234088646248042193791301379565), upper := (-11264400189153794886038805729151017453221625350981739139865952905273/44117051493798439942425127688002480205693032869993323865316392860160) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi212QChiValue_eq :
    chi212QChiValue =
      (chi212Slice.qChiAD 8 chi212LogChiCertificate).value := by
  norm_num [chi212QChiValue, chi212LogChiCertificate, chi212Slice,
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
private theorem chi212LogChi_valid :
    (if chi212Slice.lo = 0 then
      if chi212Slice.hi = 0 then true
      else decide (chi212Slice.hi ≤ 1 / 4) &&
        chi212LogChiCertificate.check
          (IntervalAD.const chi212Slice.hi).value
    else chi212LogChiCertificate.check
      chi212Slice.chiAD.value) = true := by
  norm_num [chi212Slice, chi212LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi212ValidityFacts :
    ChiFacts chi212Slice chi212LogChiCertificate :=
  { domain := by norm_num [chi212Slice]
    onePlusPositive := by
      norm_num [chi212Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi212LogChi_valid }

noncomputable def chi212InputQChi : RationalEnclosure :=
  { lower := (-4368593/16777216), upper := (-1070931/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi212InputQChi_eq :
    chi212InputQChi = outerEnclosure 24 chi212QChiValue := by
  rfl'

theorem chi212RoundedFacts :
    ChiRoundedFacts 8 chi212Slice chi212LogChiCertificate
      chi212InputQChi :=
  { coversQChi := by
      rw [chi212InputQChi_eq, chi212QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi213Slice : ChiSlice :=
  { lo := (47/256), hi := (95/512) }

noncomputable def chi213LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (47/32) }, upper := { exponent := -3, mantissa := (95/64) } }

private noncomputable def chi213QChiValue : RationalEnclosure :=
  { lower := (-269538139110587867540395215519045340729099/1014359458367179130656080227774836173547032), upper := (-28566581888013797848141726821396794892959065416765617133510226551498316979/109517163951407592457379514536937324767051115908987333130864522732131429376) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi213QChiValue_eq :
    chi213QChiValue =
      (chi213Slice.qChiAD 8 chi213LogChiCertificate).value := by
  norm_num [chi213QChiValue, chi213LogChiCertificate, chi213Slice,
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
private theorem chi213LogChi_valid :
    (if chi213Slice.lo = 0 then
      if chi213Slice.hi = 0 then true
      else decide (chi213Slice.hi ≤ 1 / 4) &&
        chi213LogChiCertificate.check
          (IntervalAD.const chi213Slice.hi).value
    else chi213LogChiCertificate.check
      chi213Slice.chiAD.value) = true := by
  norm_num [chi213Slice, chi213LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi213ValidityFacts :
    ChiFacts chi213Slice chi213LogChiCertificate :=
  { domain := by norm_num [chi213Slice]
    onePlusPositive := by
      norm_num [chi213Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi213LogChi_valid }

noncomputable def chi213InputQChi : RationalEnclosure :=
  { lower := (-1114521/4194304), upper := (-1094047/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi213InputQChi_eq :
    chi213InputQChi = outerEnclosure 24 chi213QChiValue := by
  rfl'

theorem chi213RoundedFacts :
    ChiRoundedFacts 8 chi213Slice chi213LogChiCertificate
      chi213InputQChi :=
  { coversQChi := by
      rw [chi213InputQChi_eq, chi213QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi214Slice : ChiSlice :=
  { lo := (95/512), hi := (3/16) }

noncomputable def chi214LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (95/64) }, upper := { exponent := -3, mantissa := (3/2) } }

private noncomputable def chi214QChiValue : RationalEnclosure :=
  { lower := (-849355947461286147896594597730412540936/3188229953684933220825677093920742965965), upper := (-24755533605801059810438565779101467794911088092242899/94650576750021454993262288725772056802085937500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi214QChiValue_eq :
    chi214QChiValue =
      (chi214Slice.qChiAD 8 chi214LogChiCertificate).value := by
  norm_num [chi214QChiValue, chi214LogChiCertificate, chi214Slice,
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
private theorem chi214LogChi_valid :
    (if chi214Slice.lo = 0 then
      if chi214Slice.hi = 0 then true
      else decide (chi214Slice.hi ≤ 1 / 4) &&
        chi214LogChiCertificate.check
          (IntervalAD.const chi214Slice.hi).value
    else chi214LogChiCertificate.check
      chi214Slice.chiAD.value) = true := by
  norm_num [chi214Slice, chi214LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi214ValidityFacts :
    ChiFacts chi214Slice chi214LogChiCertificate :=
  { domain := by norm_num [chi214Slice]
    onePlusPositive := by
      norm_num [chi214Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi214LogChi_valid }

noncomputable def chi214InputQChi : RationalEnclosure :=
  { lower := (-4469511/16777216), upper := (-4388023/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi214InputQChi_eq :
    chi214InputQChi = outerEnclosure 24 chi214QChiValue := by
  rfl'

theorem chi214RoundedFacts :
    ChiRoundedFacts 8 chi214Slice chi214LogChiCertificate
      chi214InputQChi :=
  { coversQChi := by
      rw [chi214InputQChi_eq, chi214QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi215Slice : ChiSlice :=
  { lo := (11/64), hi := (89/512) }

noncomputable def chi215LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (11/8) }, upper := { exponent := -3, mantissa := (89/64) } }

private noncomputable def chi215QChiValue : RationalEnclosure :=
  { lower := (-683491749998221522425385821663701/2616604949841198745662543626316000), upper := (-17136377200326997003841390325027869676738778970839621609777547723/66891750808588649064956636010349869116673506157843029008983552000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi215QChiValue_eq :
    chi215QChiValue =
      (chi215Slice.qChiAD 8 chi215LogChiCertificate).value := by
  norm_num [chi215QChiValue, chi215LogChiCertificate, chi215Slice,
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
private theorem chi215LogChi_valid :
    (if chi215Slice.lo = 0 then
      if chi215Slice.hi = 0 then true
      else decide (chi215Slice.hi ≤ 1 / 4) &&
        chi215LogChiCertificate.check
          (IntervalAD.const chi215Slice.hi).value
    else chi215LogChiCertificate.check
      chi215Slice.chiAD.value) = true := by
  norm_num [chi215Slice, chi215LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi215ValidityFacts :
    ChiFacts chi215Slice chi215LogChiCertificate :=
  { domain := by norm_num [chi215Slice]
    onePlusPositive := by
      norm_num [chi215Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi215LogChi_valid }

noncomputable def chi215InputQChi : RationalEnclosure :=
  { lower := (-4382431/16777216), upper := (-4297999/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi215InputQChi_eq :
    chi215InputQChi = outerEnclosure 24 chi215QChiValue := by
  rfl'

theorem chi215RoundedFacts :
    ChiRoundedFacts 8 chi215Slice chi215LogChiCertificate
      chi215InputQChi :=
  { coversQChi := by
      rw [chi215InputQChi_eq, chi215QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi216Slice : ChiSlice :=
  { lo := (89/512), hi := (45/256) }

noncomputable def chi216LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (89/64) }, upper := { exponent := -3, mantissa := (45/32) } }

private noncomputable def chi216QChiValue : RationalEnclosure :=
  { lower := (-61932338525228203890905275685501636087/236368039299468498450625089043207895238), upper := (-2583499775803705566129969294753850514433899683207052559324825234023657/10052141307839718307679119560952358155996525084331963151605729201303040) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi216QChiValue_eq :
    chi216QChiValue =
      (chi216Slice.qChiAD 8 chi216LogChiCertificate).value := by
  norm_num [chi216QChiValue, chi216LogChiCertificate, chi216Slice,
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
private theorem chi216LogChi_valid :
    (if chi216Slice.lo = 0 then
      if chi216Slice.hi = 0 then true
      else decide (chi216Slice.hi ≤ 1 / 4) &&
        chi216LogChiCertificate.check
          (IntervalAD.const chi216Slice.hi).value
    else chi216LogChiCertificate.check
      chi216Slice.chiAD.value) = true := by
  norm_num [chi216Slice, chi216LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi216ValidityFacts :
    ChiFacts chi216Slice chi216LogChiCertificate :=
  { domain := by norm_num [chi216Slice]
    onePlusPositive := by
      norm_num [chi216Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi216LogChi_valid }

noncomputable def chi216InputQChi : RationalEnclosure :=
  { lower := (-4395909/16777216), upper := (-2155955/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi216InputQChi_eq :
    chi216InputQChi = outerEnclosure 24 chi216QChiValue := by
  rfl'

theorem chi216RoundedFacts :
    ChiRoundedFacts 8 chi216Slice chi216LogChiCertificate
      chi216InputQChi :=
  { coversQChi := by
      rw [chi216InputQChi_eq, chi216QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi217Slice : ChiSlice :=
  { lo := (45/256), hi := (91/512) }

noncomputable def chi217LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (45/32) }, upper := { exponent := -3, mantissa := (91/64) } }

private noncomputable def chi217QChiValue : RationalEnclosure :=
  { lower := (-128626807158806288109929823763498428943/489449788626813682879668379298839875720), upper := (-126938973876452523980190781076334498185946798868985785070767790359504111602317/492359461041932538553781876266763009138815065478220403086556254343750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi217QChiValue_eq :
    chi217QChiValue =
      (chi217Slice.qChiAD 8 chi217LogChiCertificate).value := by
  norm_num [chi217QChiValue, chi217LogChiCertificate, chi217Slice,
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
private theorem chi217LogChi_valid :
    (if chi217Slice.lo = 0 then
      if chi217Slice.hi = 0 then true
      else decide (chi217Slice.hi ≤ 1 / 4) &&
        chi217LogChiCertificate.check
          (IntervalAD.const chi217Slice.hi).value
    else chi217LogChiCertificate.check
      chi217Slice.chiAD.value) = true := by
  norm_num [chi217Slice, chi217LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi217ValidityFacts :
    ChiFacts chi217Slice chi217LogChiCertificate :=
  { domain := by norm_num [chi217Slice]
    onePlusPositive := by
      norm_num [chi217Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi217LogChi_valid }

noncomputable def chi217InputQChi : RationalEnclosure :=
  { lower := (-551129/2097152), upper := (-2162731/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi217InputQChi_eq :
    chi217InputQChi = outerEnclosure 24 chi217QChiValue := by
  rfl'

theorem chi217RoundedFacts :
    ChiRoundedFacts 8 chi217Slice chi217LogChiCertificate
      chi217InputQChi :=
  { coversQChi := by
      rw [chi217InputQChi_eq, chi217QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi218Slice : ChiSlice :=
  { lo := (91/512), hi := (23/128) }

noncomputable def chi218LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (91/64) }, upper := { exponent := -3, mantissa := (23/16) } }

private noncomputable def chi218QChiValue : RationalEnclosure :=
  { lower := (-8173263521517019376959697818408685989914318547/31010994024191354357755566230658854827880859375), upper := (-891235986313280163235236468497271389677741005217574938759800658877/3446329634030617759090092167340847387722747407076019453125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi218QChiValue_eq :
    chi218QChiValue =
      (chi218Slice.qChiAD 8 chi218LogChiCertificate).value := by
  norm_num [chi218QChiValue, chi218LogChiCertificate, chi218Slice,
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
private theorem chi218LogChi_valid :
    (if chi218Slice.lo = 0 then
      if chi218Slice.hi = 0 then true
      else decide (chi218Slice.hi ≤ 1 / 4) &&
        chi218LogChiCertificate.check
          (IntervalAD.const chi218Slice.hi).value
    else chi218LogChiCertificate.check
      chi218Slice.chiAD.value) = true := by
  norm_num [chi218Slice, chi218LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi218ValidityFacts :
    ChiFacts chi218Slice chi218LogChiCertificate :=
  { domain := by norm_num [chi218Slice]
    onePlusPositive := by
      norm_num [chi218Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi218LogChi_valid }

noncomputable def chi218InputQChi : RationalEnclosure :=
  { lower := (-4421807/16777216), upper := (-4338661/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi218InputQChi_eq :
    chi218InputQChi = outerEnclosure 24 chi218QChiValue := by
  rfl'

theorem chi218RoundedFacts :
    ChiRoundedFacts 8 chi218Slice chi218LogChiCertificate
      chi218InputQChi :=
  { coversQChi := by
      rw [chi218InputQChi_eq, chi218QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi219Slice : ChiSlice :=
  { lo := (23/128), hi := (93/512) }

noncomputable def chi219LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (23/16) }, upper := { exponent := -3, mantissa := (93/64) } }

private noncomputable def chi219QChiValue : RationalEnclosure :=
  { lower := (-180561733457002580374016815859/683166819130129686503797485840), upper := (-158798336416787839035672036435632268180823398429569399274670617035/612245542510999286201073857390312334819846809088643833215868770304) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi219QChiValue_eq :
    chi219QChiValue =
      (chi219Slice.qChiAD 8 chi219LogChiCertificate).value := by
  norm_num [chi219QChiValue, chi219LogChiCertificate, chi219Slice,
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
private theorem chi219LogChi_valid :
    (if chi219Slice.lo = 0 then
      if chi219Slice.hi = 0 then true
      else decide (chi219Slice.hi ≤ 1 / 4) &&
        chi219LogChiCertificate.check
          (IntervalAD.const chi219Slice.hi).value
    else chi219LogChiCertificate.check
      chi219Slice.chiAD.value) = true := by
  norm_num [chi219Slice, chi219LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi219ValidityFacts :
    ChiFacts chi219Slice chi219LogChiCertificate :=
  { domain := by norm_num [chi219Slice]
    onePlusPositive := by
      norm_num [chi219Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi219LogChi_valid }

noncomputable def chi219InputQChi : RationalEnclosure :=
  { lower := (-4434237/16777216), upper := (-543939/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi219InputQChi_eq :
    chi219InputQChi = outerEnclosure 24 chi219QChiValue := by
  rfl'

theorem chi219RoundedFacts :
    ChiRoundedFacts 8 chi219Slice chi219LogChiCertificate
      chi219InputQChi :=
  { coversQChi := by
      rw [chi219InputQChi_eq, chi219QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi220Slice : ChiSlice :=
  { lo := (93/512), hi := (47/256) }

noncomputable def chi220LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (93/64) }, upper := { exponent := -3, mantissa := (47/32) } }

private noncomputable def chi220QChiValue : RationalEnclosure :=
  { lower := (-19988702252569715470271654486155453408786096061/75422870843335737958642950800238450237903683550), upper := (-2083802998163471404149568255800490655336371574987528145461596474187128976905717571/8011058076275504342600709603651828725205747080615495263445678705604984730527859200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi220QChiValue_eq :
    chi220QChiValue =
      (chi220Slice.qChiAD 8 chi220LogChiCertificate).value := by
  norm_num [chi220QChiValue, chi220LogChiCertificate, chi220Slice,
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
private theorem chi220LogChi_valid :
    (if chi220Slice.lo = 0 then
      if chi220Slice.hi = 0 then true
      else decide (chi220Slice.hi ≤ 1 / 4) &&
        chi220LogChiCertificate.check
          (IntervalAD.const chi220Slice.hi).value
    else chi220LogChiCertificate.check
      chi220Slice.chiAD.value) = true := by
  norm_num [chi220Slice, chi220LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi220ValidityFacts :
    ChiFacts chi220Slice chi220LogChiCertificate :=
  { domain := by norm_num [chi220Slice]
    onePlusPositive := by
      norm_num [chi220Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi220LogChi_valid }

noncomputable def chi220InputQChi : RationalEnclosure :=
  { lower := (-555791/2097152), upper := (-4364019/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi220InputQChi_eq :
    chi220InputQChi = outerEnclosure 24 chi220QChiValue := by
  rfl'

theorem chi220RoundedFacts :
    ChiRoundedFacts 8 chi220Slice chi220LogChiCertificate
      chi220InputQChi :=
  { coversQChi := by
      rw [chi220InputQChi_eq, chi220QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi221Slice : ChiSlice :=
  { lo := (3/16), hi := (97/512) }

noncomputable def chi221LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (3/2) }, upper := { exponent := -3, mantissa := (97/64) } }

private noncomputable def chi221QChiValue : RationalEnclosure :=
  { lower := (-74920461640015458265049/280532341933593750000000), upper := (-24821113111695303445840938748860085173637250334973452439611367/94653114799252905939396229059924427719682067827500000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi221QChiValue_eq :
    chi221QChiValue =
      (chi221Slice.qChiAD 8 chi221LogChiCertificate).value := by
  norm_num [chi221QChiValue, chi221LogChiCertificate, chi221Slice,
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
private theorem chi221LogChi_valid :
    (if chi221Slice.lo = 0 then
      if chi221Slice.hi = 0 then true
      else decide (chi221Slice.hi ≤ 1 / 4) &&
        chi221LogChiCertificate.check
          (IntervalAD.const chi221Slice.hi).value
    else chi221LogChiCertificate.check
      chi221Slice.chiAD.value) = true := by
  norm_num [chi221Slice, chi221LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi221ValidityFacts :
    ChiFacts chi221Slice chi221LogChiCertificate :=
  { domain := by norm_num [chi221Slice]
    onePlusPositive := by
      norm_num [chi221Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi221LogChi_valid }

noncomputable def chi221InputQChi : RationalEnclosure :=
  { lower := (-4480613/16777216), upper := (-4399529/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi221InputQChi_eq :
    chi221InputQChi = outerEnclosure 24 chi221QChiValue := by
  rfl'

theorem chi221RoundedFacts :
    ChiRoundedFacts 8 chi221Slice chi221LogChiCertificate
      chi221InputQChi :=
  { coversQChi := by
      rw [chi221InputQChi_eq, chi221QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi222Slice : ChiSlice :=
  { lo := (97/512), hi := (49/256) }

noncomputable def chi222LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (97/64) }, upper := { exponent := -3, mantissa := (49/32) } }

private noncomputable def chi222QChiValue : RationalEnclosure :=
  { lower := (-86422232586831658372064073634046757216114881/322822808399901392243503145386921542490195410), upper := (-38371194168852727335187821535323643167302899901844097253856361128314965/145954184176012231096116520922661678508065053263970096204880391463683584) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi222QChiValue_eq :
    chi222QChiValue =
      (chi222Slice.qChiAD 8 chi222LogChiCertificate).value := by
  norm_num [chi222QChiValue, chi222LogChiCertificate, chi222Slice,
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
private theorem chi222LogChi_valid :
    (if chi222Slice.lo = 0 then
      if chi222Slice.hi = 0 then true
      else decide (chi222Slice.hi ≤ 1 / 4) &&
        chi222LogChiCertificate.check
          (IntervalAD.const chi222Slice.hi).value
    else chi222LogChiCertificate.check
      chi222Slice.chiAD.value) = true := by
  norm_num [chi222Slice, chi222LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi222ValidityFacts :
    ChiFacts chi222Slice chi222LogChiCertificate :=
  { domain := by norm_num [chi222Slice]
    onePlusPositive := by
      norm_num [chi222Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi222LogChi_valid }

noncomputable def chi222InputQChi : RationalEnclosure :=
  { lower := (-4491395/16777216), upper := (-4410711/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi222InputQChi_eq :
    chi222InputQChi = outerEnclosure 24 chi222QChiValue := by
  rfl'

theorem chi222RoundedFacts :
    ChiRoundedFacts 8 chi222Slice chi222LogChiCertificate
      chi222InputQChi :=
  { coversQChi := by
      rw [chi222InputQChi_eq, chi222QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi223Slice : ChiSlice :=
  { lo := (53/256), hi := (107/512) }

noncomputable def chi223LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (53/32) }, upper := { exponent := -3, mantissa := (107/64) } }

private noncomputable def chi223QChiValue : RationalEnclosure :=
  { lower := (-4228628805636802844083186716761132659375961/15507980803351782262942314487987060546875000), upper := (-7677359299865558425941939706347555653088194256087337113405729436026612502789/28639305764555303280000793671358221248551771300553440758708542343750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi223QChiValue_eq :
    chi223QChiValue =
      (chi223Slice.qChiAD 8 chi223LogChiCertificate).value := by
  norm_num [chi223QChiValue, chi223LogChiCertificate, chi223Slice,
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
private theorem chi223LogChi_valid :
    (if chi223Slice.lo = 0 then
      if chi223Slice.hi = 0 then true
      else decide (chi223Slice.hi ≤ 1 / 4) &&
        chi223LogChiCertificate.check
          (IntervalAD.const chi223Slice.hi).value
    else chi223LogChiCertificate.check
      chi223Slice.chiAD.value) = true := by
  norm_num [chi223Slice, chi223LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi223ValidityFacts :
    ChiFacts chi223Slice chi223LogChiCertificate :=
  { domain := by norm_num [chi223Slice]
    onePlusPositive := by
      norm_num [chi223Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi223LogChi_valid }

noncomputable def chi223InputQChi : RationalEnclosure :=
  { lower := (-4574717/16777216), upper := (-562185/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi223InputQChi_eq :
    chi223InputQChi = outerEnclosure 24 chi223QChiValue := by
  rfl'

theorem chi223RoundedFacts :
    ChiRoundedFacts 8 chi223Slice chi223LogChiCertificate
      chi223InputQChi :=
  { coversQChi := by
      rw [chi223InputQChi_eq, chi223QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi224Slice : ChiSlice :=
  { lo := (107/512), hi := (27/128) }

noncomputable def chi224LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (107/64) }, upper := { exponent := -3, mantissa := (27/16) } }

private noncomputable def chi224QChiValue : RationalEnclosure :=
  { lower := (-293886002532931997133009722402504254493/1075954428201195593881835021858434799205), upper := (-55450038172210403014041322363891090257055794096229246266791479409/206473219708828772712910336834733779948674944728862220065842125312) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi224QChiValue_eq :
    chi224QChiValue =
      (chi224Slice.qChiAD 8 chi224LogChiCertificate).value := by
  norm_num [chi224QChiValue, chi224LogChiCertificate, chi224Slice,
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
private theorem chi224LogChi_valid :
    (if chi224Slice.lo = 0 then
      if chi224Slice.hi = 0 then true
      else decide (chi224Slice.hi ≤ 1 / 4) &&
        chi224LogChiCertificate.check
          (IntervalAD.const chi224Slice.hi).value
    else chi224LogChiCertificate.check
      chi224Slice.chiAD.value) = true := by
  norm_num [chi224Slice, chi224LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi224ValidityFacts :
    ChiFacts chi224Slice chi224LogChiCertificate :=
  { domain := by norm_num [chi224Slice]
    onePlusPositive := by
      norm_num [chi224Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi224LogChi_valid }

noncomputable def chi224InputQChi : RationalEnclosure :=
  { lower := (-2291263/8388608), upper := (-4505655/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi224InputQChi_eq :
    chi224InputQChi = outerEnclosure 24 chi224QChiValue := by
  rfl'

theorem chi224RoundedFacts :
    ChiRoundedFacts 8 chi224Slice chi224LogChiCertificate
      chi224InputQChi :=
  { coversQChi := by
      rw [chi224InputQChi_eq, chi224QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi225Slice : ChiSlice :=
  { lo := (27/128), hi := (109/512) }

noncomputable def chi225LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (27/16) }, upper := { exponent := -3, mantissa := (109/64) } }

private noncomputable def chi225QChiValue : RationalEnclosure :=
  { lower := (-154810284166638540725901868774744524433/565850126261426504125983085324961967600), upper := (-4908170409235526634323468051967966132520205830482242954007355167239686246799143/18244040674994759036884064199063677781014928665010904286658471326587471369574400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi225QChiValue_eq :
    chi225QChiValue =
      (chi225Slice.qChiAD 8 chi225LogChiCertificate).value := by
  norm_num [chi225QChiValue, chi225LogChiCertificate, chi225Slice,
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
private theorem chi225LogChi_valid :
    (if chi225Slice.lo = 0 then
      if chi225Slice.hi = 0 then true
      else decide (chi225Slice.hi ≤ 1 / 4) &&
        chi225LogChiCertificate.check
          (IntervalAD.const chi225Slice.hi).value
    else chi225LogChiCertificate.check
      chi225Slice.chiAD.value) = true := by
  norm_num [chi225Slice, chi225LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi225ValidityFacts :
    ChiFacts chi225Slice chi225LogChiCertificate :=
  { domain := by norm_num [chi225Slice]
    onePlusPositive := by
      norm_num [chi225Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi225LogChi_valid }

noncomputable def chi225InputQChi : RationalEnclosure :=
  { lower := (-1147515/4194304), upper := (-282097/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi225InputQChi_eq :
    chi225InputQChi = outerEnclosure 24 chi225QChiValue := by
  rfl'

theorem chi225RoundedFacts :
    ChiRoundedFacts 8 chi225Slice chi225LogChiCertificate
      chi225InputQChi :=
  { coversQChi := by
      rw [chi225InputQChi_eq, chi225QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi226Slice : ChiSlice :=
  { lo := (109/512), hi := (55/256) }

noncomputable def chi226LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (109/64) }, upper := { exponent := -3, mantissa := (55/32) } }

private noncomputable def chi226QChiValue : RationalEnclosure :=
  { lower := (-1653705760720868266392850267220873013193791203/6034945547750571154580658277053070139453314578), upper := (-1862188980249979843461843418937553006092165281239828172255180771310670583/6910228817172601166018121930464374922692546242869078991772319631682705920) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi226QChiValue_eq :
    chi226QChiValue =
      (chi226Slice.qChiAD 8 chi226LogChiCertificate).value := by
  norm_num [chi226QChiValue, chi226LogChiCertificate, chi226Slice,
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
private theorem chi226LogChi_valid :
    (if chi226Slice.lo = 0 then
      if chi226Slice.hi = 0 then true
      else decide (chi226Slice.hi ≤ 1 / 4) &&
        chi226LogChiCertificate.check
          (IntervalAD.const chi226Slice.hi).value
    else chi226LogChiCertificate.check
      chi226Slice.chiAD.value) = true := by
  norm_num [chi226Slice, chi226LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi226ValidityFacts :
    ChiFacts chi226Slice chi226LogChiCertificate :=
  { domain := by norm_num [chi226Slice]
    onePlusPositive := by
      norm_num [chi226Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi226LogChi_valid }

noncomputable def chi226InputQChi : RationalEnclosure :=
  { lower := (-4597321/16777216), upper := (-4521173/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi226InputQChi_eq :
    chi226InputQChi = outerEnclosure 24 chi226QChiValue := by
  rfl'

theorem chi226RoundedFacts :
    ChiRoundedFacts 8 chi226Slice chi226LogChiCertificate
      chi226InputQChi :=
  { coversQChi := by
      rw [chi226InputQChi_eq, chi226QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi227Slice : ChiSlice :=
  { lo := (55/256), hi := (111/512) }

noncomputable def chi227LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (55/32) }, upper := { exponent := -3, mantissa := (111/64) } }

private noncomputable def chi227QChiValue : RationalEnclosure :=
  { lower := (-423144023131343005070978051103821053/1541853983369375980890166538680642920), upper := (-223845934811148223807649462023450441656902954705022984955670959551777631/829301476906267164537441570734210767952794221533775329589843750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi227QChiValue_eq :
    chi227QChiValue =
      (chi227Slice.qChiAD 8 chi227LogChiCertificate).value := by
  norm_num [chi227QChiValue, chi227LogChiCertificate, chi227Slice,
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
private theorem chi227LogChi_valid :
    (if chi227Slice.lo = 0 then
      if chi227Slice.hi = 0 then true
      else decide (chi227Slice.hi ≤ 1 / 4) &&
        chi227LogChiCertificate.check
          (IntervalAD.const chi227Slice.hi).value
    else chi227LogChiCertificate.check
      chi227Slice.chiAD.value) = true := by
  norm_num [chi227Slice, chi227LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi227ValidityFacts :
    ChiFacts chi227Slice chi227LogChiCertificate :=
  { domain := by norm_num [chi227Slice]
    onePlusPositive := by
      norm_num [chi227Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi227LogChi_valid }

noncomputable def chi227InputQChi : RationalEnclosure :=
  { lower := (-2302157/8388608), upper := (-4528523/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi227InputQChi_eq :
    chi227InputQChi = outerEnclosure 24 chi227QChiValue := by
  rfl'

theorem chi227RoundedFacts :
    ChiRoundedFacts 8 chi227Slice chi227LogChiCertificate
      chi227InputQChi :=
  { coversQChi := by
      rw [chi227InputQChi_eq, chi227QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi228Slice : ChiSlice :=
  { lo := (111/512), hi := (7/32) }

noncomputable def chi228LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (111/64) }, upper := { exponent := -3, mantissa := (7/4) } }

private noncomputable def chi228QChiValue : RationalEnclosure :=
  { lower := (-1109595481420388182742109276633825183866290108/4037249594019847273104018531739711761474609375), upper := (-4456437967243062688393295188058959634288400602084742375902844137/16484373550450652218041451326392296386830806732177734375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi228QChiValue_eq :
    chi228QChiValue =
      (chi228Slice.qChiAD 8 chi228LogChiCertificate).value := by
  norm_num [chi228QChiValue, chi228LogChiCertificate, chi228Slice,
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
private theorem chi228LogChi_valid :
    (if chi228Slice.lo = 0 then
      if chi228Slice.hi = 0 then true
      else decide (chi228Slice.hi ≤ 1 / 4) &&
        chi228LogChiCertificate.check
          (IntervalAD.const chi228Slice.hi).value
    else chi228LogChiCertificate.check
      chi228Slice.chiAD.value) = true := by
  norm_num [chi228Slice, chi228LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi228ValidityFacts :
    ChiFacts chi228Slice chi228LogChiCertificate :=
  { domain := by norm_num [chi228Slice]
    onePlusPositive := by
      norm_num [chi228Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi228LogChi_valid }

noncomputable def chi228InputQChi : RationalEnclosure :=
  { lower := (-4611041/16777216), upper := (-4535605/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi228InputQChi_eq :
    chi228InputQChi = outerEnclosure 24 chi228QChiValue := by
  rfl'

theorem chi228RoundedFacts :
    ChiRoundedFacts 8 chi228Slice chi228LogChiCertificate
      chi228InputQChi :=
  { coversQChi := by
      rw [chi228InputQChi_eq, chi228QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi229Slice : ChiSlice :=
  { lo := (7/32), hi := (113/512) }

noncomputable def chi229LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (7/4) }, upper := { exponent := -3, mantissa := (113/64) } }

private noncomputable def chi229QChiValue : RationalEnclosure :=
  { lower := (-18734958833695801367032534511/68071461624151480802793245760), upper := (-347891124382535869603820894478044941272507397751035613299061/1284918648554696133733752225638632248646506303515000128512000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi229QChiValue_eq :
    chi229QChiValue =
      (chi229Slice.qChiAD 8 chi229LogChiCertificate).value := by
  norm_num [chi229QChiValue, chi229LogChiCertificate, chi229Slice,
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
private theorem chi229LogChi_valid :
    (if chi229Slice.lo = 0 then
      if chi229Slice.hi = 0 then true
      else decide (chi229Slice.hi ≤ 1 / 4) &&
        chi229LogChiCertificate.check
          (IntervalAD.const chi229Slice.hi).value
    else chi229LogChiCertificate.check
      chi229Slice.chiAD.value) = true := by
  norm_num [chi229Slice, chi229LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi229ValidityFacts :
    ChiFacts chi229Slice chi229LogChiCertificate :=
  { domain := by norm_num [chi229Slice]
    onePlusPositive := by
      norm_num [chi229Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi229LogChi_valid }

noncomputable def chi229InputQChi : RationalEnclosure :=
  { lower := (-1154377/4194304), upper := (-4542423/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi229InputQChi_eq :
    chi229InputQChi = outerEnclosure 24 chi229QChiValue := by
  rfl'

theorem chi229RoundedFacts :
    ChiRoundedFacts 8 chi229Slice chi229LogChiCertificate
      chi229InputQChi :=
  { coversQChi := by
      rw [chi229InputQChi_eq, chi229QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi230Slice : ChiSlice :=
  { lo := (113/512), hi := (57/256) }

noncomputable def chi230LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (113/64) }, upper := { exponent := -3, mantissa := (57/32) } }

private noncomputable def chi230QChiValue : RationalEnclosure :=
  { lower := (-9040329068771577495038614772012042328413/32802964220577444957347216992943589956250), upper := (-2357736169378804529920248023303601530592085117926655625637149829210329276081/8695630831757019595204660484866798885654826597619962409673746357160286400000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi230QChiValue_eq :
    chi230QChiValue =
      (chi230Slice.qChiAD 8 chi230LogChiCertificate).value := by
  norm_num [chi230QChiValue, chi230LogChiCertificate, chi230Slice,
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
private theorem chi230LogChi_valid :
    (if chi230Slice.lo = 0 then
      if chi230Slice.hi = 0 then true
      else decide (chi230Slice.hi ≤ 1 / 4) &&
        chi230LogChiCertificate.check
          (IntervalAD.const chi230Slice.hi).value
    else chi230LogChiCertificate.check
      chi230Slice.chiAD.value) = true := by
  norm_num [chi230Slice, chi230LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi230ValidityFacts :
    ChiFacts chi230Slice chi230LogChiCertificate :=
  { domain := by norm_num [chi230Slice]
    onePlusPositive := by
      norm_num [chi230Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi230LogChi_valid }

noncomputable def chi230InputQChi : RationalEnclosure :=
  { lower := (-4623715/16777216), upper := (-4548979/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi230InputQChi_eq :
    chi230InputQChi = outerEnclosure 24 chi230QChiValue := by
  rfl'

theorem chi230RoundedFacts :
    ChiRoundedFacts 8 chi230Slice chi230LogChiCertificate
      chi230InputQChi :=
  { coversQChi := by
      rw [chi230InputQChi_eq, chi230QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi231Slice : ChiSlice :=
  { lo := (57/256), hi := (115/512) }

noncomputable def chi231LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (57/32) }, upper := { exponent := -3, mantissa := (115/64) } }

private noncomputable def chi231QChiValue : RationalEnclosure :=
  { lower := (-1728093585918629760195733444004989568605033/6262349798106317907389646344482065235227672), upper := (-544064191579987301019068417917884695458859249383032061758688775191112550298860029/2003803390161122430477028244113764721510480993602150648683437282938084905346862080) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi231QChiValue_eq :
    chi231QChiValue =
      (chi231Slice.qChiAD 8 chi231LogChiCertificate).value := by
  norm_num [chi231QChiValue, chi231LogChiCertificate, chi231Slice,
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
private theorem chi231LogChi_valid :
    (if chi231Slice.lo = 0 then
      if chi231Slice.hi = 0 then true
      else decide (chi231Slice.hi ≤ 1 / 4) &&
        chi231LogChiCertificate.check
          (IntervalAD.const chi231Slice.hi).value
    else chi231LogChiCertificate.check
      chi231Slice.chiAD.value) = true := by
  norm_num [chi231Slice, chi231LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi231ValidityFacts :
    ChiFacts chi231Slice chi231LogChiCertificate :=
  { domain := by norm_num [chi231Slice]
    onePlusPositive := by
      norm_num [chi231Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi231LogChi_valid }

noncomputable def chi231InputQChi : RationalEnclosure :=
  { lower := (-1157417/4194304), upper := (-2277639/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi231InputQChi_eq :
    chi231InputQChi = outerEnclosure 24 chi231QChiValue := by
  rfl'

theorem chi231RoundedFacts :
    ChiRoundedFacts 8 chi231Slice chi231LogChiCertificate
      chi231InputQChi :=
  { coversQChi := by
      rw [chi231InputQChi_eq, chi231QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi232Slice : ChiSlice :=
  { lo := (115/512), hi := (29/128) }

noncomputable def chi232LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (115/64) }, upper := { exponent := -3, mantissa := (29/16) } }

private noncomputable def chi232QChiValue : RationalEnclosure :=
  { lower := (-4063466978818010148431718027180440805606633043/14707278188455900570518128678625574660154833845), upper := (-15510411075747244672481055828462276158421721380422628736707803465198449/57049573358379857772233169079173966529533047501496915310640625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi232QChiValue_eq :
    chi232QChiValue =
      (chi232Slice.qChiAD 8 chi232LogChiCertificate).value := by
  norm_num [chi232QChiValue, chi232LogChiCertificate, chi232Slice,
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
private theorem chi232LogChi_valid :
    (if chi232Slice.lo = 0 then
      if chi232Slice.hi = 0 then true
      else decide (chi232Slice.hi ≤ 1 / 4) &&
        chi232LogChiCertificate.check
          (IntervalAD.const chi232Slice.hi).value
    else chi232LogChiCertificate.check
      chi232Slice.chiAD.value) = true := by
  norm_num [chi232Slice, chi232LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi232ValidityFacts :
    ChiFacts chi232Slice chi232LogChiCertificate :=
  { domain := by norm_num [chi232Slice]
    onePlusPositive := by
      norm_num [chi232Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi232LogChi_valid }

noncomputable def chi232InputQChi : RationalEnclosure :=
  { lower := (-2317685/8388608), upper := (-2280661/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi232InputQChi_eq :
    chi232InputQChi = outerEnclosure 24 chi232QChiValue := by
  rfl'

theorem chi232RoundedFacts :
    ChiRoundedFacts 8 chi232Slice chi232LogChiCertificate
      chi232InputQChi :=
  { coversQChi := by
      rw [chi232InputQChi_eq, chi232QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi233Slice : ChiSlice :=
  { lo := (29/128), hi := (117/512) }

noncomputable def chi233LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (29/16) }, upper := { exponent := -3, mantissa := (117/64) } }

private noncomputable def chi233QChiValue : RationalEnclosure :=
  { lower := (-560301557520621768924314981819/2025567949131031706542968750000), upper := (-12693248858532473866575748823694000177029533169753451023918613785682799/46628415916756553912429362162578164236615268758923707999062500000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi233QChiValue_eq :
    chi233QChiValue =
      (chi233Slice.qChiAD 8 chi233LogChiCertificate).value := by
  norm_num [chi233QChiValue, chi233LogChiCertificate, chi233Slice,
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
private theorem chi233LogChi_valid :
    (if chi233Slice.lo = 0 then
      if chi233Slice.hi = 0 then true
      else decide (chi233Slice.hi ≤ 1 / 4) &&
        chi233LogChiCertificate.check
          (IntervalAD.const chi233Slice.hi).value
    else chi233LogChiCertificate.check
      chi233Slice.chiAD.value) = true := by
  norm_num [chi233Slice, chi233LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi233ValidityFacts :
    ChiFacts chi233Slice chi233LogChiCertificate :=
  { domain := by norm_num [chi233Slice]
    onePlusPositive := by
      norm_num [chi233Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi233LogChi_valid }

noncomputable def chi233InputQChi : RationalEnclosure :=
  { lower := (-2320411/8388608), upper := (-4567115/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi233InputQChi_eq :
    chi233InputQChi = outerEnclosure 24 chi233QChiValue := by
  rfl'

theorem chi233RoundedFacts :
    ChiRoundedFacts 8 chi233Slice chi233LogChiCertificate
      chi233InputQChi :=
  { coversQChi := by
      rw [chi233InputQChi_eq, chi233QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi234Slice : ChiSlice :=
  { lo := (117/512), hi := (59/256) }

noncomputable def chi234LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (117/64) }, upper := { exponent := -3, mantissa := (59/32) } }

private noncomputable def chi234QChiValue : RationalEnclosure :=
  { lower := (-10789350847583856590608946670256367854668494809/38961282602082715736922531821416201552185358590), upper := (-13106153522562707253026155656787546327597517801862882695753068821185882721527675/48086829228681559758300748876588903809435360038521467057026746240302330972504576) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi234QChiValue_eq :
    chi234QChiValue =
      (chi234Slice.qChiAD 8 chi234LogChiCertificate).value := by
  norm_num [chi234QChiValue, chi234LogChiCertificate, chi234Slice,
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
private theorem chi234LogChi_valid :
    (if chi234Slice.lo = 0 then
      if chi234Slice.hi = 0 then true
      else decide (chi234Slice.hi ≤ 1 / 4) &&
        chi234LogChiCertificate.check
          (IntervalAD.const chi234Slice.hi).value
    else chi234LogChiCertificate.check
      chi234Slice.chiAD.value) = true := by
  norm_num [chi234Slice, chi234LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi234ValidityFacts :
    ChiFacts chi234Slice chi234LogChiCertificate :=
  { domain := by norm_num [chi234Slice]
    onePlusPositive := by
      norm_num [chi234Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi234LogChi_valid }

noncomputable def chi234InputQChi : RationalEnclosure :=
  { lower := (-2323015/8388608), upper := (-1143165/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi234InputQChi_eq :
    chi234InputQChi = outerEnclosure 24 chi234QChiValue := by
  rfl'

theorem chi234RoundedFacts :
    ChiRoundedFacts 8 chi234Slice chi234LogChiCertificate
      chi234InputQChi :=
  { coversQChi := by
      rw [chi234InputQChi_eq, chi234QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi235Slice : ChiSlice :=
  { lo := (59/256), hi := (119/512) }

noncomputable def chi235LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (59/32) }, upper := { exponent := -3, mantissa := (119/64) } }

private noncomputable def chi235QChiValue : RationalEnclosure :=
  { lower := (-19139512088021657925554181672222213957167/69040653875003675142787138562682918768600), upper := (-1101934393484980495562306777062676656993844476092385484295287924390702449/4038345914064806861022491812028395423733214913052368650551770123007308800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi235QChiValue_eq :
    chi235QChiValue =
      (chi235Slice.qChiAD 8 chi235LogChiCertificate).value := by
  norm_num [chi235QChiValue, chi235LogChiCertificate, chi235Slice,
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
private theorem chi235LogChi_valid :
    (if chi235Slice.lo = 0 then
      if chi235Slice.hi = 0 then true
      else decide (chi235Slice.hi ≤ 1 / 4) &&
        chi235LogChiCertificate.check
          (IntervalAD.const chi235Slice.hi).value
    else chi235LogChiCertificate.check
      chi235Slice.chiAD.value) = true := by
  norm_num [chi235Slice, chi235LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi235ValidityFacts :
    ChiFacts chi235Slice chi235LogChiCertificate :=
  { domain := by norm_num [chi235Slice]
    onePlusPositive := by
      norm_num [chi235Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi235LogChi_valid }

noncomputable def chi235InputQChi : RationalEnclosure :=
  { lower := (-4650995/16777216), upper := (-4577961/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi235InputQChi_eq :
    chi235InputQChi = outerEnclosure 24 chi235QChiValue := by
  rfl'

theorem chi235RoundedFacts :
    ChiRoundedFacts 8 chi235Slice chi235LogChiCertificate
      chi235InputQChi :=
  { coversQChi := by
      rw [chi235InputQChi_eq, chi235QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi236Slice : ChiSlice :=
  { lo := (119/512), hi := (15/64) }

noncomputable def chi236LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (119/64) }, upper := { exponent := -3, mantissa := (15/8) } }

private noncomputable def chi236QChiValue : RationalEnclosure :=
  { lower := (-1515293785318363165287571746385946551474/5460466947990146212214541239059699048617), upper := (-766049660567560743930208441065878498620006902845121916109299417/2804303929134504189160676179123267927864065677085923156683971072) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi236QChiValue_eq :
    chi236QChiValue =
      (chi236Slice.qChiAD 8 chi236LogChiCertificate).value := by
  norm_num [chi236QChiValue, chi236LogChiCertificate, chi236Slice,
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
private theorem chi236LogChi_valid :
    (if chi236Slice.lo = 0 then
      if chi236Slice.hi = 0 then true
      else decide (chi236Slice.hi ≤ 1 / 4) &&
        chi236LogChiCertificate.check
          (IntervalAD.const chi236Slice.hi).value
    else chi236LogChiCertificate.check
      chi236Slice.chiAD.value) = true := by
  norm_num [chi236Slice, chi236LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi236ValidityFacts :
    ChiFacts chi236Slice chi236LogChiCertificate :=
  { domain := by norm_num [chi236Slice]
    onePlusPositive := by
      norm_num [chi236Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi236LogChi_valid }

noncomputable def chi236InputQChi : RationalEnclosure :=
  { lower := (-2327861/8388608), upper := (-4583019/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi236InputQChi_eq :
    chi236InputQChi = outerEnclosure 24 chi236QChiValue := by
  rfl'

theorem chi236RoundedFacts :
    ChiRoundedFacts 8 chi236Slice chi236LogChiCertificate
      chi236InputQChi :=
  { coversQChi := by
      rw [chi236InputQChi_eq, chi236QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi237Slice : ChiSlice :=
  { lo := (15/64), hi := (121/512) }

noncomputable def chi237LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (15/8) }, upper := { exponent := -3, mantissa := (121/64) } }

private noncomputable def chi237QChiValue : RationalEnclosure :=
  { lower := (-1222392070998250992830386485679579/4400731047899083960484110741721760), upper := (-2182857848030134784997342411754327198885179161525489251832281592735595883/7982466669950543787504189441983658125958207191158725247324875000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi237QChiValue_eq :
    chi237QChiValue =
      (chi237Slice.qChiAD 8 chi237LogChiCertificate).value := by
  norm_num [chi237QChiValue, chi237LogChiCertificate, chi237Slice,
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
private theorem chi237LogChi_valid :
    (if chi237Slice.lo = 0 then
      if chi237Slice.hi = 0 then true
      else decide (chi237Slice.hi ≤ 1 / 4) &&
        chi237LogChiCertificate.check
          (IntervalAD.const chi237Slice.hi).value
    else chi237LogChiCertificate.check
      chi237Slice.chiAD.value) = true := by
  norm_num [chi237Slice, chi237LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi237ValidityFacts :
    ChiFacts chi237Slice chi237LogChiCertificate :=
  { domain := by norm_num [chi237Slice]
    onePlusPositive := by
      norm_num [chi237Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi237LogChi_valid }

noncomputable def chi237InputQChi : RationalEnclosure :=
  { lower := (-1165053/4194304), upper := (-4587839/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi237InputQChi_eq :
    chi237InputQChi = outerEnclosure 24 chi237QChiValue := by
  rfl'

theorem chi237RoundedFacts :
    ChiRoundedFacts 8 chi237Slice chi237LogChiCertificate
      chi237InputQChi :=
  { coversQChi := by
      rw [chi237InputQChi_eq, chi237QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi238Slice : ChiSlice :=
  { lo := (121/512), hi := (61/256) }

noncomputable def chi238LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (121/64) }, upper := { exponent := -3, mantissa := (61/32) } }

private noncomputable def chi238QChiValue : RationalEnclosure :=
  { lower := (-257225933456016285518364520101662974310989868579/925193417744100381035516223806204096374511718750), upper := (-2674338554191699658034218568037578870885482620963975100427410604825369663061/9769994499988058745200908751068384172609071287821921650475375859375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi238QChiValue_eq :
    chi238QChiValue =
      (chi238Slice.qChiAD 8 chi238LogChiCertificate).value := by
  norm_num [chi238QChiValue, chi238LogChiCertificate, chi238Slice,
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
private theorem chi238LogChi_valid :
    (if chi238Slice.lo = 0 then
      if chi238Slice.hi = 0 then true
      else decide (chi238Slice.hi ≤ 1 / 4) &&
        chi238LogChiCertificate.check
          (IntervalAD.const chi238Slice.hi).value
    else chi238LogChiCertificate.check
      chi238Slice.chiAD.value) = true := by
  norm_num [chi238Slice, chi238LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi238ValidityFacts :
    ChiFacts chi238Slice chi238LogChiCertificate :=
  { domain := by norm_num [chi238Slice]
    onePlusPositive := by
      norm_num [chi238Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi238LogChi_valid }

noncomputable def chi238InputQChi : RationalEnclosure :=
  { lower := (-1166117/4194304), upper := (-4592423/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi238InputQChi_eq :
    chi238InputQChi = outerEnclosure 24 chi238QChiValue := by
  rfl'

theorem chi238RoundedFacts :
    ChiRoundedFacts 8 chi238Slice chi238LogChiCertificate
      chi238InputQChi :=
  { coversQChi := by
      rw [chi238InputQChi_eq, chi238QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi239Slice : ChiSlice :=
  { lo := (61/256), hi := (123/512) }

noncomputable def chi239LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (61/32) }, upper := { exponent := -3, mantissa := (123/64) } }

private noncomputable def chi239QChiValue : RationalEnclosure :=
  { lower := (-1189198931721043648969380585139789091/4273636297745281976405893240146662760), upper := (-169664069761707819361565896258761107378392463735553474669033860330758494805/619236454260839881123692253078281133508338310825888972982408191389158890496) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi239QChiValue_eq :
    chi239QChiValue =
      (chi239Slice.qChiAD 8 chi239LogChiCertificate).value := by
  norm_num [chi239QChiValue, chi239LogChiCertificate, chi239Slice,
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
private theorem chi239LogChi_valid :
    (if chi239Slice.lo = 0 then
      if chi239Slice.hi = 0 then true
      else decide (chi239Slice.hi ≤ 1 / 4) &&
        chi239LogChiCertificate.check
          (IntervalAD.const chi239Slice.hi).value
    else chi239LogChiCertificate.check
      chi239Slice.chiAD.value) = true := by
  norm_num [chi239Slice, chi239LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi239ValidityFacts :
    ChiFacts chi239Slice chi239LogChiCertificate :=
  { domain := by norm_num [chi239Slice]
    onePlusPositive := by
      norm_num [chi239Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi239LogChi_valid }

noncomputable def chi239InputQChi : RationalEnclosure :=
  { lower := (-4668495/16777216), upper := (-4596775/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi239InputQChi_eq :
    chi239InputQChi = outerEnclosure 24 chi239QChiValue := by
  rfl'

theorem chi239RoundedFacts :
    ChiRoundedFacts 8 chi239Slice chi239LogChiCertificate
      chi239InputQChi :=
  { coversQChi := by
      rw [chi239InputQChi_eq, chi239QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi240Slice : ChiSlice :=
  { lo := (123/512), hi := (31/128) }

noncomputable def chi240LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (123/64) }, upper := { exponent := -3, mantissa := (31/16) } }

private noncomputable def chi240QChiValue : RationalEnclosure :=
  { lower := (-13805058741229053589952623387488377673963529073/49571041175226360978754454782637832087733658925), upper := (-13350132262377305979003283444354346712365862641781557740633949841833946136433/48681392799605177836765764209687468737997886521457059186228331717271253875200) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi240QChiValue_eq :
    chi240QChiValue =
      (chi240Slice.qChiAD 8 chi240LogChiCertificate).value := by
  norm_num [chi240QChiValue, chi240LogChiCertificate, chi240Slice,
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
private theorem chi240LogChi_valid :
    (if chi240Slice.lo = 0 then
      if chi240Slice.hi = 0 then true
      else decide (chi240Slice.hi ≤ 1 / 4) &&
        chi240LogChiCertificate.check
          (IntervalAD.const chi240Slice.hi).value
    else chi240LogChiCertificate.check
      chi240Slice.chiAD.value) = true := by
  norm_num [chi240Slice, chi240LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi240ValidityFacts :
    ChiFacts chi240Slice chi240LogChiCertificate :=
  { domain := by norm_num [chi240Slice]
    onePlusPositive := by
      norm_num [chi240Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi240LogChi_valid }

noncomputable def chi240InputQChi : RationalEnclosure :=
  { lower := (-2336147/8388608), upper := (-71889/262144) }

set_option maxRecDepth 1000000 in
private theorem chi240InputQChi_eq :
    chi240InputQChi = outerEnclosure 24 chi240QChiValue := by
  rfl'

theorem chi240RoundedFacts :
    ChiRoundedFacts 8 chi240Slice chi240LogChiCertificate
      chi240InputQChi :=
  { coversQChi := by
      rw [chi240InputQChi_eq, chi240QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi241Slice : ChiSlice :=
  { lo := (1/4), hi := (33/128) }

noncomputable def chi241LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (1) }, upper := { exponent := -2, mantissa := (33/32) } }

private noncomputable def chi241QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2089200859200), upper := (-235751515906785326658438976431039147360341/875492373598692049216054788750000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi241QChiValue_eq :
    chi241QChiValue =
      (chi241Slice.qChiAD 8 chi241LogChiCertificate).value := by
  norm_num [chi241QChiValue, chi241LogChiCertificate, chi241Slice,
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
private theorem chi241LogChi_valid :
    (if chi241Slice.lo = 0 then
      if chi241Slice.hi = 0 then true
      else decide (chi241Slice.hi ≤ 1 / 4) &&
        chi241LogChiCertificate.check
          (IntervalAD.const chi241Slice.hi).value
    else chi241LogChiCertificate.check
      chi241Slice.chiAD.value) = true := by
  norm_num [chi241Slice, chi241LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi241ValidityFacts :
    ChiFacts chi241Slice chi241LogChiCertificate :=
  { domain := by norm_num [chi241Slice]
    onePlusPositive := by
      norm_num [chi241Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi241LogChi_valid }

noncomputable def chi241InputQChi : RationalEnclosure :=
  { lower := (-1199249/4194304), upper := (-1129437/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi241InputQChi_eq :
    chi241InputQChi = outerEnclosure 24 chi241QChiValue := by
  rfl'

theorem chi241RoundedFacts :
    ChiRoundedFacts 8 chi241Slice chi241LogChiCertificate
      chi241InputQChi :=
  { coversQChi := by
      rw [chi241InputQChi_eq, chi241QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi242Slice : ChiSlice :=
  { lo := (33/128), hi := (17/64) }

noncomputable def chi242LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (33/32) }, upper := { exponent := -2, mantissa := (17/16) } }

private noncomputable def chi242QChiValue : RationalEnclosure :=
  { lower := (-1193127560676338064796733149886276366323/4167993477825804433523698335113525390625), upper := (-8858557598513568756834174270619414237657204572021109443151/32820833586178824391288987617555790373858597226562500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi242QChiValue_eq :
    chi242QChiValue =
      (chi242Slice.qChiAD 8 chi242LogChiCertificate).value := by
  norm_num [chi242QChiValue, chi242LogChiCertificate, chi242Slice,
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
private theorem chi242LogChi_valid :
    (if chi242Slice.lo = 0 then
      if chi242Slice.hi = 0 then true
      else decide (chi242Slice.hi ≤ 1 / 4) &&
        chi242LogChiCertificate.check
          (IntervalAD.const chi242Slice.hi).value
    else chi242LogChiCertificate.check
      chi242Slice.chiAD.value) = true := by
  norm_num [chi242Slice, chi242LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi242ValidityFacts :
    ChiFacts chi242Slice chi242LogChiCertificate :=
  { domain := by norm_num [chi242Slice]
    onePlusPositive := by
      norm_num [chi242Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi242LogChi_valid }

noncomputable def chi242InputQChi : RationalEnclosure :=
  { lower := (-4802637/16777216), upper := (-566035/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi242InputQChi_eq :
    chi242InputQChi = outerEnclosure 24 chi242QChiValue := by
  rfl'

theorem chi242RoundedFacts :
    ChiRoundedFacts 8 chi242Slice chi242LogChiCertificate
      chi242InputQChi :=
  { coversQChi := by
      rw [chi242InputQChi_eq, chi242QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi243Slice : ChiSlice :=
  { lo := (17/64), hi := (35/128) }

noncomputable def chi243LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (17/16) }, upper := { exponent := -2, mantissa := (35/32) } }

private noncomputable def chi243QChiValue : RationalEnclosure :=
  { lower := (-24102638627020926605400103/84154279480407050443013628), upper := (-3504518831585808433185910347064657941547241134788706363547/12963344879543410843401015569398618805187705486035296762368) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi243QChiValue_eq :
    chi243QChiValue =
      (chi243Slice.qChiAD 8 chi243LogChiCertificate).value := by
  norm_num [chi243QChiValue, chi243LogChiCertificate, chi243Slice,
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
private theorem chi243LogChi_valid :
    (if chi243Slice.lo = 0 then
      if chi243Slice.hi = 0 then true
      else decide (chi243Slice.hi ≤ 1 / 4) &&
        chi243LogChiCertificate.check
          (IntervalAD.const chi243Slice.hi).value
    else chi243LogChiCertificate.check
      chi243Slice.chiAD.value) = true := by
  norm_num [chi243Slice, chi243LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi243ValidityFacts :
    ChiFacts chi243Slice chi243LogChiCertificate :=
  { domain := by norm_num [chi243Slice]
    onePlusPositive := by
      norm_num [chi243Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi243LogChi_valid }

noncomputable def chi243InputQChi : RationalEnclosure :=
  { lower := (-4805165/16777216), upper := (-4535563/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi243InputQChi_eq :
    chi243InputQChi = outerEnclosure 24 chi243QChiValue := by
  rfl'

theorem chi243RoundedFacts :
    ChiRoundedFacts 8 chi243Slice chi243LogChiCertificate
      chi243InputQChi :=
  { coversQChi := by
      rw [chi243InputQChi_eq, chi243QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi244Slice : ChiSlice :=
  { lo := (35/128), hi := (9/32) }

noncomputable def chi244LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (35/32) }, upper := { exponent := -2, mantissa := (9/8) } }

private noncomputable def chi244QChiValue : RationalEnclosure :=
  { lower := (-2750171328931401931083549188216213314586/9603096494794585374513843698451823753605), upper := (-234208141511875394406753902199165962283200577047724236600611147/865546072838782810038182213737586989160766870276027000602392320) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi244QChiValue_eq :
    chi244QChiValue =
      (chi244Slice.qChiAD 8 chi244LogChiCertificate).value := by
  norm_num [chi244QChiValue, chi244LogChiCertificate, chi244Slice,
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
private theorem chi244LogChi_valid :
    (if chi244Slice.lo = 0 then
      if chi244Slice.hi = 0 then true
      else decide (chi244Slice.hi ≤ 1 / 4) &&
        chi244LogChiCertificate.check
          (IntervalAD.const chi244Slice.hi).value
    else chi244LogChiCertificate.check
      chi244Slice.chiAD.value) = true := by
  norm_num [chi244Slice, chi244LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi244ValidityFacts :
    ChiFacts chi244Slice chi244LogChiCertificate :=
  { domain := by norm_num [chi244Slice]
    onePlusPositive := by
      norm_num [chi244Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi244LogChi_valid }

noncomputable def chi244InputQChi : RationalEnclosure :=
  { lower := (-4804723/16777216), upper := (-4539747/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi244InputQChi_eq :
    chi244InputQChi = outerEnclosure 24 chi244QChiValue := by
  rfl'

theorem chi244RoundedFacts :
    ChiRoundedFacts 8 chi244Slice chi244LogChiCertificate
      chi244InputQChi :=
  { coversQChi := by
      rw [chi244InputQChi_eq, chi244QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi245Slice : ChiSlice :=
  { lo := (9/32), hi := (37/128) }

noncomputable def chi245LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (9/8) }, upper := { exponent := -2, mantissa := (37/32) } }

private noncomputable def chi245QChiValue : RationalEnclosure :=
  { lower := (-57890067771821225771437104497651/202279476830422128629862565114920), upper := (-760506551263971858867447801376451424899562700145098812883/2809789212832953010218408231566746095922573115822549898240) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi245QChiValue_eq :
    chi245QChiValue =
      (chi245Slice.qChiAD 8 chi245LogChiCertificate).value := by
  norm_num [chi245QChiValue, chi245LogChiCertificate, chi245Slice,
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
private theorem chi245LogChi_valid :
    (if chi245Slice.lo = 0 then
      if chi245Slice.hi = 0 then true
      else decide (chi245Slice.hi ≤ 1 / 4) &&
        chi245LogChiCertificate.check
          (IntervalAD.const chi245Slice.hi).value
    else chi245LogChiCertificate.check
      chi245Slice.chiAD.value) = true := by
  norm_num [chi245Slice, chi245LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi245ValidityFacts :
    ChiFacts chi245Slice chi245LogChiCertificate :=
  { domain := by norm_num [chi245Slice]
    onePlusPositive := by
      norm_num [chi245Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi245LogChi_valid }

noncomputable def chi245InputQChi : RationalEnclosure :=
  { lower := (-4801447/16777216), upper := (-4540975/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi245InputQChi_eq :
    chi245InputQChi = outerEnclosure 24 chi245QChiValue := by
  rfl'

theorem chi245RoundedFacts :
    ChiRoundedFacts 8 chi245Slice chi245LogChiCertificate
      chi245InputQChi :=
  { coversQChi := by
      rw [chi245InputQChi_eq, chi245QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi246Slice : ChiSlice :=
  { lo := (37/128), hi := (19/64) }

noncomputable def chi246LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (37/32) }, upper := { exponent := -2, mantissa := (19/16) } }

private noncomputable def chi246QChiValue : RationalEnclosure :=
  { lower := (-2709295672666068962716655505937507/9478631548975677280393980612608775), upper := (-122455553161081863981802470945421498525213451568521372549999/452586793425088048322848792809288361873175089757812500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi246QChiValue_eq :
    chi246QChiValue =
      (chi246Slice.qChiAD 8 chi246LogChiCertificate).value := by
  norm_num [chi246QChiValue, chi246LogChiCertificate, chi246Slice,
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
private theorem chi246LogChi_valid :
    (if chi246Slice.lo = 0 then
      if chi246Slice.hi = 0 then true
      else decide (chi246Slice.hi ≤ 1 / 4) &&
        chi246LogChiCertificate.check
          (IntervalAD.const chi246Slice.hi).value
    else chi246LogChiCertificate.check
      chi246Slice.chiAD.value) = true := by
  norm_num [chi246Slice, chi246LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi246ValidityFacts :
    ChiFacts chi246Slice chi246LogChiCertificate :=
  { domain := by norm_num [chi246Slice]
    onePlusPositive := by
      norm_num [chi246Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi246LogChi_valid }

noncomputable def chi246InputQChi : RationalEnclosure :=
  { lower := (-4795465/16777216), upper := (-4539379/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi246InputQChi_eq :
    chi246InputQChi = outerEnclosure 24 chi246QChiValue := by
  rfl'

theorem chi246RoundedFacts :
    ChiRoundedFacts 8 chi246Slice chi246LogChiCertificate
      chi246InputQChi :=
  { coversQChi := by
      rw [chi246InputQChi_eq, chi246QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi247Slice : ChiSlice :=
  { lo := (19/64), hi := (39/128) }

noncomputable def chi247LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (19/16) }, upper := { exponent := -2, mantissa := (39/32) } }

private noncomputable def chi247QChiValue : RationalEnclosure :=
  { lower := (-10831143775292511139439782773239147/37961228556051566125984497070312500), upper := (-16747540867839001056287171216595263646192367075872236901027945196277/61956272770373645704324853356376970785984769187801380703125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi247QChiValue_eq :
    chi247QChiValue =
      (chi247Slice.qChiAD 8 chi247LogChiCertificate).value := by
  norm_num [chi247QChiValue, chi247LogChiCertificate, chi247Slice,
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
private theorem chi247LogChi_valid :
    (if chi247Slice.lo = 0 then
      if chi247Slice.hi = 0 then true
      else decide (chi247Slice.hi ≤ 1 / 4) &&
        chi247LogChiCertificate.check
          (IntervalAD.const chi247Slice.hi).value
    else chi247LogChiCertificate.check
      chi247Slice.chiAD.value) = true := by
  norm_num [chi247Slice, chi247LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi247ValidityFacts :
    ChiFacts chi247Slice chi247LogChiCertificate :=
  { domain := by norm_num [chi247Slice]
    onePlusPositive := by
      norm_num [chi247Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi247LogChi_valid }

noncomputable def chi247InputQChi : RationalEnclosure :=
  { lower := (-299181/1048576), upper := (-4535087/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi247InputQChi_eq :
    chi247InputQChi = outerEnclosure 24 chi247QChiValue := by
  rfl'

theorem chi247RoundedFacts :
    ChiRoundedFacts 8 chi247Slice chi247LogChiCertificate
      chi247InputQChi :=
  { coversQChi := by
      rw [chi247InputQChi_eq, chi247QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi248Slice : ChiSlice :=
  { lo := (39/128), hi := (5/16) }

noncomputable def chi248LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (39/32) }, upper := { exponent := -2, mantissa := (5/4) } }

private noncomputable def chi248QChiValue : RationalEnclosure :=
  { lower := (-1093715634566193816184484472112367312908/3842139859524983276547921144756102699387), upper := (-67687421569316242992623499665101754936470715075999/250784437924396078629656886309816626766476753173248) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi248QChiValue_eq :
    chi248QChiValue =
      (chi248Slice.qChiAD 8 chi248LogChiCertificate).value := by
  norm_num [chi248QChiValue, chi248LogChiCertificate, chi248Slice,
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
private theorem chi248LogChi_valid :
    (if chi248Slice.lo = 0 then
      if chi248Slice.hi = 0 then true
      else decide (chi248Slice.hi ≤ 1 / 4) &&
        chi248LogChiCertificate.check
          (IntervalAD.const chi248Slice.hi).value
    else chi248LogChiCertificate.check
      chi248Slice.chiAD.value) = true := by
  norm_num [chi248Slice, chi248LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi248ValidityFacts :
    ChiFacts chi248Slice chi248LogChiCertificate :=
  { domain := by norm_num [chi248Slice]
    onePlusPositive := by
      norm_num [chi248Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi248LogChi_valid }

noncomputable def chi248InputQChi : RationalEnclosure :=
  { lower := (-298491/1048576), upper := (-4528217/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi248InputQChi_eq :
    chi248InputQChi = outerEnclosure 24 chi248QChiValue := by
  rfl'

theorem chi248RoundedFacts :
    ChiRoundedFacts 8 chi248Slice chi248LogChiCertificate
      chi248InputQChi :=
  { coversQChi := by
      rw [chi248InputQChi_eq, chi248QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi249Slice : ChiSlice :=
  { lo := (5/16), hi := (41/128) }

noncomputable def chi249LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (5/4) }, upper := { exponent := -2, mantissa := (41/32) } }

private noncomputable def chi249QChiValue : RationalEnclosure :=
  { lower := (-294857969262084122837/1038728997062787990960), upper := (-2210735985404823457332991297260902236370181118404290329/8207779643519942681612252279216968960109524312173680640) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi249QChiValue_eq :
    chi249QChiValue =
      (chi249Slice.qChiAD 8 chi249LogChiCertificate).value := by
  norm_num [chi249QChiValue, chi249LogChiCertificate, chi249Slice,
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
private theorem chi249LogChi_valid :
    (if chi249Slice.lo = 0 then
      if chi249Slice.hi = 0 then true
      else decide (chi249Slice.hi ≤ 1 / 4) &&
        chi249LogChiCertificate.check
          (IntervalAD.const chi249Slice.hi).value
    else chi249LogChiCertificate.check
      chi249Slice.chiAD.value) = true := by
  norm_num [chi249Slice, chi249LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi249ValidityFacts :
    ChiFacts chi249Slice chi249LogChiCertificate :=
  { domain := by norm_num [chi249Slice]
    onePlusPositive := by
      norm_num [chi249Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi249LogChi_valid }

noncomputable def chi249InputQChi : RationalEnclosure :=
  { lower := (-4762451/16777216), upper := (-2259441/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi249InputQChi_eq :
    chi249InputQChi = outerEnclosure 24 chi249QChiValue := by
  rfl'

theorem chi249RoundedFacts :
    ChiRoundedFacts 8 chi249Slice chi249LogChiCertificate
      chi249InputQChi :=
  { coversQChi := by
      rw [chi249InputQChi_eq, chi249QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi250Slice : ChiSlice :=
  { lo := (41/128), hi := (21/64) }

noncomputable def chi250LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (41/32) }, upper := { exponent := -2, mantissa := (21/16) } }

private noncomputable def chi250QChiValue : RationalEnclosure :=
  { lower := (-4370530504776474812545920669401142975727/15447367154292797548504425385874848564665), upper := (-42155403630941115024608298652536720216966402065723432641183857285821/156916010072669705888175799632488258654789968292991889111388180878080) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi250QChiValue_eq :
    chi250QChiValue =
      (chi250Slice.qChiAD 8 chi250LogChiCertificate).value := by
  norm_num [chi250QChiValue, chi250LogChiCertificate, chi250Slice,
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
private theorem chi250LogChi_valid :
    (if chi250Slice.lo = 0 then
      if chi250Slice.hi = 0 then true
      else decide (chi250Slice.hi ≤ 1 / 4) &&
        chi250LogChiCertificate.check
          (IntervalAD.const chi250Slice.hi).value
    else chi250LogChiCertificate.check
      chi250Slice.chiAD.value) = true := by
  norm_num [chi250Slice, chi250LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi250ValidityFacts :
    ChiFacts chi250Slice chi250LogChiCertificate :=
  { domain := by norm_num [chi250Slice]
    onePlusPositive := by
      norm_num [chi250Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi250LogChi_valid }

noncomputable def chi250InputQChi : RationalEnclosure :=
  { lower := (-2373393/8388608), upper := (-2253595/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi250InputQChi_eq :
    chi250InputQChi = outerEnclosure 24 chi250QChiValue := by
  rfl'

theorem chi250RoundedFacts :
    ChiRoundedFacts 8 chi250Slice chi250LogChiCertificate
      chi250InputQChi :=
  { coversQChi := by
      rw [chi250InputQChi_eq, chi250QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi251Slice : ChiSlice :=
  { lo := (21/64), hi := (43/128) }

noncomputable def chi251LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (21/16) }, upper := { exponent := -2, mantissa := (43/32) } }

private noncomputable def chi251QChiValue : RationalEnclosure :=
  { lower := (-6884846289318740398719465761599357321/24425807796912681604650261875288570100), upper := (-1146815086299395005435541792127591855836498158487353646780388851/4282068365352128692602953328347131155617237091064453125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi251QChiValue_eq :
    chi251QChiValue =
      (chi251Slice.qChiAD 8 chi251LogChiCertificate).value := by
  norm_num [chi251QChiValue, chi251LogChiCertificate, chi251Slice,
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
private theorem chi251LogChi_valid :
    (if chi251Slice.lo = 0 then
      if chi251Slice.hi = 0 then true
      else decide (chi251Slice.hi ≤ 1 / 4) &&
        chi251LogChiCertificate.check
          (IntervalAD.const chi251Slice.hi).value
    else chi251LogChiCertificate.check
      chi251Slice.chiAD.value) = true := by
  norm_num [chi251Slice, chi251LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi251ValidityFacts :
    ChiFacts chi251Slice chi251LogChiCertificate :=
  { domain := by norm_num [chi251Slice]
    onePlusPositive := by
      norm_num [chi251Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi251LogChi_valid }

noncomputable def chi251InputQChi : RationalEnclosure :=
  { lower := (-1182239/4194304), upper := (-561655/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi251InputQChi_eq :
    chi251InputQChi = outerEnclosure 24 chi251QChiValue := by
  rfl'

theorem chi251RoundedFacts :
    ChiRoundedFacts 8 chi251Slice chi251LogChiCertificate
      chi251InputQChi :=
  { coversQChi := by
      rw [chi251InputQChi_eq, chi251QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi252Slice : ChiSlice :=
  { lo := (43/128), hi := (11/32) }

noncomputable def chi252LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (43/32) }, upper := { exponent := -2, mantissa := (11/8) } }

private noncomputable def chi252QChiValue : RationalEnclosure :=
  { lower := (-2494332283715988326803971915842/8886701571755111217498779296875), upper := (-510048471937735772083575695670116552959789225088128329961/1911311963814728893524078854352389574050903320312500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi252QChiValue_eq :
    chi252QChiValue =
      (chi252Slice.qChiAD 8 chi252LogChiCertificate).value := by
  norm_num [chi252QChiValue, chi252LogChiCertificate, chi252Slice,
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
private theorem chi252LogChi_valid :
    (if chi252Slice.lo = 0 then
      if chi252Slice.hi = 0 then true
      else decide (chi252Slice.hi ≤ 1 / 4) &&
        chi252LogChiCertificate.check
          (IntervalAD.const chi252Slice.hi).value
    else chi252LogChiCertificate.check
      chi252Slice.chiAD.value) = true := by
  norm_num [chi252Slice, chi252LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi252ValidityFacts :
    ChiFacts chi252Slice chi252LogChiCertificate :=
  { domain := by norm_num [chi252Slice]
    onePlusPositive := by
      norm_num [chi252Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi252LogChi_valid }

noncomputable def chi252InputQChi : RationalEnclosure :=
  { lower := (-2354527/8388608), upper := (-2238565/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi252InputQChi_eq :
    chi252InputQChi = outerEnclosure 24 chi252QChiValue := by
  rfl'

theorem chi252RoundedFacts :
    ChiRoundedFacts 8 chi252Slice chi252LogChiCertificate
      chi252InputQChi :=
  { coversQChi := by
      rw [chi252InputQChi_eq, chi252QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi253Slice : ChiSlice :=
  { lo := (11/32), hi := (45/128) }

noncomputable def chi253LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (11/8) }, upper := { exponent := -2, mantissa := (45/32) } }

private noncomputable def chi253QChiValue : RationalEnclosure :=
  { lower := (-6985292909966222992985209183453/25003113965149232458553194651464), upper := (-16242629482914725683811507562887189559985903313377021072779085/61114398304308749192486890267938102513438464482204995376382976) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi253QChiValue_eq :
    chi253QChiValue =
      (chi253Slice.qChiAD 8 chi253LogChiCertificate).value := by
  norm_num [chi253QChiValue, chi253LogChiCertificate, chi253Slice,
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
private theorem chi253LogChi_valid :
    (if chi253Slice.lo = 0 then
      if chi253Slice.hi = 0 then true
      else decide (chi253Slice.hi ≤ 1 / 4) &&
        chi253LogChiCertificate.check
          (IntervalAD.const chi253Slice.hi).value
    else chi253LogChiCertificate.check
      chi253Slice.chiAD.value) = true := by
  norm_num [chi253Slice, chi253LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi253ValidityFacts :
    ChiFacts chi253Slice chi253LogChiCertificate :=
  { domain := by norm_num [chi253Slice]
    onePlusPositive := by
      norm_num [chi253Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi253LogChi_valid }

noncomputable def chi253InputQChi : RationalEnclosure :=
  { lower := (-4687167/16777216), upper := (-2229475/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi253InputQChi_eq :
    chi253InputQChi = outerEnclosure 24 chi253QChiValue := by
  rfl'

theorem chi253RoundedFacts :
    ChiRoundedFacts 8 chi253Slice chi253LogChiCertificate
      chi253InputQChi :=
  { coversQChi := by
      rw [chi253InputQChi_eq, chi253QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi254Slice : ChiSlice :=
  { lo := (45/128), hi := (23/64) }

noncomputable def chi254LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (45/32) }, upper := { exponent := -2, mantissa := (23/16) } }

private noncomputable def chi254QChiValue : RationalEnclosure :=
  { lower := (-2668340591785835092149010106752148180057/9599760825189278832526519055608350701985), upper := (-131351286780188845404972847818652319092822700272414316721341/496466320636745747317433103191094095768215698879074741948160) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi254QChiValue_eq :
    chi254QChiValue =
      (chi254Slice.qChiAD 8 chi254LogChiCertificate).value := by
  norm_num [chi254QChiValue, chi254LogChiCertificate, chi254Slice,
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
private theorem chi254LogChi_valid :
    (if chi254Slice.lo = 0 then
      if chi254Slice.hi = 0 then true
      else decide (chi254Slice.hi ≤ 1 / 4) &&
        chi254LogChiCertificate.check
          (IntervalAD.const chi254Slice.hi).value
    else chi254LogChiCertificate.check
      chi254Slice.chiAD.value) = true := by
  norm_num [chi254Slice, chi254LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi254ValidityFacts :
    ChiFacts chi254Slice chi254LogChiCertificate :=
  { domain := by norm_num [chi254Slice]
    onePlusPositive := by
      norm_num [chi254Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi254LogChi_valid }

noncomputable def chi254InputQChi : RationalEnclosure :=
  { lower := (-1165845/4194304), upper := (-1109697/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi254InputQChi_eq :
    chi254InputQChi = outerEnclosure 24 chi254QChiValue := by
  rfl'

theorem chi254RoundedFacts :
    ChiRoundedFacts 8 chi254Slice chi254LogChiCertificate
      chi254InputQChi :=
  { coversQChi := by
      rw [chi254InputQChi_eq, chi254QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi255Slice : ChiSlice :=
  { lo := (23/64), hi := (47/128) }

noncomputable def chi255LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -2, mantissa := (23/16) }, upper := { exponent := -2, mantissa := (47/32) } }

private noncomputable def chi255QChiValue : RationalEnclosure :=
  { lower := (-81605540480437200032594690113/295209502968483192346839642060), upper := (-95350519183174302999761270263870590755651422129003560310534853/362195099928343199463740569595018492360238768631963211797793280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi255QChiValue_eq :
    chi255QChiValue =
      (chi255Slice.qChiAD 8 chi255LogChiCertificate).value := by
  norm_num [chi255QChiValue, chi255LogChiCertificate, chi255Slice,
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
private theorem chi255LogChi_valid :
    (if chi255Slice.lo = 0 then
      if chi255Slice.hi = 0 then true
      else decide (chi255Slice.hi ≤ 1 / 4) &&
        chi255LogChiCertificate.check
          (IntervalAD.const chi255Slice.hi).value
    else chi255LogChiCertificate.check
      chi255Slice.chiAD.value) = true := by
  norm_num [chi255Slice, chi255LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi255ValidityFacts :
    ChiFacts chi255Slice chi255LogChiCertificate :=
  { domain := by norm_num [chi255Slice]
    onePlusPositive := by
      norm_num [chi255Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi255LogChi_valid }

noncomputable def chi255InputQChi : RationalEnclosure :=
  { lower := (-4637771/16777216), upper := (-4416725/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi255InputQChi_eq :
    chi255InputQChi = outerEnclosure 24 chi255QChiValue := by
  rfl'

theorem chi255RoundedFacts :
    ChiRoundedFacts 8 chi255Slice chi255LogChiCertificate
      chi255InputQChi :=
  { coversQChi := by
      rw [chi255InputQChi_eq, chi255QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
