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

noncomputable def sk128Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2) }

noncomputable def sk128LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (1146825/1048576) }, upper := { exponent := 2, mantissa := (9/8) } }

noncomputable def sk128LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (27/16) }, upper := { exponent := 1, mantissa := (7/4) } }

noncomputable def sk128LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (6877303/5505024) }, upper := { exponent := 0, mantissa := (4/3) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk128LogOuter_valid :
    sk128LogOuterCertificate.check sk128Slice.outerAD.value = true := by
  norm_num [sk128LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk128Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk128LogK_valid :
    sk128LogKCertificate.check sk128Slice.kAD.value = true := by
  norm_num [sk128LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk128Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk128LogDArg_valid :
    sk128LogDArgCertificate.check sk128Slice.dArgAD.value = true := by
  norm_num [sk128LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk128Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk128ValidityFacts : SKFacts sk128Slice
    sk128LogOuterCertificate sk128LogKCertificate
    sk128LogDArgCertificate :=
  { domain := by norm_num [sk128Slice]
    kPositive := by
      norm_num [sk128Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk128LogOuter_valid
    logK := sk128LogK_valid
    logDArg := sk128LogDArg_valid }

noncomputable def sk128RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24760797/16777216), upper := (3154279/2097152) }
    logK := { lower := (20407727/16777216), upper := (5254469/4194304) }
    logDArg := { lower := (933507/4194304), upper := (4826505/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk128LogOuterInput_eq :
    sk128RoundedInputs.logOuter = outerEnclosure 24
      (sk128LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk128LogKInput_eq :
    sk128RoundedInputs.logK = outerEnclosure 24
      (sk128LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk128LogDArgInput_eq :
    sk128RoundedInputs.logDArg = outerEnclosure 24
      (sk128LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk128RoundedFacts : SKRoundedFacts 8
    sk128LogOuterCertificate sk128LogKCertificate
    sk128LogDArgCertificate sk128RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk128LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk128LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk128LogDArgInput_eq }

noncomputable def sk129Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16) }

noncomputable def sk129LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2293651/2097152) }, upper := { exponent := 2, mantissa := (71/64) } }

noncomputable def sk129LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (27/16) }, upper := { exponent := 1, mantissa := (55/32) } }

noncomputable def sk129LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (27520159/21626880) }, upper := { exponent := 0, mantissa := (71/54) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk129LogOuter_valid :
    sk129LogOuterCertificate.check sk129Slice.outerAD.value = true := by
  norm_num [sk129LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk129Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk129LogK_valid :
    sk129LogKCertificate.check sk129Slice.kAD.value = true := by
  norm_num [sk129LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk129Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk129LogDArg_valid :
    sk129LogDArgCertificate.check sk129Slice.dArgAD.value = true := by
  norm_num [sk129LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk129Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk129ValidityFacts : SKFacts sk129Slice
    sk129LogOuterCertificate sk129LogKCertificate
    sk129LogDArgCertificate :=
  { domain := by norm_num [sk129Slice]
    kPositive := by
      norm_num [sk129Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk129LogOuter_valid
    logK := sk129LogK_valid
    logDArg := sk129LogDArg_valid }

noncomputable def sk129RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24760805/16777216), upper := (12499791/8388608) }
    logK := { lower := (20407727/16777216), upper := (20715575/16777216) }
    logDArg := { lower := (4043003/16777216), upper := (4591855/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk129LogOuterInput_eq :
    sk129RoundedInputs.logOuter = outerEnclosure 24
      (sk129LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk129LogKInput_eq :
    sk129RoundedInputs.logK = outerEnclosure 24
      (sk129LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk129LogDArgInput_eq :
    sk129RoundedInputs.logDArg = outerEnclosure 24
      (sk129LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk129RoundedFacts : SKRoundedFacts 8
    sk129LogOuterCertificate sk129LogKCertificate
    sk129LogDArgCertificate sk129RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk129LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk129LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk129LogDArgInput_eq }

noncomputable def sk130Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2) }

noncomputable def sk130LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2326417/2097152) }, upper := { exponent := 2, mantissa := (9/8) } }

noncomputable def sk130LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (55/32) }, upper := { exponent := 1, mantissa := (7/4) } }

noncomputable def sk130LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (23261181/18350080) }, upper := { exponent := 0, mantissa := (72/55) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk130LogOuter_valid :
    sk130LogOuterCertificate.check sk130Slice.outerAD.value = true := by
  norm_num [sk130LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk130Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk130LogK_valid :
    sk130LogKCertificate.check sk130Slice.kAD.value = true := by
  norm_num [sk130LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk130Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk130LogDArg_valid :
    sk130LogDArgCertificate.check sk130Slice.dArgAD.value = true := by
  norm_num [sk130LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk130Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk130ValidityFacts : SKFacts sk130Slice
    sk130LogOuterCertificate sk130LogKCertificate
    sk130LogDArgCertificate :=
  { domain := by norm_num [sk130Slice]
    kPositive := by
      norm_num [sk130Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk130LogOuter_valid
    logK := sk130LogK_valid
    logDArg := sk130LogDArg_valid }

noncomputable def sk130RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6249695/4194304), upper := (3154279/2097152) }
    logK := { lower := (10357787/8388608), upper := (5254469/4194304) }
    logDArg := { lower := (1989375/8388608), upper := (4518657/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk130LogOuterInput_eq :
    sk130RoundedInputs.logOuter = outerEnclosure 24
      (sk130LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk130LogKInput_eq :
    sk130RoundedInputs.logK = outerEnclosure 24
      (sk130LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk130LogDArgInput_eq :
    sk130RoundedInputs.logDArg = outerEnclosure 24
      (sk130LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk130RoundedFacts : SKRoundedFacts 8
    sk130LogOuterCertificate sk130LogKCertificate
    sk130LogDArgCertificate sk130RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk130LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk130LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk130LogDArgInput_eq }

noncomputable def sk131Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16) }

noncomputable def sk131LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2228119/2097152) }, upper := { exponent := 2, mantissa := (69/64) } }

noncomputable def sk131LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (13/8) }, upper := { exponent := 1, mantissa := (53/32) } }

noncomputable def sk131LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (231691503/180617216) }, upper := { exponent := 0, mantissa := (69/52) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk131LogOuter_valid :
    sk131LogOuterCertificate.check sk131Slice.outerAD.value = true := by
  norm_num [sk131LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk131Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk131LogK_valid :
    sk131LogKCertificate.check sk131Slice.kAD.value = true := by
  norm_num [sk131LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk131Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk131LogDArg_valid :
    sk131LogDArgCertificate.check sk131Slice.dArgAD.value = true := by
  norm_num [sk131LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk131Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk131ValidityFacts : SKFacts sk131Slice
    sk131LogOuterCertificate sk131LogKCertificate
    sk131LogDArgCertificate :=
  { domain := by norm_num [sk131Slice]
    kPositive := by
      norm_num [sk131Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk131LogOuter_valid
    logK := sk131LogK_valid
    logDArg := sk131LogDArg_valid }

noncomputable def sk131RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24274481/16777216), upper := (24520201/16777216) }
    logK := { lower := (19774549/16777216), upper := (10047063/8388608) }
    logDArg := { lower := (522247/2097152), upper := (4745651/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk131LogOuterInput_eq :
    sk131RoundedInputs.logOuter = outerEnclosure 24
      (sk131LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk131LogKInput_eq :
    sk131RoundedInputs.logK = outerEnclosure 24
      (sk131LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk131LogDArgInput_eq :
    sk131RoundedInputs.logDArg = outerEnclosure 24
      (sk131LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk131RoundedFacts : SKRoundedFacts 8
    sk131LogOuterCertificate sk131LogKCertificate
    sk131LogDArgCertificate sk131RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk131LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk131LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk131LogDArgInput_eq }

noncomputable def sk132Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8) }

noncomputable def sk132LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2260885/2097152) }, upper := { exponent := 2, mantissa := (35/32) } }

noncomputable def sk132LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (53/32) }, upper := { exponent := 1, mantissa := (27/16) } }

noncomputable def sk132LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (79873645/62521344) }, upper := { exponent := 0, mantissa := (70/53) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk132LogOuter_valid :
    sk132LogOuterCertificate.check sk132Slice.outerAD.value = true := by
  norm_num [sk132LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk132Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk132LogK_valid :
    sk132LogKCertificate.check sk132Slice.kAD.value = true := by
  norm_num [sk132LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk132Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk132LogDArg_valid :
    sk132LogDArgCertificate.check sk132Slice.dArgAD.value = true := by
  norm_num [sk132LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk132Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk132ValidityFacts : SKFacts sk132Slice
    sk132LogOuterCertificate sk132LogKCertificate
    sk132LogDArgCertificate :=
  { domain := by norm_num [sk132Slice]
    kPositive := by
      norm_num [sk132Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk132LogOuter_valid
    logK := sk132LogK_valid
    logDArg := sk132LogDArg_valid }

noncomputable def sk132RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24519405/16777216), upper := (6190401/4194304) }
    logK := { lower := (20094125/16777216), upper := (1275483/1048576) }
    logDArg := { lower := (64209/262144), upper := (2333739/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk132LogOuterInput_eq :
    sk132RoundedInputs.logOuter = outerEnclosure 24
      (sk132LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk132LogKInput_eq :
    sk132RoundedInputs.logK = outerEnclosure 24
      (sk132LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk132LogDArgInput_eq :
    sk132RoundedInputs.logDArg = outerEnclosure 24
      (sk132LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk132RoundedFacts : SKRoundedFacts 8
    sk132LogOuterCertificate sk132LogKCertificate
    sk132LogDArgCertificate sk132RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk132LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk132LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk132LogDArgInput_eq }

noncomputable def sk133Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (97/32) }

noncomputable def sk133LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4194111/2097152) }, upper := { exponent := 2, mantissa := (129/128) } }

noncomputable def sk133LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3/2) }, upper := { exponent := 1, mantissa := (97/64) } }

noncomputable def sk133LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (268412117/203423744) }, upper := { exponent := 0, mantissa := (43/32) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk133LogOuter_valid :
    sk133LogOuterCertificate.check sk133Slice.outerAD.value = true := by
  norm_num [sk133LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk133Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk133LogK_valid :
    sk133LogKCertificate.check sk133Slice.kAD.value = true := by
  norm_num [sk133LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk133Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk133LogDArg_valid :
    sk133LogDArgCertificate.check sk133Slice.dArgAD.value = true := by
  norm_num [sk133LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk133Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk133ValidityFacts : SKFacts sk133Slice
    sk133LogOuterCertificate sk133LogKCertificate
    sk133LogDArgCertificate :=
  { domain := by norm_num [sk133Slice]
    kPositive := by
      norm_num [sk133Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk133LogOuter_valid
    logK := sk133LogK_valid
    logDArg := sk133LogDArg_valid }

noncomputable def sk133RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23257387/16777216), upper := (5847181/4194304) }
    logK := { lower := (18431655/16777216), upper := (18605515/16777216) }
    logDArg := { lower := (2325593/8388608), upper := (4957067/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk133LogOuterInput_eq :
    sk133RoundedInputs.logOuter = outerEnclosure 24
      (sk133LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk133LogKInput_eq :
    sk133RoundedInputs.logK = outerEnclosure 24
      (sk133LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk133LogDArgInput_eq :
    sk133RoundedInputs.logDArg = outerEnclosure 24
      (sk133LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk133RoundedFacts : SKRoundedFacts 8
    sk133LogOuterCertificate sk133LogKCertificate
    sk133LogDArgCertificate sk133RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk133LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk133LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk133LogDArgInput_eq }

noncomputable def sk134Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (49/16) }

noncomputable def sk134LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4226877/4194304) }, upper := { exponent := 2, mantissa := (65/64) } }

noncomputable def sk134LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (97/64) }, upper := { exponent := 1, mantissa := (49/32) } }

noncomputable def sk134LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (819981175/622985216) }, upper := { exponent := 0, mantissa := (130/97) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk134LogOuter_valid :
    sk134LogOuterCertificate.check sk134Slice.outerAD.value = true := by
  norm_num [sk134LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk134Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk134LogK_valid :
    sk134LogKCertificate.check sk134Slice.kAD.value = true := by
  norm_num [sk134LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk134Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk134LogDArg_valid :
    sk134LogDArgCertificate.check sk134Slice.dArgAD.value = true := by
  norm_num [sk134LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk134Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk134ValidityFacts : SKFacts sk134Slice
    sk134LogOuterCertificate sk134LogKCertificate
    sk134LogDArgCertificate :=
  { domain := by norm_num [sk134Slice]
    kPositive := by
      norm_num [sk134Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk134LogOuter_valid
    logK := sk134LogK_valid
    logDArg := sk134LogDArg_valid }

noncomputable def sk134RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5846987/4194304), upper := (11759139/8388608) }
    logK := { lower := (9302757/8388608), upper := (18777591/16777216) }
    logDArg := { lower := (1152421/4194304), upper := (4912763/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk134LogOuterInput_eq :
    sk134RoundedInputs.logOuter = outerEnclosure 24
      (sk134LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk134LogKInput_eq :
    sk134RoundedInputs.logK = outerEnclosure 24
      (sk134LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk134LogDArgInput_eq :
    sk134RoundedInputs.logDArg = outerEnclosure 24
      (sk134LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk134RoundedFacts : SKRoundedFacts 8
    sk134LogOuterCertificate sk134LogKCertificate
    sk134LogDArgCertificate sk134RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk134LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk134LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk134LogDArgInput_eq }

noncomputable def sk135Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32) }

noncomputable def sk135LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4259643/4194304) }, upper := { exponent := 2, mantissa := (131/128) } }

noncomputable def sk135LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (49/32) }, upper := { exponent := 1, mantissa := (99/64) } }

noncomputable def sk135LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (834857063/635830272) }, upper := { exponent := 0, mantissa := (131/98) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk135LogOuter_valid :
    sk135LogOuterCertificate.check sk135Slice.outerAD.value = true := by
  norm_num [sk135LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk135Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk135LogK_valid :
    sk135LogKCertificate.check sk135Slice.kAD.value = true := by
  norm_num [sk135LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk135Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk135LogDArg_valid :
    sk135LogDArgCertificate.check sk135Slice.dArgAD.value = true := by
  norm_num [sk135LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk135Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk135ValidityFacts : SKFacts sk135Slice
    sk135LogOuterCertificate sk135LogKCertificate
    sk135LogDArgCertificate :=
  { domain := by norm_num [sk135Slice]
    kPositive := by
      norm_num [sk135Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk135LogOuter_valid
    logK := sk135LogK_valid
    logDArg := sk135LogDArg_valid }

noncomputable def sk135RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23517501/16777216), upper := (2955855/2097152) }
    logK := { lower := (18777589/16777216), upper := (18947919/16777216) }
    logDArg := { lower := (571115/2097152), upper := (4869249/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk135LogOuterInput_eq :
    sk135RoundedInputs.logOuter = outerEnclosure 24
      (sk135LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk135LogKInput_eq :
    sk135RoundedInputs.logK = outerEnclosure 24
      (sk135LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk135LogDArgInput_eq :
    sk135RoundedInputs.logDArg = outerEnclosure 24
      (sk135LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk135RoundedFacts : SKRoundedFacts 8
    sk135LogOuterCertificate sk135LogKCertificate
    sk135LogDArgCertificate sk135RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk135LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk135LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk135LogDArgInput_eq }

noncomputable def sk136Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8) }

noncomputable def sk136LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4292409/4194304) }, upper := { exponent := 2, mantissa := (33/32) } }

noncomputable def sk136LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (99/64) }, upper := { exponent := 1, mantissa := (25/16) } }

noncomputable def sk136LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1716897/1310720) }, upper := { exponent := 0, mantissa := (4/3) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk136LogOuter_valid :
    sk136LogOuterCertificate.check sk136Slice.outerAD.value = true := by
  norm_num [sk136LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk136Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk136LogK_valid :
    sk136LogKCertificate.check sk136Slice.kAD.value = true := by
  norm_num [sk136LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk136Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk136LogDArg_valid :
    sk136LogDArgCertificate.check sk136Slice.dArgAD.value = true := by
  norm_num [sk136LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk136Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk136ValidityFacts : SKFacts sk136Slice
    sk136LogOuterCertificate sk136LogKCertificate
    sk136LogDArgCertificate :=
  { domain := by norm_num [sk136Slice]
    kPositive := by
      norm_num [sk136Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk136LogOuter_valid
    logK := sk136LogK_valid
    logDArg := sk136LogDArg_valid }

noncomputable def sk136RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5911515/4194304), upper := (2971803/2097152) }
    logK := { lower := (9473959/8388608), upper := (2389567/2097152) }
    logDArg := { lower := (4528875/16777216), upper := (4826505/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk136LogOuterInput_eq :
    sk136RoundedInputs.logOuter = outerEnclosure 24
      (sk136LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk136LogKInput_eq :
    sk136RoundedInputs.logK = outerEnclosure 24
      (sk136LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk136LogDArgInput_eq :
    sk136RoundedInputs.logDArg = outerEnclosure 24
      (sk136LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk136RoundedFacts : SKRoundedFacts 8
    sk136LogOuterCertificate sk136LogKCertificate
    sk136LogDArgCertificate sk136RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk136LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk136LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk136LogDArgInput_eq }

noncomputable def sk137Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32) }

noncomputable def sk137LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4325175/4194304) }, upper := { exponent := 2, mantissa := (133/128) } }

noncomputable def sk137LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (25/16) }, upper := { exponent := 1, mantissa := (101/64) } }

noncomputable def sk137LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (865002031/661913600) }, upper := { exponent := 0, mantissa := (133/100) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk137LogOuter_valid :
    sk137LogOuterCertificate.check sk137Slice.outerAD.value = true := by
  norm_num [sk137LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk137Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk137LogK_valid :
    sk137LogKCertificate.check sk137Slice.kAD.value = true := by
  norm_num [sk137LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk137Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk137LogDArg_valid :
    sk137LogDArgCertificate.check sk137Slice.dArgAD.value = true := by
  norm_num [sk137LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk137Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk137ValidityFacts : SKFacts sk137Slice
    sk137LogOuterCertificate sk137LogKCertificate
    sk137LogDArgCertificate :=
  { domain := by norm_num [sk137Slice]
    kPositive := by
      norm_num [sk137Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk137LogOuter_valid
    logK := sk137LogK_valid
    logDArg := sk137LogDArg_valid }

noncomputable def sk137RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23773643/16777216), upper := (23901045/16777216) }
    logK := { lower := (19116535/16777216), upper := (19283475/16777216) }
    logDArg := { lower := (4489529/16777216), upper := (4784509/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk137LogOuterInput_eq :
    sk137RoundedInputs.logOuter = outerEnclosure 24
      (sk137LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk137LogKInput_eq :
    sk137RoundedInputs.logK = outerEnclosure 24
      (sk137LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk137LogDArgInput_eq :
    sk137RoundedInputs.logDArg = outerEnclosure 24
      (sk137LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk137RoundedFacts : SKRoundedFacts 8
    sk137LogOuterCertificate sk137LogKCertificate
    sk137LogDArgCertificate sk137RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk137LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk137LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk137LogDArgInput_eq }

noncomputable def sk138Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16) }

noncomputable def sk138LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4357941/4194304) }, upper := { exponent := 2, mantissa := (67/64) } }

noncomputable def sk138LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (101/64) }, upper := { exponent := 1, mantissa := (51/32) } }

noncomputable def sk138LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (880271111/675151872) }, upper := { exponent := 0, mantissa := (134/101) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk138LogOuter_valid :
    sk138LogOuterCertificate.check sk138Slice.outerAD.value = true := by
  norm_num [sk138LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk138Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk138LogK_valid :
    sk138LogKCertificate.check sk138Slice.kAD.value = true := by
  norm_num [sk138LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk138Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk138LogDArg_valid :
    sk138LogDArgCertificate.check sk138Slice.dArgAD.value = true := by
  norm_num [sk138LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk138Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk138ValidityFacts : SKFacts sk138Slice
    sk138LogOuterCertificate sk138LogKCertificate
    sk138LogDArgCertificate :=
  { domain := by norm_num [sk138Slice]
    kPositive := by
      norm_num [sk138Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk138LogOuter_valid
    logK := sk138LogK_valid
    logDArg := sk138LogDArg_valid }

noncomputable def sk138RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11950131/8388608), upper := (24026717/16777216) }
    logK := { lower := (19283473/16777216), upper := (19448769/16777216) }
    logDArg := { lower := (4450865/16777216), upper := (4743243/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk138LogOuterInput_eq :
    sk138RoundedInputs.logOuter = outerEnclosure 24
      (sk138LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk138LogKInput_eq :
    sk138RoundedInputs.logK = outerEnclosure 24
      (sk138LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk138LogDArgInput_eq :
    sk138RoundedInputs.logDArg = outerEnclosure 24
      (sk138LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk138RoundedFacts : SKRoundedFacts 8
    sk138LogOuterCertificate sk138LogKCertificate
    sk138LogDArgCertificate sk138RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk138LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk138LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk138LogDArgInput_eq }

noncomputable def sk139Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32) }

noncomputable def sk139LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4390707/4194304) }, upper := { exponent := 2, mantissa := (135/128) } }

noncomputable def sk139LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (51/32) }, upper := { exponent := 1, mantissa := (103/64) } }

noncomputable def sk139LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (298557085/229507072) }, upper := { exponent := 0, mantissa := (45/34) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk139LogOuter_valid :
    sk139LogOuterCertificate.check sk139Slice.outerAD.value = true := by
  norm_num [sk139LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk139Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk139LogK_valid :
    sk139LogKCertificate.check sk139Slice.kAD.value = true := by
  norm_num [sk139LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk139Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk139LogDArg_valid :
    sk139LogDArgCertificate.check sk139Slice.dArgAD.value = true := by
  norm_num [sk139LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk139Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk139ValidityFacts : SKFacts sk139Slice
    sk139LogOuterCertificate sk139LogKCertificate
    sk139LogDArgCertificate :=
  { domain := by norm_num [sk139Slice]
    kPositive := by
      norm_num [sk139Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk139LogOuter_valid
    logK := sk139LogK_valid
    logDArg := sk139LogDArg_valid }

noncomputable def sk139RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24025933/16777216), upper := (754733/524288) }
    logK := { lower := (303887/262144), upper := (9806225/8388608) }
    logDArg := { lower := (4412865/16777216), upper := (4702687/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk139LogOuterInput_eq :
    sk139RoundedInputs.logOuter = outerEnclosure 24
      (sk139LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk139LogKInput_eq :
    sk139RoundedInputs.logK = outerEnclosure 24
      (sk139LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk139LogDArgInput_eq :
    sk139RoundedInputs.logDArg = outerEnclosure 24
      (sk139LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk139RoundedFacts : SKRoundedFacts 8
    sk139LogOuterCertificate sk139LogKCertificate
    sk139LogDArgCertificate sk139RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk139LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk139LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk139LogDArgInput_eq }

noncomputable def sk140Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4) }

noncomputable def sk140LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4423473/4194304) }, upper := { exponent := 2, mantissa := (17/16) } }

noncomputable def sk140LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (103/64) }, upper := { exponent := 1, mantissa := (13/8) } }

noncomputable def sk140LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (911202463/702021632) }, upper := { exponent := 0, mantissa := (136/103) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk140LogOuter_valid :
    sk140LogOuterCertificate.check sk140Slice.outerAD.value = true := by
  norm_num [sk140LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk140Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk140LogK_valid :
    sk140LogKCertificate.check sk140Slice.kAD.value = true := by
  norm_num [sk140LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk140Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk140LogDArg_valid :
    sk140LogDArgCertificate.check sk140Slice.dArgAD.value = true := by
  norm_num [sk140LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk140Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk140ValidityFacts : SKFacts sk140Slice
    sk140LogOuterCertificate sk140LogKCertificate
    sk140LogDArgCertificate :=
  { domain := by norm_num [sk140Slice]
    kPositive := by
      norm_num [sk140Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk140LogOuter_valid
    logK := sk140LogK_valid
    logDArg := sk140LogDArg_valid }

noncomputable def sk140RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24150669/16777216), upper := (24275273/16777216) }
    logK := { lower := (19612449/16777216), upper := (9887275/8388608) }
    logDArg := { lower := (546939/2097152), upper := (4662823/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk140LogOuterInput_eq :
    sk140RoundedInputs.logOuter = outerEnclosure 24
      (sk140LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk140LogKInput_eq :
    sk140RoundedInputs.logK = outerEnclosure 24
      (sk140LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk140LogDArgInput_eq :
    sk140RoundedInputs.logDArg = outerEnclosure 24
      (sk140LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk140RoundedFacts : SKRoundedFacts 8
    sk140LogOuterCertificate sk140LogKCertificate
    sk140LogDArgCertificate sk140RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk140LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk140LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk140LogDArgInput_eq }

noncomputable def sk141Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32) }

noncomputable def sk141LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4456239/4194304) }, upper := { exponent := 2, mantissa := (137/128) } }

noncomputable def sk141LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (13/8) }, upper := { exponent := 1, mantissa := (105/64) } }

noncomputable def sk141LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (185372947/143130624) }, upper := { exponent := 0, mantissa := (137/104) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk141LogOuter_valid :
    sk141LogOuterCertificate.check sk141Slice.outerAD.value = true := by
  norm_num [sk141LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk141Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk141LogK_valid :
    sk141LogKCertificate.check sk141Slice.kAD.value = true := by
  norm_num [sk141LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk141Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk141LogDArg_valid :
    sk141LogDArgCertificate.check sk141Slice.dArgAD.value = true := by
  norm_num [sk141LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk141Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk141ValidityFacts : SKFacts sk141Slice
    sk141LogOuterCertificate sk141LogKCertificate
    sk141LogDArgCertificate :=
  { domain := by norm_num [sk141Slice]
    kPositive := by
      norm_num [sk141Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk141LogOuter_valid
    logK := sk141LogK_valid
    logDArg := sk141LogDArg_valid }

noncomputable def sk141RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24274485/16777216), upper := (3049773/2097152) }
    logK := { lower := (19774549/16777216), upper := (19935099/16777216) }
    logDArg := { lower := (2169395/8388608), upper := (2311817/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk141LogOuterInput_eq :
    sk141RoundedInputs.logOuter = outerEnclosure 24
      (sk141LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk141LogKInput_eq :
    sk141RoundedInputs.logK = outerEnclosure 24
      (sk141LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk141LogDArgInput_eq :
    sk141RoundedInputs.logDArg = outerEnclosure 24
      (sk141LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk141RoundedFacts : SKRoundedFacts 8
    sk141LogOuterCertificate sk141LogKCertificate
    sk141LogDArgCertificate sk141RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk141LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk141LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk141LogDArgInput_eq }

noncomputable def sk142Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16) }

noncomputable def sk142LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4489005/4194304) }, upper := { exponent := 2, mantissa := (69/64) } }

noncomputable def sk142LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (105/64) }, upper := { exponent := 1, mantissa := (53/32) } }

noncomputable def sk142LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (314219357/243138560) }, upper := { exponent := 0, mantissa := (46/35) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk142LogOuter_valid :
    sk142LogOuterCertificate.check sk142Slice.outerAD.value = true := by
  norm_num [sk142LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk142Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk142LogK_valid :
    sk142LogKCertificate.check sk142Slice.kAD.value = true := by
  norm_num [sk142LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk142Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk142LogDArg_valid :
    sk142LogDArgCertificate.check sk142Slice.dArgAD.value = true := by
  norm_num [sk142LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk142Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk142ValidityFacts : SKFacts sk142Slice
    sk142LogOuterCertificate sk142LogKCertificate
    sk142LogDArgCertificate :=
  { domain := by norm_num [sk142Slice]
    kPositive := by
      norm_num [sk142Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk142LogOuter_valid
    logK := sk142LogK_valid
    logDArg := sk142LogDArg_valid }

noncomputable def sk142RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12198697/8388608), upper := (24520201/16777216) }
    logK := { lower := (9967549/8388608), upper := (10047063/8388608) }
    logDArg := { lower := (2151341/8388608), upper := (2292551/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk142LogOuterInput_eq :
    sk142RoundedInputs.logOuter = outerEnclosure 24
      (sk142LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk142LogKInput_eq :
    sk142RoundedInputs.logK = outerEnclosure 24
      (sk142LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk142LogDArgInput_eq :
    sk142RoundedInputs.logDArg = outerEnclosure 24
      (sk142LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk142RoundedFacts : SKRoundedFacts 8
    sk142LogOuterCertificate sk142LogKCertificate
    sk142LogDArgCertificate sk142RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk142LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk142LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk142LogDArgInput_eq }

noncomputable def sk143Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32) }

noncomputable def sk143LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4521771/4194304) }, upper := { exponent := 2, mantissa := (139/128) } }

noncomputable def sk143LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (53/32) }, upper := { exponent := 1, mantissa := (107/64) } }

noncomputable def sk143LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (958582471/743309312) }, upper := { exponent := 0, mantissa := (139/106) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk143LogOuter_valid :
    sk143LogOuterCertificate.check sk143Slice.outerAD.value = true := by
  norm_num [sk143LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk143Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk143LogK_valid :
    sk143LogKCertificate.check sk143Slice.kAD.value = true := by
  norm_num [sk143LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk143Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk143LogDArg_valid :
    sk143LogDArgCertificate.check sk143Slice.dArgAD.value = true := by
  norm_num [sk143LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk143Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk143ValidityFacts : SKFacts sk143Slice
    sk143LogOuterCertificate sk143LogKCertificate
    sk143LogDArgCertificate :=
  { domain := by norm_num [sk143Slice]
    kPositive := by
      norm_num [sk143Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk143LogOuter_valid
    logK := sk143LogK_valid
    logDArg := sk143LogDArg_valid }

noncomputable def sk143RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24519409/16777216), upper := (3080167/2097152) }
    logK := { lower := (20094125/16777216), upper := (5062915/4194304) }
    logDArg := { lower := (4267173/16777216), upper := (4547211/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk143LogOuterInput_eq :
    sk143RoundedInputs.logOuter = outerEnclosure 24
      (sk143LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk143LogKInput_eq :
    sk143RoundedInputs.logK = outerEnclosure 24
      (sk143LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk143LogDArgInput_eq :
    sk143RoundedInputs.logDArg = outerEnclosure 24
      (sk143LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk143RoundedFacts : SKRoundedFacts 8
    sk143LogOuterCertificate sk143LogKCertificate
    sk143LogDArgCertificate sk143RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk143LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk143LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk143LogDArgInput_eq }

noncomputable def sk144Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8) }

noncomputable def sk144LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4554537/4194304) }, upper := { exponent := 2, mantissa := (35/32) } }

noncomputable def sk144LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (107/64) }, upper := { exponent := 1, mantissa := (27/16) } }

noncomputable def sk144LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (974637935/757334016) }, upper := { exponent := 0, mantissa := (140/107) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk144LogOuter_valid :
    sk144LogOuterCertificate.check sk144Slice.outerAD.value = true := by
  norm_num [sk144LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk144Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk144LogK_valid :
    sk144LogKCertificate.check sk144Slice.kAD.value = true := by
  norm_num [sk144LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk144Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk144LogDArg_valid :
    sk144LogDArgCertificate.check sk144Slice.dArgAD.value = true := by
  norm_num [sk144LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk144Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk144ValidityFacts : SKFacts sk144Slice
    sk144LogOuterCertificate sk144LogKCertificate
    sk144LogDArgCertificate :=
  { domain := by norm_num [sk144Slice]
    kPositive := by
      norm_num [sk144Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk144LogOuter_valid
    logK := sk144LogK_valid
    logDArg := sk144LogDArg_valid }

noncomputable def sk144RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24640543/16777216), upper := (6190401/4194304) }
    logK := { lower := (10125829/8388608), upper := (1275483/1048576) }
    logDArg := { lower := (529031/2097152), upper := (563743/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk144LogOuterInput_eq :
    sk144RoundedInputs.logOuter = outerEnclosure 24
      (sk144LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk144LogKInput_eq :
    sk144RoundedInputs.logK = outerEnclosure 24
      (sk144LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk144LogDArgInput_eq :
    sk144RoundedInputs.logDArg = outerEnclosure 24
      (sk144LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk144RoundedFacts : SKRoundedFacts 8
    sk144LogOuterCertificate sk144LogKCertificate
    sk144LogDArgCertificate sk144RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk144LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk144LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk144LogDArgInput_eq }

noncomputable def sk145Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32) }

noncomputable def sk145LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4587303/4194304) }, upper := { exponent := 2, mantissa := (141/128) } }

noncomputable def sk145LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (27/16) }, upper := { exponent := 1, mantissa := (109/64) } }

noncomputable def sk145LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (110091607/85721088) }, upper := { exponent := 0, mantissa := (47/36) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk145LogOuter_valid :
    sk145LogOuterCertificate.check sk145Slice.outerAD.value = true := by
  norm_num [sk145LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk145Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk145LogK_valid :
    sk145LogKCertificate.check sk145Slice.kAD.value = true := by
  norm_num [sk145LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk145Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk145LogDArg_valid :
    sk145LogDArgCertificate.check sk145Slice.dArgAD.value = true := by
  norm_num [sk145LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk145Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk145ValidityFacts : SKFacts sk145Slice
    sk145LogOuterCertificate sk145LogKCertificate
    sk145LogDArgCertificate :=
  { domain := by norm_num [sk145Slice]
    kPositive := by
      norm_num [sk145Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk145LogOuter_valid
    logK := sk145LogK_valid
    logDArg := sk145LogDArg_valid }

noncomputable def sk145RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3095101/2097152), upper := (24881015/16777216) }
    logK := { lower := (20407727/16777216), upper := (10281179/8388608) }
    logDArg := { lower := (4197893/16777216), upper := (4473287/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk145LogOuterInput_eq :
    sk145RoundedInputs.logOuter = outerEnclosure 24
      (sk145LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk145LogKInput_eq :
    sk145RoundedInputs.logK = outerEnclosure 24
      (sk145LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk145LogDArgInput_eq :
    sk145RoundedInputs.logDArg = outerEnclosure 24
      (sk145LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk145RoundedFacts : SKRoundedFacts 8
    sk145LogOuterCertificate sk145LogKCertificate
    sk145LogDArgCertificate sk145RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk145LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk145LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk145LogDArgInput_eq }

noncomputable def sk146Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16) }

noncomputable def sk146LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4620069/4194304) }, upper := { exponent := 2, mantissa := (71/64) } }

noncomputable def sk146LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (109/64) }, upper := { exponent := 1, mantissa := (55/32) } }

noncomputable def sk146LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (201428411/157155328) }, upper := { exponent := 0, mantissa := (142/109) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk146LogOuter_valid :
    sk146LogOuterCertificate.check sk146Slice.outerAD.value = true := by
  norm_num [sk146LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk146Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk146LogK_valid :
    sk146LogKCertificate.check sk146Slice.kAD.value = true := by
  norm_num [sk146LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk146Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk146LogDArg_valid :
    sk146LogDArgCertificate.check sk146Slice.dArgAD.value = true := by
  norm_num [sk146LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk146Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk146ValidityFacts : SKFacts sk146Slice
    sk146LogOuterCertificate sk146LogKCertificate
    sk146LogDArgCertificate :=
  { domain := by norm_num [sk146Slice]
    kPositive := by
      norm_num [sk146Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk146LogOuter_valid
    logK := sk146LogK_valid
    logDArg := sk146LogDArg_valid }

noncomputable def sk146RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12440109/8388608), upper := (12499791/8388608) }
    logK := { lower := (5140589/4194304), upper := (20715575/16777216) }
    logDArg := { lower := (2082047/8388608), upper := (4437225/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk146LogOuterInput_eq :
    sk146RoundedInputs.logOuter = outerEnclosure 24
      (sk146LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk146LogKInput_eq :
    sk146RoundedInputs.logK = outerEnclosure 24
      (sk146LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk146LogDArgInput_eq :
    sk146RoundedInputs.logDArg = outerEnclosure 24
      (sk146LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk146RoundedFacts : SKRoundedFacts 8
    sk146LogOuterCertificate sk146LogKCertificate
    sk146LogDArgCertificate sk146RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk146LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk146LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk146LogDArgInput_eq }

noncomputable def sk147Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32) }

noncomputable def sk147LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4652835/4194304) }, upper := { exponent := 2, mantissa := (143/128) } }

noncomputable def sk147LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (55/32) }, upper := { exponent := 1, mantissa := (111/64) } }

noncomputable def sk147LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (93053701/72744960) }, upper := { exponent := 0, mantissa := (13/10) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk147LogOuter_valid :
    sk147LogOuterCertificate.check sk147Slice.outerAD.value = true := by
  norm_num [sk147LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk147Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk147LogK_valid :
    sk147LogKCertificate.check sk147Slice.kAD.value = true := by
  norm_num [sk147LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk147Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk147LogDArg_valid :
    sk147LogDArgCertificate.check sk147Slice.dArgAD.value = true := by
  norm_num [sk147LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk147Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk147ValidityFacts : SKFacts sk147Slice
    sk147LogOuterCertificate sk147LogKCertificate
    sk147LogDArgCertificate :=
  { domain := by norm_num [sk147Slice]
    kPositive := by
      norm_num [sk147Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk147LogOuter_valid
    logK := sk147LogK_valid
    logDArg := sk147LogDArg_valid }

noncomputable def sk147RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (195303/131072), upper := (12558659/8388608) }
    logK := { lower := (10357787/8388608), upper := (10433703/8388608) }
    logDArg := { lower := (4130837/16777216), upper := (2200871/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk147LogOuterInput_eq :
    sk147RoundedInputs.logOuter = outerEnclosure 24
      (sk147LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk147LogKInput_eq :
    sk147RoundedInputs.logK = outerEnclosure 24
      (sk147LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk147LogDArgInput_eq :
    sk147RoundedInputs.logDArg = outerEnclosure 24
      (sk147LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk147RoundedFacts : SKRoundedFacts 8
    sk147LogOuterCertificate sk147LogKCertificate
    sk147LogDArgCertificate sk147RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk147LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk147LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk147LogDArgInput_eq }

noncomputable def sk148Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2) }

noncomputable def sk148LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4685601/4194304) }, upper := { exponent := 2, mantissa := (9/8) } }

noncomputable def sk148LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (111/64) }, upper := { exponent := 1, mantissa := (7/4) } }

noncomputable def sk148LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (346723477/271581184) }, upper := { exponent := 0, mantissa := (48/37) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk148LogOuter_valid :
    sk148LogOuterCertificate.check sk148Slice.outerAD.value = true := by
  norm_num [sk148LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk148Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk148LogK_valid :
    sk148LogKCertificate.check sk148Slice.kAD.value = true := by
  norm_num [sk148LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk148Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk148LogDArg_valid :
    sk148LogDArgCertificate.check sk148Slice.dArgAD.value = true := by
  norm_num [sk148LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk148Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk148ValidityFacts : SKFacts sk148Slice
    sk148LogOuterCertificate sk148LogKCertificate
    sk148LogDArgCertificate :=
  { domain := by norm_num [sk148Slice]
    kPositive := by
      norm_num [sk148Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk148LogOuter_valid
    logK := sk148LogK_valid
    logDArg := sk148LogDArg_valid }

noncomputable def sk148RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12558259/8388608), upper := (3154279/2097152) }
    logK := { lower := (20867405/16777216), upper := (5254469/4194304) }
    logDArg := { lower := (4098111/16777216), upper := (2183413/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk148LogOuterInput_eq :
    sk148RoundedInputs.logOuter = outerEnclosure 24
      (sk148LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk148LogKInput_eq :
    sk148RoundedInputs.logK = outerEnclosure 24
      (sk148LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk148LogDArgInput_eq :
    sk148RoundedInputs.logDArg = outerEnclosure 24
      (sk148LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk148RoundedFacts : SKRoundedFacts 8
    sk148LogOuterCertificate sk148LogKCertificate
    sk148LogDArgCertificate sk148RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk148LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk148LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk148LogDArgInput_eq }

noncomputable def sk149Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8) }

noncomputable def sk149LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (1179591/1048576) }, upper := { exponent := 2, mantissa := (37/32) } }

noncomputable def sk149LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (7/4) }, upper := { exponent := 1, mantissa := (29/16) } }

noncomputable def sk149LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (2276699/1835008) }, upper := { exponent := 0, mantissa := (37/28) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk149LogOuter_valid :
    sk149LogOuterCertificate.check sk149Slice.outerAD.value = true := by
  norm_num [sk149LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk149Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk149LogK_valid :
    sk149LogKCertificate.check sk149Slice.kAD.value = true := by
  norm_num [sk149LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk149Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk149LogDArg_valid :
    sk149LogDArgCertificate.check sk149Slice.dArgAD.value = true := by
  norm_num [sk149LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk149Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk149ValidityFacts : SKFacts sk149Slice
    sk149LogOuterCertificate sk149LogKCertificate
    sk149LogDArgCertificate :=
  { domain := by norm_num [sk149Slice]
    kPositive := by
      norm_num [sk149Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk149LogOuter_valid
    logK := sk149LogK_valid
    logDArg := sk149LogDArg_valid }

noncomputable def sk149RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6308355/4194304), upper := (25693911/16777216) }
    logK := { lower := (10508937/8388608), upper := (10803305/8388608) }
    logDArg := { lower := (452309/2097152), upper := (4676035/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk149LogOuterInput_eq :
    sk149RoundedInputs.logOuter = outerEnclosure 24
      (sk149LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk149LogKInput_eq :
    sk149RoundedInputs.logK = outerEnclosure 24
      (sk149LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk149LogDArgInput_eq :
    sk149RoundedInputs.logDArg = outerEnclosure 24
      (sk149LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk149RoundedFacts : SKRoundedFacts 8
    sk149LogOuterCertificate sk149LogKCertificate
    sk149LogDArgCertificate sk149RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk149LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk149LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk149LogDArgInput_eq }

noncomputable def sk150Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4) }

noncomputable def sk150LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (1212357/1048576) }, upper := { exponent := 2, mantissa := (19/16) } }

noncomputable def sk150LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (29/16) }, upper := { exponent := 1, mantissa := (15/8) } }

noncomputable def sk150LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (70283879/57016320) }, upper := { exponent := 0, mantissa := (38/29) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk150LogOuter_valid :
    sk150LogOuterCertificate.check sk150Slice.outerAD.value = true := by
  norm_num [sk150LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk150Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk150LogK_valid :
    sk150LogKCertificate.check sk150Slice.kAD.value = true := by
  norm_num [sk150LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk150Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk150LogDArg_valid :
    sk150LogDArgCertificate.check sk150Slice.dArgAD.value = true := by
  norm_num [sk150LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk150Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk150ValidityFacts : SKFacts sk150Slice
    sk150LogOuterCertificate sk150LogKCertificate
    sk150LogDArgCertificate :=
  { domain := by norm_num [sk150Slice]
    kPositive := by
      norm_num [sk150Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk150LogOuter_valid
    logK := sk150LogK_valid
    logDArg := sk150LogDArg_valid }

noncomputable def sk150RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25693093/16777216), upper := (13070665/8388608) }
    logK := { lower := (21606609/16777216), upper := (2771923/2097152) }
    logDArg := { lower := (877469/4194304), upper := (70855/262144) } }

set_option maxRecDepth 1000000 in
private theorem sk150LogOuterInput_eq :
    sk150RoundedInputs.logOuter = outerEnclosure 24
      (sk150LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk150LogKInput_eq :
    sk150RoundedInputs.logK = outerEnclosure 24
      (sk150LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk150LogDArgInput_eq :
    sk150RoundedInputs.logDArg = outerEnclosure 24
      (sk150LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk150RoundedFacts : SKRoundedFacts 8
    sk150LogOuterCertificate sk150LogKCertificate
    sk150LogDArgCertificate sk150RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk150LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk150LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk150LogDArgInput_eq }

noncomputable def sk151Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16) }

noncomputable def sk151LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2359183/2097152) }, upper := { exponent := 2, mantissa := (73/64) } }

noncomputable def sk151LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (7/4) }, upper := { exponent := 1, mantissa := (57/32) } }

noncomputable def sk151LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (88065205/69730304) }, upper := { exponent := 0, mantissa := (73/56) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk151LogOuter_valid :
    sk151LogOuterCertificate.check sk151Slice.outerAD.value = true := by
  norm_num [sk151LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk151Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk151LogK_valid :
    sk151LogKCertificate.check sk151Slice.kAD.value = true := by
  norm_num [sk151LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk151Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk151LogDArg_valid :
    sk151LogDArgCertificate.check sk151Slice.dArgAD.value = true := by
  norm_num [sk151LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk151Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk151ValidityFacts : SKFacts sk151Slice
    sk151LogOuterCertificate sk151LogKCertificate
    sk151LogDArgCertificate :=
  { domain := by norm_num [sk151Slice]
    kPositive := by
      norm_num [sk151Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk151LogOuter_valid
    logK := sk151LogK_valid
    logDArg := sk151LogDArg_valid }

noncomputable def sk151RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25233427/16777216), upper := (12732823/8388608) }
    logK := { lower := (10508937/8388608), upper := (21314825/16777216) }
    logDArg := { lower := (3916515/16777216), upper := (2223885/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk151LogOuterInput_eq :
    sk151RoundedInputs.logOuter = outerEnclosure 24
      (sk151LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk151LogKInput_eq :
    sk151RoundedInputs.logK = outerEnclosure 24
      (sk151LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk151LogDArgInput_eq :
    sk151RoundedInputs.logDArg = outerEnclosure 24
      (sk151LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk151RoundedFacts : SKRoundedFacts 8
    sk151LogOuterCertificate sk151LogKCertificate
    sk151LogDArgCertificate sk151RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk151LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk151LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk151LogDArgInput_eq }

noncomputable def sk152Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8) }

noncomputable def sk152LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2391949/2097152) }, upper := { exponent := 2, mantissa := (37/32) } }

noncomputable def sk152LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (57/32) }, upper := { exponent := 1, mantissa := (29/16) } }

noncomputable def sk152LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (90883101/72220672) }, upper := { exponent := 0, mantissa := (74/57) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk152LogOuter_valid :
    sk152LogOuterCertificate.check sk152Slice.outerAD.value = true := by
  norm_num [sk152LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk152Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk152LogK_valid :
    sk152LogKCertificate.check sk152Slice.kAD.value = true := by
  norm_num [sk152LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk152Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk152LogDArg_valid :
    sk152LogDArgCertificate.check sk152Slice.dArgAD.value = true := by
  norm_num [sk152LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk152Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk152ValidityFacts : SKFacts sk152Slice
    sk152LogOuterCertificate sk152LogKCertificate
    sk152LogDArgCertificate :=
  { domain := by norm_num [sk152Slice]
    kPositive := by
      norm_num [sk152Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk152LogOuter_valid
    logK := sk152LogK_valid
    logDArg := sk152LogDArg_valid }

noncomputable def sk152RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12732419/8388608), upper := (25693911/16777216) }
    logK := { lower := (2664353/2097152), upper := (10803305/8388608) }
    logDArg := { lower := (3856205/16777216), upper := (2189543/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk152LogOuterInput_eq :
    sk152RoundedInputs.logOuter = outerEnclosure 24
      (sk152LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk152LogKInput_eq :
    sk152RoundedInputs.logK = outerEnclosure 24
      (sk152LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk152LogDArgInput_eq :
    sk152RoundedInputs.logDArg = outerEnclosure 24
      (sk152LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk152RoundedFacts : SKRoundedFacts 8
    sk152LogOuterCertificate sk152LogKCertificate
    sk152LogDArgCertificate sk152RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk152LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk152LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk152LogDArgInput_eq }

noncomputable def sk153Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16) }

noncomputable def sk153LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2424715/2097152) }, upper := { exponent := 2, mantissa := (75/64) } }

noncomputable def sk153LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (29/16) }, upper := { exponent := 1, mantissa := (59/32) } }

noncomputable def sk153LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (281234055/224264192) }, upper := { exponent := 0, mantissa := (75/58) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk153LogOuter_valid :
    sk153LogOuterCertificate.check sk153Slice.outerAD.value = true := by
  norm_num [sk153LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk153Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk153LogK_valid :
    sk153LogKCertificate.check sk153Slice.kAD.value = true := by
  norm_num [sk153LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk153Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk153LogDArg_valid :
    sk153LogDArgCertificate.check sk153Slice.dArgAD.value = true := by
  norm_num [sk153LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk153Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk153ValidityFacts : SKFacts sk153Slice
    sk153LogOuterCertificate sk153LogKCertificate
    sk153LogDArgCertificate :=
  { domain := by norm_num [sk153Slice]
    kPositive := by
      norm_num [sk153Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk153LogOuter_valid
    logK := sk153LogK_valid
    logDArg := sk153LogDArg_valid }

noncomputable def sk153RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6423275/4194304), upper := (3239889/2097152) }
    logK := { lower := (21606609/16777216), upper := (21893407/16777216) }
    logDArg := { lower := (949433/4194304), upper := (2156251/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk153LogOuterInput_eq :
    sk153RoundedInputs.logOuter = outerEnclosure 24
      (sk153LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk153LogKInput_eq :
    sk153RoundedInputs.logK = outerEnclosure 24
      (sk153LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk153LogDArgInput_eq :
    sk153RoundedInputs.logDArg = outerEnclosure 24
      (sk153LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk153RoundedFacts : SKRoundedFacts 8
    sk153LogOuterCertificate sk153LogKCertificate
    sk153LogDArgCertificate sk153RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk153LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk153LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk153LogDArgInput_eq }

noncomputable def sk154Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4) }

noncomputable def sk154LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2457481/2097152) }, upper := { exponent := 2, mantissa := (19/16) } }

noncomputable def sk154LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (59/32) }, upper := { exponent := 1, mantissa := (15/8) } }

noncomputable def sk154LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (96649957/77332480) }, upper := { exponent := 0, mantissa := (76/59) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk154LogOuter_valid :
    sk154LogOuterCertificate.check sk154Slice.outerAD.value = true := by
  norm_num [sk154LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk154Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk154LogK_valid :
    sk154LogKCertificate.check sk154Slice.kAD.value = true := by
  norm_num [sk154LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk154Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk154LogDArg_valid :
    sk154LogDArgCertificate.check sk154Slice.dArgAD.value = true := by
  norm_num [sk154LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk154Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk154ValidityFacts : SKFacts sk154Slice
    sk154LogOuterCertificate sk154LogKCertificate
    sk154LogDArgCertificate :=
  { domain := by norm_num [sk154Slice]
    kPositive := by
      norm_num [sk154Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk154LogOuter_valid
    logK := sk154LogK_valid
    logDArg := sk154LogDArg_valid }

noncomputable def sk154RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12959149/8388608), upper := (13070665/8388608) }
    logK := { lower := (10946703/8388608), upper := (2771923/2097152) }
    logDArg := { lower := (935253/4194304), upper := (4247923/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk154LogOuterInput_eq :
    sk154RoundedInputs.logOuter = outerEnclosure 24
      (sk154LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk154LogKInput_eq :
    sk154RoundedInputs.logK = outerEnclosure 24
      (sk154LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk154LogDArgInput_eq :
    sk154RoundedInputs.logDArg = outerEnclosure 24
      (sk154LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk154RoundedFacts : SKRoundedFacts 8
    sk154LogOuterCertificate sk154LogKCertificate
    sk154LogDArgCertificate sk154RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk154LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk154LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk154LogDArgInput_eq }

noncomputable def sk155Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8) }

noncomputable def sk155LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (1245123/1048576) }, upper := { exponent := 2, mantissa := (39/32) } }

noncomputable def sk155LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (15/8) }, upper := { exponent := 1, mantissa := (31/16) } }

noncomputable def sk155LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (24891517/20316160) }, upper := { exponent := 0, mantissa := (13/10) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk155LogOuter_valid :
    sk155LogOuterCertificate.check sk155Slice.outerAD.value = true := by
  norm_num [sk155LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk155Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk155LogK_valid :
    sk155LogKCertificate.check sk155Slice.kAD.value = true := by
  norm_num [sk155LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk155Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk155LogDArg_valid :
    sk155LogDArgCertificate.check sk155Slice.dArgAD.value = true := by
  norm_num [sk155LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk155Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk155ValidityFacts : SKFacts sk155Slice
    sk155LogOuterCertificate sk155LogKCertificate
    sk155LogDArgCertificate :=
  { domain := by norm_num [sk155Slice]
    kPositive := by
      norm_num [sk155Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk155LogOuter_valid
    logK := sk155LogK_valid
    logDArg := sk155LogDArg_valid }

noncomputable def sk155RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13070253/8388608), upper := (13288563/8388608) }
    logK := { lower := (22175383/16777216), upper := (11362753/8388608) }
    logDArg := { lower := (3407627/16777216), upper := (2200871/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk155LogOuterInput_eq :
    sk155RoundedInputs.logOuter = outerEnclosure 24
      (sk155LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk155LogKInput_eq :
    sk155RoundedInputs.logK = outerEnclosure 24
      (sk155LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk155LogDArgInput_eq :
    sk155RoundedInputs.logDArg = outerEnclosure 24
      (sk155LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk155RoundedFacts : SKRoundedFacts 8
    sk155LogOuterCertificate sk155LogKCertificate
    sk155LogDArgCertificate sk155RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk155LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk155LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk155LogDArgInput_eq }

noncomputable def sk156Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4) }

noncomputable def sk156LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (1277889/1048576) }, upper := { exponent := 2, mantissa := (5/4) } }

noncomputable def sk156LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (31/16) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk156LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (79196287/65011712) }, upper := { exponent := 0, mantissa := (40/31) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk156LogOuter_valid :
    sk156LogOuterCertificate.check sk156Slice.outerAD.value = true := by
  norm_num [sk156LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk156Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk156LogK_valid :
    sk156LogKCertificate.check sk156Slice.kAD.value = true := by
  norm_num [sk156LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk156Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk156LogDArg_valid :
    sk156LogDArgCertificate.check sk156Slice.dArgAD.value = true := by
  norm_num [sk156LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk156Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk156ValidityFacts : SKFacts sk156Slice
    sk156LogOuterCertificate sk156LogKCertificate
    sk156LogDArgCertificate :=
  { domain := by norm_num [sk156Slice]
    kPositive := by
      norm_num [sk156Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk156LogOuter_valid
    logK := sk156LogK_valid
    logDArg := sk156LogDArg_valid }

noncomputable def sk156RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13288149/8388608), upper := (27001889/16777216) }
    logK := { lower := (22725505/16777216), upper := (23258161/16777216) }
    logDArg := { lower := (206949/1048576), upper := (4276383/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk156LogOuterInput_eq :
    sk156RoundedInputs.logOuter = outerEnclosure 24
      (sk156LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk156LogKInput_eq :
    sk156RoundedInputs.logK = outerEnclosure 24
      (sk156LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk156LogDArgInput_eq :
    sk156RoundedInputs.logDArg = outerEnclosure 24
      (sk156LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk156RoundedFacts : SKRoundedFacts 8
    sk156LogOuterCertificate sk156LogKCertificate
    sk156LogDArgCertificate sk156RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk156LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk156LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk156LogDArgInput_eq }

noncomputable def sk157Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16) }

noncomputable def sk157LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2490247/2097152) }, upper := { exponent := 2, mantissa := (77/64) } }

noncomputable def sk157LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (15/8) }, upper := { exponent := 1, mantissa := (61/32) } }

noncomputable def sk157LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (99598917/79953920) }, upper := { exponent := 0, mantissa := (77/60) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk157LogOuter_valid :
    sk157LogOuterCertificate.check sk157Slice.outerAD.value = true := by
  norm_num [sk157LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk157Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk157LogK_valid :
    sk157LogKCertificate.check sk157Slice.kAD.value = true := by
  norm_num [sk157LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk157Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk157LogDArg_valid :
    sk157LogDArgCertificate.check sk157Slice.dArgAD.value = true := by
  norm_num [sk157LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk157Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk157ValidityFacts : SKFacts sk157Slice
    sk157LogOuterCertificate sk157LogKCertificate
    sk157LogDArgCertificate :=
  { domain := by norm_num [sk157Slice]
    kPositive := by
      norm_num [sk157Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk157LogOuter_valid
    logK := sk157LogK_valid
    logDArg := sk157LogDArg_valid }

noncomputable def sk157RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26140513/16777216), upper := (26360643/16777216) }
    logK := { lower := (22175383/16777216), upper := (5613175/4194304) }
    logDArg := { lower := (230373/1048576), upper := (4185259/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk157LogOuterInput_eq :
    sk157RoundedInputs.logOuter = outerEnclosure 24
      (sk157LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk157LogKInput_eq :
    sk157RoundedInputs.logK = outerEnclosure 24
      (sk157LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk157LogDArgInput_eq :
    sk157RoundedInputs.logDArg = outerEnclosure 24
      (sk157LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk157RoundedFacts : SKRoundedFacts 8
    sk157LogOuterCertificate sk157LogKCertificate
    sk157LogDArgCertificate sk157RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk157LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk157LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk157LogDArgInput_eq }

noncomputable def sk158Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8) }

noncomputable def sk158LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2523013/2097152) }, upper := { exponent := 2, mantissa := (39/32) } }

noncomputable def sk158LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (61/32) }, upper := { exponent := 1, mantissa := (31/16) } }

noncomputable def sk158LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (307774695/247857152) }, upper := { exponent := 0, mantissa := (78/61) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk158LogOuter_valid :
    sk158LogOuterCertificate.check sk158Slice.outerAD.value = true := by
  norm_num [sk158LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk158Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk158LogK_valid :
    sk158LogKCertificate.check sk158Slice.kAD.value = true := by
  norm_num [sk158LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk158Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk158LogDArg_valid :
    sk158LogDArgCertificate.check sk158Slice.dArgAD.value = true := by
  norm_num [sk158LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk158Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk158ValidityFacts : SKFacts sk158Slice
    sk158LogOuterCertificate sk158LogKCertificate
    sk158LogDArgCertificate :=
  { domain := by norm_num [sk158Slice]
    kPositive := by
      norm_num [sk158Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk158LogOuter_valid
    logK := sk158LogK_valid
    logDArg := sk158LogDArg_valid }

noncomputable def sk158RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1647489/1048576), upper := (13288563/8388608) }
    logK := { lower := (11226349/8388608), upper := (11362753/8388608) }
    logDArg := { lower := (1816263/8388608), upper := (4124427/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk158LogOuterInput_eq :
    sk158RoundedInputs.logOuter = outerEnclosure 24
      (sk158LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk158LogKInput_eq :
    sk158RoundedInputs.logK = outerEnclosure 24
      (sk158LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk158LogDArgInput_eq :
    sk158RoundedInputs.logDArg = outerEnclosure 24
      (sk158LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk158RoundedFacts : SKRoundedFacts 8
    sk158LogOuterCertificate sk158LogKCertificate
    sk158LogDArgCertificate sk158RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk158LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk158LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk158LogDArgInput_eq }

noncomputable def sk159Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16) }

noncomputable def sk159LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2555779/2097152) }, upper := { exponent := 2, mantissa := (79/64) } }

noncomputable def sk159LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (31/16) }, upper := { exponent := 1, mantissa := (63/32) } }

noncomputable def sk159LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (105627901/85327872) }, upper := { exponent := 0, mantissa := (79/62) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk159LogOuter_valid :
    sk159LogOuterCertificate.check sk159Slice.outerAD.value = true := by
  norm_num [sk159LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk159Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk159LogK_valid :
    sk159LogKCertificate.check sk159Slice.kAD.value = true := by
  norm_num [sk159LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk159Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk159LogDArg_valid :
    sk159LogDArgCertificate.check sk159Slice.dArgAD.value = true := by
  norm_num [sk159LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk159Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk159ValidityFacts : SKFacts sk159Slice
    sk159LogOuterCertificate sk159LogKCertificate
    sk159LogDArgCertificate :=
  { domain := by norm_num [sk159Slice]
    kPositive := by
      norm_num [sk159Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk159LogOuter_valid
    logK := sk159LogK_valid
    logDArg := sk159LogDArg_valid }

noncomputable def sk159RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1661019/1048576), upper := (6697713/4194304) }
    logK := { lower := (22725505/16777216), upper := (22993947/16777216) }
    logDArg := { lower := (447577/2097152), upper := (2032673/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk159LogOuterInput_eq :
    sk159RoundedInputs.logOuter = outerEnclosure 24
      (sk159LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk159LogKInput_eq :
    sk159RoundedInputs.logK = outerEnclosure 24
      (sk159LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk159LogDArgInput_eq :
    sk159RoundedInputs.logDArg = outerEnclosure 24
      (sk159LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk159RoundedFacts : SKRoundedFacts 8
    sk159LogOuterCertificate sk159LogKCertificate
    sk159LogDArgCertificate sk159RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk159LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk159LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk159LogDArgInput_eq }

noncomputable def sk160Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4) }

noncomputable def sk160LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2588545/2097152) }, upper := { exponent := 2, mantissa := (5/4) } }

noncomputable def sk160LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (63/32) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk160LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (36235975/29360128) }, upper := { exponent := 0, mantissa := (80/63) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk160LogOuter_valid :
    sk160LogOuterCertificate.check sk160Slice.outerAD.value = true := by
  norm_num [sk160LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk160Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk160LogK_valid :
    sk160LogKCertificate.check sk160Slice.kAD.value = true := by
  norm_num [sk160LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk160Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk160LogDArg_valid :
    sk160LogDArgCertificate.check sk160Slice.dArgAD.value = true := by
  norm_num [sk160LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk160Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk160ValidityFacts : SKFacts sk160Slice
    sk160LogOuterCertificate sk160LogKCertificate
    sk160LogDArgCertificate :=
  { domain := by norm_num [sk160Slice]
    kPositive := by
      norm_num [sk160Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk160LogOuter_valid
    logK := sk160LogK_valid
    logDArg := sk160LogDArg_valid }

noncomputable def sk160RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26790027/16777216), upper := (27001889/16777216) }
    logK := { lower := (11496973/8388608), upper := (23258161/16777216) }
    logDArg := { lower := (3530175/16777216), upper := (2003971/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk160LogOuterInput_eq :
    sk160RoundedInputs.logOuter = outerEnclosure 24
      (sk160LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk160LogKInput_eq :
    sk160RoundedInputs.logK = outerEnclosure 24
      (sk160LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk160LogDArgInput_eq :
    sk160RoundedInputs.logDArg = outerEnclosure 24
      (sk160LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk160RoundedFacts : SKRoundedFacts 8
    sk160LogOuterCertificate sk160LogKCertificate
    sk160LogDArgCertificate sk160RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk160LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk160LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk160LogDArgInput_eq }

noncomputable def sk161Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32) }

noncomputable def sk161LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4783899/4194304) }, upper := { exponent := 2, mantissa := (147/128) } }

noncomputable def sk161LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (57/32) }, upper := { exponent := 1, mantissa := (115/64) } }

noncomputable def sk161LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (72713065/57278464) }, upper := { exponent := 0, mantissa := (49/38) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk161LogOuter_valid :
    sk161LogOuterCertificate.check sk161Slice.outerAD.value = true := by
  norm_num [sk161LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk161Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk161LogK_valid :
    sk161LogKCertificate.check sk161Slice.kAD.value = true := by
  norm_num [sk161LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk161Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk161LogDArg_valid :
    sk161LogDArgCertificate.check sk161Slice.dArgAD.value = true := by
  norm_num [sk161LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk161Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk161ValidityFacts : SKFacts sk161Slice
    sk161LogOuterCertificate sk161LogKCertificate
    sk161LogDArgCertificate :=
  { domain := by norm_num [sk161Slice]
    kPositive := by
      norm_num [sk161Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk161LogOuter_valid
    logK := sk161LogK_valid
    logDArg := sk161LogDArg_valid }

noncomputable def sk161RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25464841/16777216), upper := (25580167/16777216) }
    logK := { lower := (2664353/2097152), upper := (2682669/2097152) }
    logDArg := { lower := (2001491/8388608), upper := (2132671/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk161LogOuterInput_eq :
    sk161RoundedInputs.logOuter = outerEnclosure 24
      (sk161LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk161LogKInput_eq :
    sk161RoundedInputs.logK = outerEnclosure 24
      (sk161LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk161LogDArgInput_eq :
    sk161RoundedInputs.logDArg = outerEnclosure 24
      (sk161LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk161RoundedFacts : SKRoundedFacts 8
    sk161LogOuterCertificate sk161LogKCertificate
    sk161LogDArgCertificate sk161RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk161LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk161LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk161LogDArgInput_eq }

noncomputable def sk162Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8) }

noncomputable def sk162LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4816665/4194304) }, upper := { exponent := 2, mantissa := (37/32) } }

noncomputable def sk162LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (115/64) }, upper := { exponent := 1, mantissa := (29/16) } }

noncomputable def sk162LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1107799951/874250240) }, upper := { exponent := 0, mantissa := (148/115) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk162LogOuter_valid :
    sk162LogOuterCertificate.check sk162Slice.outerAD.value = true := by
  norm_num [sk162LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk162Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk162LogK_valid :
    sk162LogKCertificate.check sk162Slice.kAD.value = true := by
  norm_num [sk162LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk162Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk162LogDArg_valid :
    sk162LogDArgCertificate.check sk162Slice.dArgAD.value = true := by
  norm_num [sk162LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk162Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk162ValidityFacts : SKFacts sk162Slice
    sk162LogOuterCertificate sk162LogKCertificate
    sk162LogDArgCertificate :=
  { domain := by norm_num [sk162Slice]
    kPositive := by
      norm_num [sk162Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk162LogOuter_valid
    logK := sk162LogK_valid
    logDArg := sk162LogDArg_valid }

noncomputable def sk162RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (799355/524288), upper := (25693911/16777216) }
    logK := { lower := (21461351/16777216), upper := (10803305/8388608) }
    logDArg := { lower := (3972251/16777216), upper := (4232559/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk162LogOuterInput_eq :
    sk162RoundedInputs.logOuter = outerEnclosure 24
      (sk162LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk162LogKInput_eq :
    sk162RoundedInputs.logK = outerEnclosure 24
      (sk162LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk162LogDArgInput_eq :
    sk162RoundedInputs.logDArg = outerEnclosure 24
      (sk162LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk162RoundedFacts : SKRoundedFacts 8
    sk162LogOuterCertificate sk162LogKCertificate
    sk162LogDArgCertificate sk162RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk162LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk162LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk162LogDArgInput_eq }

noncomputable def sk163Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32) }

noncomputable def sk163LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4849431/4194304) }, upper := { exponent := 2, mantissa := (149/128) } }

noncomputable def sk163LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (29/16) }, upper := { exponent := 1, mantissa := (117/64) } }

noncomputable def sk163LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1125034991/889454592) }, upper := { exponent := 0, mantissa := (149/116) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk163LogOuter_valid :
    sk163LogOuterCertificate.check sk163Slice.outerAD.value = true := by
  norm_num [sk163LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk163Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk163LogK_valid :
    sk163LogKCertificate.check sk163Slice.kAD.value = true := by
  norm_num [sk163LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk163Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk163LogDArg_valid :
    sk163LogDArgCertificate.check sk163Slice.dArgAD.value = true := by
  norm_num [sk163LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk163Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk163ValidityFacts : SKFacts sk163Slice
    sk163LogOuterCertificate sk163LogKCertificate
    sk163LogDArgCertificate :=
  { domain := by norm_num [sk163Slice]
    kPositive := by
      norm_num [sk163Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk163LogOuter_valid
    logK := sk163LogK_valid
    logDArg := sk163LogDArg_valid }

noncomputable def sk163RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25693103/16777216), upper := (25806889/16777216) }
    logK := { lower := (21606609/16777216), upper := (10875311/8388608) }
    logDArg := { lower := (1970995/8388608), upper := (4200279/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk163LogOuterInput_eq :
    sk163RoundedInputs.logOuter = outerEnclosure 24
      (sk163LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk163LogKInput_eq :
    sk163RoundedInputs.logK = outerEnclosure 24
      (sk163LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk163LogDArgInput_eq :
    sk163RoundedInputs.logDArg = outerEnclosure 24
      (sk163LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk163RoundedFacts : SKRoundedFacts 8
    sk163LogOuterCertificate sk163LogKCertificate
    sk163LogDArgCertificate sk163RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk163LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk163LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk163LogDArgInput_eq }

noncomputable def sk164Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16) }

noncomputable def sk164LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4882197/4194304) }, upper := { exponent := 2, mantissa := (75/64) } }

noncomputable def sk164LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (117/64) }, upper := { exponent := 1, mantissa := (59/32) } }

noncomputable def sk164LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (126933455/100532224) }, upper := { exponent := 0, mantissa := (50/39) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk164LogOuter_valid :
    sk164LogOuterCertificate.check sk164Slice.outerAD.value = true := by
  norm_num [sk164LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk164Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk164LogK_valid :
    sk164LogKCertificate.check sk164Slice.kAD.value = true := by
  norm_num [sk164LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk164Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk164LogDArg_valid :
    sk164LogDArgCertificate.check sk164Slice.dArgAD.value = true := by
  norm_num [sk164LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk164Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk164ValidityFacts : SKFacts sk164Slice
    sk164LogOuterCertificate sk164LogKCertificate
    sk164LogDArgCertificate :=
  { domain := by norm_num [sk164Slice]
    kPositive := by
      norm_num [sk164Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk164LogOuter_valid
    logK := sk164LogK_valid
    logDArg := sk164LogDArg_valid }

noncomputable def sk164RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (100805/65536), upper := (3239889/2097152) }
    logK := { lower := (5437655/4194304), upper := (21893407/16777216) }
    logDArg := { lower := (3912189/16777216), upper := (2084245/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk164LogOuterInput_eq :
    sk164RoundedInputs.logOuter = outerEnclosure 24
      (sk164LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk164LogKInput_eq :
    sk164RoundedInputs.logK = outerEnclosure 24
      (sk164LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk164LogDArgInput_eq :
    sk164RoundedInputs.logDArg = outerEnclosure 24
      (sk164LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk164RoundedFacts : SKRoundedFacts 8
    sk164LogOuterCertificate sk164LogKCertificate
    sk164LogDArgCertificate sk164RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk164LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk164LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk164LogDArgInput_eq }

noncomputable def sk165Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32) }

noncomputable def sk165LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4914963/4194304) }, upper := { exponent := 2, mantissa := (151/128) } }

noncomputable def sk165LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (59/32) }, upper := { exponent := 1, mantissa := (119/64) } }

noncomputable def sk165LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1159898263/920256512) }, upper := { exponent := 0, mantissa := (151/118) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk165LogOuter_valid :
    sk165LogOuterCertificate.check sk165Slice.outerAD.value = true := by
  norm_num [sk165LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk165Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk165LogK_valid :
    sk165LogKCertificate.check sk165Slice.kAD.value = true := by
  norm_num [sk165LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk165Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk165LogDArg_valid :
    sk165LogDArgCertificate.check sk165Slice.dArgAD.value = true := by
  norm_num [sk165LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk165Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk165ValidityFacts : SKFacts sk165Slice
    sk165LogOuterCertificate sk165LogKCertificate
    sk165LogDArgCertificate :=
  { domain := by norm_num [sk165Slice]
    kPositive := by
      norm_num [sk165Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk165LogOuter_valid
    logK := sk165LogK_valid
    logDArg := sk165LogDArg_valid }

noncomputable def sk165RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25918301/16777216), upper := (26030589/16777216) }
    logK := { lower := (10946703/8388608), upper := (5508747/4194304) }
    logDArg := { lower := (3882837/16777216), upper := (2068591/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk165LogOuterInput_eq :
    sk165RoundedInputs.logOuter = outerEnclosure 24
      (sk165LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk165LogKInput_eq :
    sk165RoundedInputs.logK = outerEnclosure 24
      (sk165LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk165LogDArgInput_eq :
    sk165RoundedInputs.logDArg = outerEnclosure 24
      (sk165LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk165RoundedFacts : SKRoundedFacts 8
    sk165LogOuterCertificate sk165LogKCertificate
    sk165LogDArgCertificate sk165RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk165LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk165LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk165LogDArgInput_eq }

noncomputable def sk166Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4) }

noncomputable def sk166LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4947729/4194304) }, upper := { exponent := 2, mantissa := (19/16) } }

noncomputable def sk166LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (119/64) }, upper := { exponent := 1, mantissa := (15/8) } }

noncomputable def sk166LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (235505299/187170816) }, upper := { exponent := 0, mantissa := (152/119) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk166LogOuter_valid :
    sk166LogOuterCertificate.check sk166Slice.outerAD.value = true := by
  norm_num [sk166LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk166Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk166LogK_valid :
    sk166LogKCertificate.check sk166Slice.kAD.value = true := by
  norm_num [sk166LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk166Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk166LogDArg_valid :
    sk166LogDArgCertificate.check sk166Slice.dArgAD.value = true := by
  norm_num [sk166LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk166Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk166ValidityFacts : SKFacts sk166Slice
    sk166LogOuterCertificate sk166LogKCertificate
    sk166LogDArgCertificate :=
  { domain := by norm_num [sk166Slice]
    kPositive := by
      norm_num [sk166Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk166LogOuter_valid
    logK := sk166LogK_valid
    logDArg := sk166LogDArg_valid }

noncomputable def sk166RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26029777/16777216), upper := (13070665/8388608) }
    logK := { lower := (22034987/16777216), upper := (2771923/2097152) }
    logDArg := { lower := (3853923/16777216), upper := (2053171/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk166LogOuterInput_eq :
    sk166RoundedInputs.logOuter = outerEnclosure 24
      (sk166LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk166LogKInput_eq :
    sk166RoundedInputs.logK = outerEnclosure 24
      (sk166LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk166LogDArgInput_eq :
    sk166RoundedInputs.logDArg = outerEnclosure 24
      (sk166LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk166RoundedFacts : SKRoundedFacts 8
    sk166LogOuterCertificate sk166LogKCertificate
    sk166LogDArgCertificate sk166RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk166LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk166LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk166LogDArgInput_eq }

noncomputable def sk167Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32) }

noncomputable def sk167LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4718367/4194304) }, upper := { exponent := 2, mantissa := (145/128) } }

noncomputable def sk167LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (7/4) }, upper := { exponent := 1, mantissa := (113/64) } }

noncomputable def sk167LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1056881215/829423616) }, upper := { exponent := 0, mantissa := (145/112) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk167LogOuter_valid :
    sk167LogOuterCertificate.check sk167Slice.outerAD.value = true := by
  norm_num [sk167LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk167Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk167LogK_valid :
    sk167LogKCertificate.check sk167Slice.kAD.value = true := by
  norm_num [sk167LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk167Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk167LogDArg_valid :
    sk167LogDArgCertificate.check sk167Slice.dArgAD.value = true := by
  norm_num [sk167LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk167Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk167ValidityFacts : SKFacts sk167Slice
    sk167LogOuterCertificate sk167LogKCertificate
    sk167LogDArgCertificate :=
  { domain := by norm_num [sk167Slice]
    kPositive := by
      norm_num [sk167Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk167LogOuter_valid
    logK := sk167LogK_valid
    logDArg := sk167LogDArg_valid }

noncomputable def sk167RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25233431/16777216), upper := (12675169/8388608) }
    logK := { lower := (10508937/8388608), upper := (21167007/16777216) }
    logDArg := { lower := (1016475/4194304), upper := (4332463/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk167LogOuterInput_eq :
    sk167RoundedInputs.logOuter = outerEnclosure 24
      (sk167LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk167LogKInput_eq :
    sk167RoundedInputs.logK = outerEnclosure 24
      (sk167LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk167LogDArgInput_eq :
    sk167RoundedInputs.logDArg = outerEnclosure 24
      (sk167LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk167RoundedFacts : SKRoundedFacts 8
    sk167LogOuterCertificate sk167LogKCertificate
    sk167LogDArgCertificate sk167RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk167LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk167LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk167LogDArgInput_eq }

noncomputable def sk168Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16) }

noncomputable def sk168LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4751133/4194304) }, upper := { exponent := 2, mantissa := (73/64) } }

noncomputable def sk168LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (113/64) }, upper := { exponent := 1, mantissa := (57/32) } }

noncomputable def sk168LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1073723063/844234752) }, upper := { exponent := 0, mantissa := (146/113) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk168LogOuter_valid :
    sk168LogOuterCertificate.check sk168Slice.outerAD.value = true := by
  norm_num [sk168LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk168Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk168LogK_valid :
    sk168LogKCertificate.check sk168Slice.kAD.value = true := by
  norm_num [sk168LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk168Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk168LogDArg_valid :
    sk168LogDArgCertificate.check sk168Slice.dArgAD.value = true := by
  norm_num [sk168LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk168Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk168ValidityFacts : SKFacts sk168Slice
    sk168LogOuterCertificate sk168LogKCertificate
    sk168LogDArgCertificate :=
  { domain := by norm_num [sk168Slice]
    kPositive := by
      norm_num [sk168Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk168LogOuter_valid
    logK := sk168LogK_valid
    logDArg := sk168LogDArg_valid }

noncomputable def sk168RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25349535/16777216), upper := (12732823/8388608) }
    logK := { lower := (10583503/8388608), upper := (21314825/16777216) }
    logDArg := { lower := (4034195/16777216), upper := (4298639/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk168LogOuterInput_eq :
    sk168RoundedInputs.logOuter = outerEnclosure 24
      (sk168LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk168LogKInput_eq :
    sk168RoundedInputs.logK = outerEnclosure 24
      (sk168LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk168LogDArgInput_eq :
    sk168RoundedInputs.logDArg = outerEnclosure 24
      (sk168LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk168RoundedFacts : SKRoundedFacts 8
    sk168LogOuterCertificate sk168LogKCertificate
    sk168LogDArgCertificate sk168RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk168LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk168LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk168LogDArgInput_eq }

noncomputable def sk169Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32) }

noncomputable def sk169LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (4980495/4194304) }, upper := { exponent := 2, mantissa := (153/128) } }

noncomputable def sk169LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (15/8) }, upper := { exponent := 1, mantissa := (121/64) } }

noncomputable def sk169LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (398428597/317194240) }, upper := { exponent := 0, mantissa := (51/40) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk169LogOuter_valid :
    sk169LogOuterCertificate.check sk169Slice.outerAD.value = true := by
  norm_num [sk169LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk169Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk169LogK_valid :
    sk169LogKCertificate.check sk169Slice.kAD.value = true := by
  norm_num [sk169LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk169Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk169LogDArg_valid :
    sk169LogDArgCertificate.check sk169Slice.dArgAD.value = true := by
  norm_num [sk169LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk169Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk169ValidityFacts : SKFacts sk169Slice
    sk169LogOuterCertificate sk169LogKCertificate
    sk169LogDArgCertificate :=
  { domain := by norm_num [sk169Slice]
    kPositive := by
      norm_num [sk169Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk169LogOuter_valid
    logK := sk169LogK_valid
    logDArg := sk169LogDArg_valid }

noncomputable def sk169RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6535129/4194304), upper := (26251345/16777216) }
    logK := { lower := (22175383/16777216), upper := (22314615/16777216) }
    logDArg := { lower := (3825439/16777216), upper := (4075961/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk169LogOuterInput_eq :
    sk169RoundedInputs.logOuter = outerEnclosure 24
      (sk169LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk169LogKInput_eq :
    sk169RoundedInputs.logK = outerEnclosure 24
      (sk169LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk169LogDArgInput_eq :
    sk169RoundedInputs.logDArg = outerEnclosure 24
      (sk169LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk169RoundedFacts : SKRoundedFacts 8
    sk169LogOuterCertificate sk169LogKCertificate
    sk169LogDArgCertificate sk169RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk169LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk169LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk169LogDArgInput_eq }

noncomputable def sk170Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16) }

noncomputable def sk170LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (5013261/4194304) }, upper := { exponent := 2, mantissa := (77/64) } }

noncomputable def sk170LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (121/64) }, upper := { exponent := 1, mantissa := (61/32) } }

noncomputable def sk170LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (110288741/87949312) }, upper := { exponent := 0, mantissa := (14/11) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk170LogOuter_valid :
    sk170LogOuterCertificate.check sk170Slice.outerAD.value = true := by
  norm_num [sk170LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk170Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk170LogK_valid :
    sk170LogKCertificate.check sk170Slice.kAD.value = true := by
  norm_num [sk170LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk170Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk170LogDArg_valid :
    sk170LogDArgCertificate.check sk170Slice.dArgAD.value = true := by
  norm_num [sk170LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk170Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk170ValidityFacts : SKFacts sk170Slice
    sk170LogOuterCertificate sk170LogKCertificate
    sk170LogDArgCertificate :=
  { domain := by norm_num [sk170Slice]
    kPositive := by
      norm_num [sk170Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk170LogOuter_valid
    logK := sk170LogK_valid
    logDArg := sk170LogDArg_valid }

noncomputable def sk170RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13125265/8388608), upper := (26360643/16777216) }
    logK := { lower := (11157307/8388608), upper := (5613175/4194304) }
    logDArg := { lower := (3797375/16777216), upper := (1011507/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk170LogOuterInput_eq :
    sk170RoundedInputs.logOuter = outerEnclosure 24
      (sk170LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk170LogKInput_eq :
    sk170RoundedInputs.logK = outerEnclosure 24
      (sk170LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk170LogDArgInput_eq :
    sk170RoundedInputs.logDArg = outerEnclosure 24
      (sk170LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk170RoundedFacts : SKRoundedFacts 8
    sk170LogOuterCertificate sk170LogKCertificate
    sk170LogDArgCertificate sk170RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk170LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk170LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk170LogDArgInput_eq }

noncomputable def sk171Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32) }

noncomputable def sk171LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (5046027/4194304) }, upper := { exponent := 2, mantissa := (155/128) } }

noncomputable def sk171LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (61/32) }, upper := { exponent := 1, mantissa := (123/64) } }

noncomputable def sk171LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1231197575/983433216) }, upper := { exponent := 0, mantissa := (155/122) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk171LogOuter_valid :
    sk171LogOuterCertificate.check sk171Slice.outerAD.value = true := by
  norm_num [sk171LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk171Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk171LogK_valid :
    sk171LogKCertificate.check sk171Slice.kAD.value = true := by
  norm_num [sk171LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk171Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk171LogDArg_valid :
    sk171LogDArgCertificate.check sk171Slice.dArgAD.value = true := by
  norm_num [sk171LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk171Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk171ValidityFacts : SKFacts sk171Slice
    sk171LogOuterCertificate sk171LogKCertificate
    sk171LogDArgCertificate :=
  { domain := by norm_num [sk171Slice]
    kPositive := by
      norm_num [sk171Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk171LogOuter_valid
    logK := sk171LogK_valid
    logDArg := sk171LogDArg_valid }

noncomputable def sk171RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26359827/16777216), upper := (13234617/8388608) }
    logK := { lower := (11226349/8388608), upper := (22589657/16777216) }
    logDArg := { lower := (3769721/16777216), upper := (2008267/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk171LogOuterInput_eq :
    sk171RoundedInputs.logOuter = outerEnclosure 24
      (sk171LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk171LogKInput_eq :
    sk171RoundedInputs.logK = outerEnclosure 24
      (sk171LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk171LogDArgInput_eq :
    sk171RoundedInputs.logDArg = outerEnclosure 24
      (sk171LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk171RoundedFacts : SKRoundedFacts 8
    sk171LogOuterCertificate sk171LogKCertificate
    sk171LogDArgCertificate sk171RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk171LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk171LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk171LogDArgInput_eq }

noncomputable def sk172Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8) }

noncomputable def sk172LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (5078793/4194304) }, upper := { exponent := 2, mantissa := (39/32) } }

noncomputable def sk172LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (123/64) }, upper := { exponent := 1, mantissa := (31/16) } }

noncomputable def sk172LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (416450021/333185024) }, upper := { exponent := 0, mantissa := (52/41) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk172LogOuter_valid :
    sk172LogOuterCertificate.check sk172Slice.outerAD.value = true := by
  norm_num [sk172LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk172Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk172LogK_valid :
    sk172LogKCertificate.check sk172Slice.kAD.value = true := by
  norm_num [sk172LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk172Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk172LogDArg_valid :
    sk172LogDArgCertificate.check sk172Slice.dArgAD.value = true := by
  norm_num [sk172LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk172Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk172ValidityFacts : SKFacts sk172Slice
    sk172LogOuterCertificate sk172LogKCertificate
    sk172LogDArgCertificate :=
  { domain := by norm_num [sk172Slice]
    kPositive := by
      norm_num [sk172Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk172LogOuter_valid
    logK := sk172LogK_valid
    logDArg := sk172LogDArg_valid }

noncomputable def sk172RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (413569/262144), upper := (13288563/8388608) }
    logK := { lower := (2823707/2097152), upper := (11362753/8388608) }
    logDArg := { lower := (935617/4194304), upper := (3987469/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk172LogOuterInput_eq :
    sk172RoundedInputs.logOuter = outerEnclosure 24
      (sk172LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk172LogKInput_eq :
    sk172RoundedInputs.logK = outerEnclosure 24
      (sk172LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk172LogDArgInput_eq :
    sk172RoundedInputs.logDArg = outerEnclosure 24
      (sk172LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk172RoundedFacts : SKRoundedFacts 8
    sk172LogOuterCertificate sk172LogKCertificate
    sk172LogDArgCertificate sk172RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk172LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk172LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk172LogDArgInput_eq }

noncomputable def sk173Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32) }

noncomputable def sk173LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (5111559/4194304) }, upper := { exponent := 2, mantissa := (157/128) } }

noncomputable def sk173LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (31/16) }, upper := { exponent := 1, mantissa := (125/64) } }

noncomputable def sk173LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (253526723/203161600) }, upper := { exponent := 0, mantissa := (157/124) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk173LogOuter_valid :
    sk173LogOuterCertificate.check sk173Slice.outerAD.value = true := by
  norm_num [sk173LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk173Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk173LogK_valid :
    sk173LogKCertificate.check sk173Slice.kAD.value = true := by
  norm_num [sk173LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk173Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk173LogDArg_valid :
    sk173LogDArgCertificate.check sk173Slice.dArgAD.value = true := by
  norm_num [sk173LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk173Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk173ValidityFacts : SKFacts sk173Slice
    sk173LogOuterCertificate sk173LogKCertificate
    sk173LogDArgCertificate :=
  { domain := by norm_num [sk173Slice]
    kPositive := by
      norm_num [sk173Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk173LogOuter_valid
    logK := sk173LogK_valid
    logDArg := sk173LogDArg_valid }

noncomputable def sk173RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26576307/16777216), upper := (26684329/16777216) }
    logK := { lower := (22725505/16777216), upper := (2857533/2097152) }
    logDArg := { lower := (464451/2097152), upper := (494853/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk173LogOuterInput_eq :
    sk173RoundedInputs.logOuter = outerEnclosure 24
      (sk173LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk173LogKInput_eq :
    sk173RoundedInputs.logK = outerEnclosure 24
      (sk173LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk173LogDArgInput_eq :
    sk173RoundedInputs.logDArg = outerEnclosure 24
      (sk173LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk173RoundedFacts : SKRoundedFacts 8
    sk173LogOuterCertificate sk173LogKCertificate
    sk173LogDArgCertificate sk173RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk173LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk173LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk173LogDArgInput_eq }

noncomputable def sk174Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16) }

noncomputable def sk174LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (5144325/4194304) }, upper := { exponent := 2, mantissa := (79/64) } }

noncomputable def sk174LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (125/64) }, upper := { exponent := 1, mantissa := (63/32) } }

noncomputable def sk174LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1286048231/1032192000) }, upper := { exponent := 0, mantissa := (158/125) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk174LogOuter_valid :
    sk174LogOuterCertificate.check sk174Slice.outerAD.value = true := by
  norm_num [sk174LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk174Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk174LogK_valid :
    sk174LogKCertificate.check sk174Slice.kAD.value = true := by
  norm_num [sk174LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk174Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk174LogDArg_valid :
    sk174LogDArgCertificate.check sk174Slice.dArgAD.value = true := by
  norm_num [sk174LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk174Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk174ValidityFacts : SKFacts sk174Slice
    sk174LogOuterCertificate sk174LogKCertificate
    sk174LogDArgCertificate :=
  { domain := by norm_num [sk174Slice]
    kPositive := by
      norm_num [sk174Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk174LogOuter_valid
    logK := sk174LogK_valid
    logDArg := sk174LogDArg_valid }

noncomputable def sk174RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26683509/16777216), upper := (6697713/4194304) }
    logK := { lower := (11430131/8388608), upper := (22993947/16777216) }
    logDArg := { lower := (922283/4194304), upper := (982647/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk174LogOuterInput_eq :
    sk174RoundedInputs.logOuter = outerEnclosure 24
      (sk174LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk174LogKInput_eq :
    sk174RoundedInputs.logK = outerEnclosure 24
      (sk174LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk174LogDArgInput_eq :
    sk174RoundedInputs.logDArg = outerEnclosure 24
      (sk174LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk174RoundedFacts : SKRoundedFacts 8
    sk174LogOuterCertificate sk174LogKCertificate
    sk174LogDArgCertificate sk174RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk174LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk174LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk174LogDArgInput_eq }

noncomputable def sk175Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32) }

noncomputable def sk175LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (5177091/4194304) }, upper := { exponent := 2, mantissa := (159/128) } }

noncomputable def sk175LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (63/32) }, upper := { exponent := 1, mantissa := (127/64) } }

noncomputable def sk175LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1141377/917504) }, upper := { exponent := 0, mantissa := (53/42) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk175LogOuter_valid :
    sk175LogOuterCertificate.check sk175Slice.outerAD.value = true := by
  norm_num [sk175LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk175Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk175LogK_valid :
    sk175LogKCertificate.check sk175Slice.kAD.value = true := by
  norm_num [sk175LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk175Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk175LogDArg_valid :
    sk175LogDArgCertificate.check sk175Slice.dArgAD.value = true := by
  norm_num [sk175LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk175Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk175ValidityFacts : SKFacts sk175Slice
    sk175LogOuterCertificate sk175LogKCertificate
    sk175LogDArgCertificate :=
  { domain := by norm_num [sk175Slice]
    kPositive := by
      norm_num [sk175Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk175LogOuter_valid
    logK := sk175LogK_valid
    logDArg := sk175LogDArg_valid }

noncomputable def sk175RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13395015/8388608), upper := (13448351/8388608) }
    logK := { lower := (11496973/8388608), upper := (11563287/8388608) }
    logDArg := { lower := (457879/2097152), upper := (3902755/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk175LogOuterInput_eq :
    sk175RoundedInputs.logOuter = outerEnclosure 24
      (sk175LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk175LogKInput_eq :
    sk175RoundedInputs.logK = outerEnclosure 24
      (sk175LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk175LogDArgInput_eq :
    sk175RoundedInputs.logDArg = outerEnclosure 24
      (sk175LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk175RoundedFacts : SKRoundedFacts 8
    sk175LogOuterCertificate sk175LogKCertificate
    sk175LogDArgCertificate sk175RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk175LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk175LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk175LogDArgInput_eq }

noncomputable def sk176Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4) }

noncomputable def sk176LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (5209857/4194304) }, upper := { exponent := 2, mantissa := (5/4) } }

noncomputable def sk176LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (127/64) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk176LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1323270655/1065353216) }, upper := { exponent := 0, mantissa := (160/127) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk176LogOuter_valid :
    sk176LogOuterCertificate.check sk176Slice.outerAD.value = true := by
  norm_num [sk176LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk176Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk176LogK_valid :
    sk176LogKCertificate.check sk176Slice.kAD.value = true := by
  norm_num [sk176LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk176Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk176LogDArg_valid :
    sk176LogDArgCertificate.check sk176Slice.dArgAD.value = true := by
  norm_num [sk176LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk176Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk176ValidityFacts : SKFacts sk176Slice
    sk176LogOuterCertificate sk176LogKCertificate
    sk176LogDArgCertificate :=
  { domain := by norm_num [sk176Slice]
    kPositive := by
      norm_num [sk176Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk176LogOuter_valid
    logK := sk176LogK_valid
    logDArg := sk176LogDArg_valid }

noncomputable def sk176RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26895879/16777216), upper := (27001889/16777216) }
    logK := { lower := (23126573/16777216), upper := (23258161/16777216) }
    logDArg := { lower := (3637301/16777216), upper := (3875315/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk176LogOuterInput_eq :
    sk176RoundedInputs.logOuter = outerEnclosure 24
      (sk176LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk176LogKInput_eq :
    sk176RoundedInputs.logK = outerEnclosure 24
      (sk176LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk176LogDArgInput_eq :
    sk176RoundedInputs.logDArg = outerEnclosure 24
      (sk176LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk176RoundedFacts : SKRoundedFacts 8
    sk176LogOuterCertificate sk176LogKCertificate
    sk176LogDArgCertificate sk176RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk176LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk176LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk176LogDArgInput_eq }

noncomputable def sk177Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64) }

noncomputable def sk177LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9240139/8388608) }, upper := { exponent := 2, mantissa := (283/256) } }

noncomputable def sk177LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (109/64) }, upper := { exponent := 1, mantissa := (219/128) } }

noncomputable def sk177LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1342889133/1042939904) }, upper := { exponent := 0, mantissa := (283/218) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk177LogOuter_valid :
    sk177LogOuterCertificate.check sk177Slice.outerAD.value = true := by
  norm_num [sk177LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk177Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk177LogK_valid :
    sk177LogKCertificate.check sk177Slice.kAD.value = true := by
  norm_num [sk177LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk177Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk177LogDArg_valid :
    sk177LogDArgCertificate.check sk177Slice.dArgAD.value = true := by
  norm_num [sk177LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk177Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk177ValidityFacts : SKFacts sk177Slice
    sk177LogOuterCertificate sk177LogKCertificate
    sk177LogDArgCertificate :=
  { domain := by norm_num [sk177Slice]
    kPositive := by
      norm_num [sk177Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk177LogOuter_valid
    logK := sk177LogK_valid
    logDArg := sk177LogDArg_valid }

noncomputable def sk177RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6220055/4194304), upper := (24940403/16777216) }
    logK := { lower := (5140589/4194304), upper := (20639141/16777216) }
    logDArg := { lower := (4240941/16777216), upper := (2189023/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk177LogOuterInput_eq :
    sk177RoundedInputs.logOuter = outerEnclosure 24
      (sk177LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk177LogKInput_eq :
    sk177RoundedInputs.logK = outerEnclosure 24
      (sk177LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk177LogDArgInput_eq :
    sk177RoundedInputs.logDArg = outerEnclosure 24
      (sk177LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk177RoundedFacts : SKRoundedFacts 8
    sk177LogOuterCertificate sk177LogKCertificate
    sk177LogDArgCertificate sk177RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk177LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk177LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk177LogDArgInput_eq }

noncomputable def sk178Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16) }

noncomputable def sk178LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9272905/8388608) }, upper := { exponent := 2, mantissa := (71/64) } }

noncomputable def sk178LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (219/128) }, upper := { exponent := 1, mantissa := (55/32) } }

noncomputable def sk178LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1353833061/1052508160) }, upper := { exponent := 0, mantissa := (284/219) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk178LogOuter_valid :
    sk178LogOuterCertificate.check sk178Slice.outerAD.value = true := by
  norm_num [sk178LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk178Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk178LogK_valid :
    sk178LogKCertificate.check sk178Slice.kAD.value = true := by
  norm_num [sk178LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk178Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk178LogDArg_valid :
    sk178LogDArgCertificate.check sk178Slice.dArgAD.value = true := by
  norm_num [sk178LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk178Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk178ValidityFacts : SKFacts sk178Slice
    sk178LogOuterCertificate sk178LogKCertificate
    sk178LogDArgCertificate :=
  { domain := by norm_num [sk178Slice]
    kPositive := by
      norm_num [sk178Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk178LogOuter_valid
    logK := sk178LogK_valid
    logDArg := sk178LogDArg_valid }

noncomputable def sk178RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24939607/16777216), upper := (12499791/8388608) }
    logK := { lower := (5159785/4194304), upper := (20715575/16777216) }
    logDArg := { lower := (527987/2097152), upper := (4360441/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk178LogOuterInput_eq :
    sk178RoundedInputs.logOuter = outerEnclosure 24
      (sk178LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk178LogKInput_eq :
    sk178RoundedInputs.logK = outerEnclosure 24
      (sk178LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk178LogDArgInput_eq :
    sk178RoundedInputs.logDArg = outerEnclosure 24
      (sk178LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk178RoundedFacts : SKRoundedFacts 8
    sk178LogOuterCertificate sk178LogKCertificate
    sk178LogDArgCertificate sk178RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk178LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk178LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk178LogDArgInput_eq }

noncomputable def sk179Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64) }

noncomputable def sk179LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9305671/8388608) }, upper := { exponent := 2, mantissa := (285/256) } }

noncomputable def sk179LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (55/32) }, upper := { exponent := 1, mantissa := (221/128) } }

noncomputable def sk179LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (372223821/289669120) }, upper := { exponent := 0, mantissa := (57/44) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk179LogOuter_valid :
    sk179LogOuterCertificate.check sk179Slice.outerAD.value = true := by
  norm_num [sk179LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk179Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk179LogK_valid :
    sk179LogKCertificate.check sk179Slice.kAD.value = true := by
  norm_num [sk179LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk179Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk179LogDArg_valid :
    sk179LogDArgCertificate.check sk179Slice.dArgAD.value = true := by
  norm_num [sk179LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk179Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk179ValidityFacts : SKFacts sk179Slice
    sk179LogOuterCertificate sk179LogKCertificate
    sk179LogDArgCertificate :=
  { domain := by norm_num [sk179Slice]
    kPositive := by
      norm_num [sk179Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk179LogOuter_valid
    logK := sk179LogK_valid
    logDArg := sk179LogDArg_valid }

noncomputable def sk179RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12499393/8388608), upper := (25058553/16777216) }
    logK := { lower := (10357787/8388608), upper := (20791663/16777216) }
    logDArg := { lower := (1051747/4194304), upper := (2171489/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk179LogOuterInput_eq :
    sk179RoundedInputs.logOuter = outerEnclosure 24
      (sk179LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk179LogKInput_eq :
    sk179RoundedInputs.logK = outerEnclosure 24
      (sk179LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk179LogDArgInput_eq :
    sk179RoundedInputs.logDArg = outerEnclosure 24
      (sk179LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk179RoundedFacts : SKRoundedFacts 8
    sk179LogOuterCertificate sk179LogKCertificate
    sk179LogDArgCertificate sk179RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk179LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk179LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk179LogDArgInput_eq }

noncomputable def sk180Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32) }

noncomputable def sk180LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9338437/8388608) }, upper := { exponent := 2, mantissa := (143/128) } }

noncomputable def sk180LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (221/128) }, upper := { exponent := 1, mantissa := (111/64) } }

noncomputable def sk180LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1375851981/1071775744) }, upper := { exponent := 0, mantissa := (22/17) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk180LogOuter_valid :
    sk180LogOuterCertificate.check sk180Slice.outerAD.value = true := by
  norm_num [sk180LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk180Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk180LogK_valid :
    sk180LogKCertificate.check sk180Slice.kAD.value = true := by
  norm_num [sk180LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk180Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk180LogDArg_valid :
    sk180LogDArgCertificate.check sk180Slice.dArgAD.value = true := by
  norm_num [sk180LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk180Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk180ValidityFacts : SKFacts sk180Slice
    sk180LogOuterCertificate sk180LogKCertificate
    sk180LogDArgCertificate :=
  { domain := by norm_num [sk180Slice]
    kPositive := by
      norm_num [sk180Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk180LogOuter_valid
    logK := sk180LogK_valid
    logDArg := sk180LogDArg_valid }

noncomputable def sk180RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6264439/4194304), upper := (12558659/8388608) }
    logK := { lower := (20791661/16777216), upper := (10433703/8388608) }
    logDArg := { lower := (4190215/16777216), upper := (4325655/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk180LogOuterInput_eq :
    sk180RoundedInputs.logOuter = outerEnclosure 24
      (sk180LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk180LogKInput_eq :
    sk180RoundedInputs.logK = outerEnclosure 24
      (sk180LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk180LogDArgInput_eq :
    sk180RoundedInputs.logDArg = outerEnclosure 24
      (sk180LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk180RoundedFacts : SKRoundedFacts 8
    sk180LogOuterCertificate sk180LogKCertificate
    sk180LogDArgCertificate sk180RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk180LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk180LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk180LogDArgInput_eq }

noncomputable def sk181Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64) }

noncomputable def sk181LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9371203/8388608) }, upper := { exponent := 2, mantissa := (287/256) } }

noncomputable def sk181LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (111/64) }, upper := { exponent := 1, mantissa := (223/128) } }

noncomputable def sk181LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1386926973/1081475072) }, upper := { exponent := 0, mantissa := (287/222) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk181LogOuter_valid :
    sk181LogOuterCertificate.check sk181Slice.outerAD.value = true := by
  norm_num [sk181LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk181Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk181LogK_valid :
    sk181LogKCertificate.check sk181Slice.kAD.value = true := by
  norm_num [sk181LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk181Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk181LogDArg_valid :
    sk181LogDArgCertificate.check sk181Slice.dArgAD.value = true := by
  norm_num [sk181LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk181Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk181ValidityFacts : SKFacts sk181Slice
    sk181LogOuterCertificate sk181LogKCertificate
    sk181LogDArgCertificate :=
  { domain := by norm_num [sk181Slice]
    kPositive := by
      norm_num [sk181Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk181LogOuter_valid
    logK := sk181LogK_valid
    logDArg := sk181LogDArg_valid }

noncomputable def sk181RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25116519/16777216), upper := (25175877/16777216) }
    logK := { lower := (20867405/16777216), upper := (10471405/8388608) }
    logDArg := { lower := (521697/2097152), upper := (4308471/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk181LogOuterInput_eq :
    sk181RoundedInputs.logOuter = outerEnclosure 24
      (sk181LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk181LogKInput_eq :
    sk181RoundedInputs.logK = outerEnclosure 24
      (sk181LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk181LogDArgInput_eq :
    sk181RoundedInputs.logDArg = outerEnclosure 24
      (sk181LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk181RoundedFacts : SKRoundedFacts 8
    sk181LogOuterCertificate sk181LogKCertificate
    sk181LogDArgCertificate sk181RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk181LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk181LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk181LogDArgInput_eq }

noncomputable def sk182Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2) }

noncomputable def sk182LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9403969/8388608) }, upper := { exponent := 2, mantissa := (9/8) } }

noncomputable def sk182LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (223/128) }, upper := { exponent := 1, mantissa := (7/4) } }

noncomputable def sk182LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4194136959/3273654272) }, upper := { exponent := 0, mantissa := (288/223) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk182LogOuter_valid :
    sk182LogOuterCertificate.check sk182Slice.outerAD.value = true := by
  norm_num [sk182LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk182Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk182LogK_valid :
    sk182LogKCertificate.check sk182Slice.kAD.value = true := by
  norm_num [sk182LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk182Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk182LogDArg_valid :
    sk182LogDArgCertificate.check sk182Slice.dArgAD.value = true := by
  norm_num [sk182LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk182Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk182ValidityFacts : SKFacts sk182Slice
    sk182LogOuterCertificate sk182LogKCertificate
    sk182LogDArgCertificate :=
  { domain := by norm_num [sk182Slice]
    kPositive := by
      norm_num [sk182Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk182LogOuter_valid
    logK := sk182LogK_valid
    logDArg := sk182LogDArg_valid }

noncomputable def sk182RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12587539/8388608), upper := (3154279/2097152) }
    logK := { lower := (2617851/2097152), upper := (5254469/4194304) }
    logDArg := { lower := (2078535/8388608), upper := (4291423/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk182LogOuterInput_eq :
    sk182RoundedInputs.logOuter = outerEnclosure 24
      (sk182LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk182LogKInput_eq :
    sk182RoundedInputs.logK = outerEnclosure 24
      (sk182LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk182LogDArgInput_eq :
    sk182RoundedInputs.logDArg = outerEnclosure 24
      (sk182LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk182RoundedFacts : SKRoundedFacts 8
    sk182LogOuterCertificate sk182LogKCertificate
    sk182LogDArgCertificate sk182RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk182LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk182LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk182LogDArgInput_eq }

noncomputable def sk183Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64) }

noncomputable def sk183LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9174607/8388608) }, upper := { exponent := 2, mantissa := (281/256) } }

noncomputable def sk183LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (27/16) }, upper := { exponent := 1, mantissa := (217/128) } }

noncomputable def sk183LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (440377447/341311488) }, upper := { exponent := 0, mantissa := (281/216) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk183LogOuter_valid :
    sk183LogOuterCertificate.check sk183Slice.outerAD.value = true := by
  norm_num [sk183LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk183Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk183LogK_valid :
    sk183LogKCertificate.check sk183Slice.kAD.value = true := by
  norm_num [sk183LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk183Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk183LogDArg_valid :
    sk183LogDArgCertificate.check sk183Slice.dArgAD.value = true := by
  norm_num [sk183LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk183Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk183ValidityFacts : SKFacts sk183Slice
    sk183LogOuterCertificate sk183LogKCertificate
    sk183LogDArgCertificate :=
  { domain := by norm_num [sk183Slice]
    kPositive := by
      norm_num [sk183Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk183LogOuter_valid
    logK := sk183LogK_valid
    logDArg := sk183LogDArg_valid }

noncomputable def sk183RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12380405/8388608), upper := (24821415/16777216) }
    logK := { lower := (20407727/16777216), upper := (20485221/16777216) }
    logDArg := { lower := (4275449/16777216), upper := (551711/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk183LogOuterInput_eq :
    sk183RoundedInputs.logOuter = outerEnclosure 24
      (sk183LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk183LogKInput_eq :
    sk183RoundedInputs.logK = outerEnclosure 24
      (sk183LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk183LogDArgInput_eq :
    sk183RoundedInputs.logDArg = outerEnclosure 24
      (sk183LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk183RoundedFacts : SKRoundedFacts 8
    sk183LogOuterCertificate sk183LogKCertificate
    sk183LogDArgCertificate sk183RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk183LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk183LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk183LogDArgInput_eq }

noncomputable def sk184Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32) }

noncomputable def sk184LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9207373/8388608) }, upper := { exponent := 2, mantissa := (141/128) } }

noncomputable def sk184LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (217/128) }, upper := { exponent := 1, mantissa := (109/64) } }

noncomputable def sk184LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3995966679/3100246016) }, upper := { exponent := 0, mantissa := (282/217) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk184LogOuter_valid :
    sk184LogOuterCertificate.check sk184Slice.outerAD.value = true := by
  norm_num [sk184LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk184Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk184LogK_valid :
    sk184LogKCertificate.check sk184Slice.kAD.value = true := by
  norm_num [sk184LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk184Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk184LogDArg_valid :
    sk184LogDArgCertificate.check sk184Slice.dArgAD.value = true := by
  norm_num [sk184LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk184Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk184ValidityFacts : SKFacts sk184Slice
    sk184LogOuterCertificate sk184LogKCertificate
    sk184LogDArgCertificate :=
  { domain := by norm_num [sk184Slice]
    kPositive := by
      norm_num [sk184Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk184LogOuter_valid
    logK := sk184LogK_valid
    logDArg := sk184LogDArg_valid }

noncomputable def sk184RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24820621/16777216), upper := (24881015/16777216) }
    logK := { lower := (5121305/4194304), upper := (10281179/8388608) }
    logDArg := { lower := (4258125/16777216), upper := (2197897/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk184LogOuterInput_eq :
    sk184RoundedInputs.logOuter = outerEnclosure 24
      (sk184LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk184LogKInput_eq :
    sk184RoundedInputs.logK = outerEnclosure 24
      (sk184LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk184LogDArgInput_eq :
    sk184RoundedInputs.logDArg = outerEnclosure 24
      (sk184LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk184RoundedFacts : SKRoundedFacts 8
    sk184LogOuterCertificate sk184LogKCertificate
    sk184LogDArgCertificate sk184RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk184LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk184LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk184LogDArgInput_eq }

noncomputable def sk185Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (193/64) }

noncomputable def sk185LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (8388223/4194304) }, upper := { exponent := 2, mantissa := (257/256) } }

noncomputable def sk185LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3/2) }, upper := { exponent := 1, mantissa := (193/128) } }

noncomputable def sk185LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1073681493/809500672) }, upper := { exponent := 0, mantissa := (257/192) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk185LogOuter_valid :
    sk185LogOuterCertificate.check sk185Slice.outerAD.value = true := by
  norm_num [sk185LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk185Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk185LogK_valid :
    sk185LogKCertificate.check sk185Slice.kAD.value = true := by
  norm_num [sk185LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk185Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk185LogDArg_valid :
    sk185LogDArgCertificate.check sk185Slice.dArgAD.value = true := by
  norm_num [sk185LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk185Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk185ValidityFacts : SKFacts sk185Slice
    sk185LogOuterCertificate sk185LogKCertificate
    sk185LogDArgCertificate :=
  { domain := by norm_num [sk185Slice]
    kPositive := by
      norm_num [sk185Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk185LogOuter_valid
    logK := sk185LogK_valid
    logDArg := sk185LogDArg_valid }

noncomputable def sk185RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23257389/16777216), upper := (23323569/16777216) }
    logK := { lower := (18431655/16777216), upper := (18518811/16777216) }
    logDArg := { lower := (4738407/16777216), upper := (4891913/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk185LogOuterInput_eq :
    sk185RoundedInputs.logOuter = outerEnclosure 24
      (sk185LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk185LogKInput_eq :
    sk185RoundedInputs.logK = outerEnclosure 24
      (sk185LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk185LogDArgInput_eq :
    sk185RoundedInputs.logDArg = outerEnclosure 24
      (sk185LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk185RoundedFacts : SKRoundedFacts 8
    sk185LogOuterCertificate sk185LogKCertificate
    sk185LogDArgCertificate sk185RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk185LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk185LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk185LogDArgInput_eq }

noncomputable def sk186Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (193/64), kHi := (97/32) }

noncomputable def sk186LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8420989/8388608) }, upper := { exponent := 2, mantissa := (129/128) } }

noncomputable def sk186LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (193/128) }, upper := { exponent := 1, mantissa := (97/64) } }

noncomputable def sk186LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3250468599/2453798912) }, upper := { exponent := 0, mantissa := (258/193) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk186LogOuter_valid :
    sk186LogOuterCertificate.check sk186Slice.outerAD.value = true := by
  norm_num [sk186LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk186Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk186LogK_valid :
    sk186LogKCertificate.check sk186Slice.kAD.value = true := by
  norm_num [sk186LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk186Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk186LogDArg_valid :
    sk186LogDArgCertificate.check sk186Slice.dArgAD.value = true := by
  norm_num [sk186LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk186Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk186ValidityFacts : SKFacts sk186Slice
    sk186LogOuterCertificate sk186LogKCertificate
    sk186LogDArgCertificate :=
  { domain := by norm_num [sk186Slice]
    kPositive := by
      norm_num [sk186Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk186LogOuter_valid
    logK := sk186LogK_valid
    logDArg := sk186LogDArg_valid }

noncomputable def sk186RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23322797/16777216), upper := (5847181/4194304) }
    logK := { lower := (9259405/8388608), upper := (18605515/16777216) }
    logDArg := { lower := (4717111/16777216), upper := (4869913/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk186LogOuterInput_eq :
    sk186RoundedInputs.logOuter = outerEnclosure 24
      (sk186LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk186LogKInput_eq :
    sk186RoundedInputs.logK = outerEnclosure 24
      (sk186LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk186LogDArgInput_eq :
    sk186RoundedInputs.logDArg = outerEnclosure 24
      (sk186LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk186RoundedFacts : SKRoundedFacts 8
    sk186LogOuterCertificate sk186LogKCertificate
    sk186LogDArgCertificate sk186RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk186LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk186LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk186LogDArgInput_eq }

noncomputable def sk187Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (97/32), kHi := (195/64) }

noncomputable def sk187LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8453755/8388608) }, upper := { exponent := 2, mantissa := (259/256) } }

noncomputable def sk187LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (97/64) }, upper := { exponent := 1, mantissa := (195/128) } }

noncomputable def sk187LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1093341261/826408960) }, upper := { exponent := 0, mantissa := (259/194) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk187LogOuter_valid :
    sk187LogOuterCertificate.check sk187Slice.outerAD.value = true := by
  norm_num [sk187LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk187Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk187LogK_valid :
    sk187LogKCertificate.check sk187Slice.kAD.value = true := by
  norm_num [sk187LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk187Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk187LogDArg_valid :
    sk187LogDArgCertificate.check sk187Slice.dArgAD.value = true := by
  norm_num [sk187LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk187Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk187ValidityFacts : SKFacts sk187Slice
    sk187LogOuterCertificate sk187LogKCertificate
    sk187LogDArgCertificate :=
  { domain := by norm_num [sk187Slice]
    kPositive := by
      norm_num [sk187Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk187LogOuter_valid
    logK := sk187LogK_valid
    logDArg := sk187LogDArg_valid }

noncomputable def sk187RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11693975/8388608), upper := (11726813/8388608) }
    logK := { lower := (9302757/8388608), upper := (9345887/8388608) }
    logDArg := { lower := (587001/2097152), upper := (4848111/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk187LogOuterInput_eq :
    sk187RoundedInputs.logOuter = outerEnclosure 24
      (sk187LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk187LogKInput_eq :
    sk187RoundedInputs.logK = outerEnclosure 24
      (sk187LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk187LogDArgInput_eq :
    sk187RoundedInputs.logDArg = outerEnclosure 24
      (sk187LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk187RoundedFacts : SKRoundedFacts 8
    sk187LogOuterCertificate sk187LogKCertificate
    sk187LogDArgCertificate sk187RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk187LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk187LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk187LogDArgInput_eq }

noncomputable def sk188Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (195/64), kHi := (49/16) }

noncomputable def sk188LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8486521/8388608) }, upper := { exponent := 2, mantissa := (65/64) } }

noncomputable def sk188LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (195/128) }, upper := { exponent := 1, mantissa := (49/32) } }

noncomputable def sk188LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1103236677/834928640) }, upper := { exponent := 0, mantissa := (4/3) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk188LogOuter_valid :
    sk188LogOuterCertificate.check sk188Slice.outerAD.value = true := by
  norm_num [sk188LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk188Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk188LogK_valid :
    sk188LogKCertificate.check sk188Slice.kAD.value = true := by
  norm_num [sk188LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk188Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk188LogDArg_valid :
    sk188LogDArgCertificate.check sk188Slice.dArgAD.value = true := by
  norm_num [sk188LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk188Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk188ValidityFacts : SKFacts sk188Slice
    sk188LogOuterCertificate sk188LogKCertificate
    sk188LogDArgCertificate :=
  { domain := by norm_num [sk188Slice]
    kPositive := by
      norm_num [sk188Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk188LogOuter_valid
    logK := sk188LogK_valid
    logDArg := sk188LogDArg_valid }

noncomputable def sk188RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23452851/16777216), upper := (11759139/8388608) }
    logK := { lower := (4672943/4194304), upper := (18777591/16777216) }
    logDArg := { lower := (4675093/16777216), upper := (4826505/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk188LogOuterInput_eq :
    sk188RoundedInputs.logOuter = outerEnclosure 24
      (sk188LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk188LogKInput_eq :
    sk188RoundedInputs.logK = outerEnclosure 24
      (sk188LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk188LogDArgInput_eq :
    sk188RoundedInputs.logDArg = outerEnclosure 24
      (sk188LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk188RoundedFacts : SKRoundedFacts 8
    sk188LogOuterCertificate sk188LogKCertificate
    sk188LogDArgCertificate sk188RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk188LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk188LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk188LogDArgInput_eq }

noncomputable def sk189Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (197/64) }

noncomputable def sk189LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8519287/8388608) }, upper := { exponent := 2, mantissa := (261/256) } }

noncomputable def sk189LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (49/32) }, upper := { exponent := 1, mantissa := (197/128) } }

noncomputable def sk189LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3339527343/2530476032) }, upper := { exponent := 0, mantissa := (261/196) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk189LogOuter_valid :
    sk189LogOuterCertificate.check sk189Slice.outerAD.value = true := by
  norm_num [sk189LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk189Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk189LogK_valid :
    sk189LogKCertificate.check sk189Slice.kAD.value = true := by
  norm_num [sk189LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk189Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk189LogDArg_valid :
    sk189LogDArgCertificate.check sk189Slice.dArgAD.value = true := by
  norm_num [sk189LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk189Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk189ValidityFacts : SKFacts sk189Slice
    sk189LogOuterCertificate sk189LogKCertificate
    sk189LogDArgCertificate :=
  { domain := by norm_num [sk189Slice]
    kPositive := by
      norm_num [sk189Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk189LogOuter_valid
    logK := sk189LogK_valid
    logDArg := sk189LogDArg_valid }

noncomputable def sk189RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23517503/16777216), upper := (11791341/8388608) }
    logK := { lower := (18777589/16777216), upper := (18862971/16777216) }
    logDArg := { lower := (2327183/8388608), upper := (1201273/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk189LogOuterInput_eq :
    sk189RoundedInputs.logOuter = outerEnclosure 24
      (sk189LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk189LogKInput_eq :
    sk189RoundedInputs.logK = outerEnclosure 24
      (sk189LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk189LogDArgInput_eq :
    sk189RoundedInputs.logDArg = outerEnclosure 24
      (sk189LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk189RoundedFacts : SKRoundedFacts 8
    sk189LogOuterCertificate sk189LogKCertificate
    sk189LogDArgCertificate sk189RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk189LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk189LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk189LogDArgInput_eq }

noncomputable def sk190Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (197/64), kHi := (99/32) }

noncomputable def sk190LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8552053/8388608) }, upper := { exponent := 2, mantissa := (131/128) } }

noncomputable def sk190LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (197/128) }, upper := { exponent := 1, mantissa := (99/64) } }

noncomputable def sk190LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (374386191/284033024) }, upper := { exponent := 0, mantissa := (262/197) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk190LogOuter_valid :
    sk190LogOuterCertificate.check sk190Slice.outerAD.value = true := by
  norm_num [sk190LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk190Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk190LogK_valid :
    sk190LogKCertificate.check sk190Slice.kAD.value = true := by
  norm_num [sk190LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk190Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk190LogDArg_valid :
    sk190LogDArgCertificate.check sk190Slice.dArgAD.value = true := by
  norm_num [sk190LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk190Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk190ValidityFacts : SKFacts sk190Slice
    sk190LogOuterCertificate sk190LogKCertificate
    sk190LogDArgCertificate :=
  { domain := by norm_num [sk190Slice]
    kPositive := by
      norm_num [sk190Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk190LogOuter_valid
    logK := sk190LogK_valid
    logDArg := sk190LogDArg_valid }

noncomputable def sk190RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11790953/8388608), upper := (2955855/2097152) }
    logK := { lower := (9431485/8388608), upper := (18947919/16777216) }
    logDArg := { lower := (2316911/8388608), upper := (4783869/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk190LogOuterInput_eq :
    sk190RoundedInputs.logOuter = outerEnclosure 24
      (sk190LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk190LogKInput_eq :
    sk190RoundedInputs.logK = outerEnclosure 24
      (sk190LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk190LogDArgInput_eq :
    sk190RoundedInputs.logDArg = outerEnclosure 24
      (sk190LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk190RoundedFacts : SKRoundedFacts 8
    sk190LogOuterCertificate sk190LogKCertificate
    sk190LogDArgCertificate sk190RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk190LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk190LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk190LogDArgInput_eq }

noncomputable def sk191Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (199/64) }

noncomputable def sk191LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8584819/8388608) }, upper := { exponent := 2, mantissa := (263/256) } }

noncomputable def sk191LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (99/64) }, upper := { exponent := 1, mantissa := (199/128) } }

noncomputable def sk191LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (34338941/26083328) }, upper := { exponent := 0, mantissa := (263/198) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk191LogOuter_valid :
    sk191LogOuterCertificate.check sk191Slice.outerAD.value = true := by
  norm_num [sk191LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk191Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk191LogK_valid :
    sk191LogKCertificate.check sk191Slice.kAD.value = true := by
  norm_num [sk191LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk191Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk191LogDArg_valid :
    sk191LogDArgCertificate.check sk191Slice.dArgAD.value = true := by
  norm_num [sk191LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk191Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk191ValidityFacts : SKFacts sk191Slice
    sk191LogOuterCertificate sk191LogKCertificate
    sk191LogDArgCertificate :=
  { domain := by norm_num [sk191Slice]
    kPositive := by
      norm_num [sk191Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk191LogOuter_valid
    logK := sk191LogK_valid
    logDArg := sk191LogDArg_valid }

noncomputable def sk191RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11823031/8388608), upper := (23710753/16777216) }
    logK := { lower := (9473959/8388608), upper := (19032439/16777216) }
    logDArg := { lower := (1153365/4194304), upper := (2381417/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk191LogOuterInput_eq :
    sk191RoundedInputs.logOuter = outerEnclosure 24
      (sk191LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk191LogKInput_eq :
    sk191RoundedInputs.logK = outerEnclosure 24
      (sk191LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk191LogDArgInput_eq :
    sk191RoundedInputs.logDArg = outerEnclosure 24
      (sk191LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk191RoundedFacts : SKRoundedFacts 8
    sk191LogOuterCertificate sk191LogKCertificate
    sk191LogDArgCertificate sk191RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk191LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk191LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk191LogDArgInput_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
