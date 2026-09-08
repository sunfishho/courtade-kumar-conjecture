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

noncomputable def sk192Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (199/64), kHi := (25/8) }

noncomputable def sk192LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8617585/8388608) }, upper := { exponent := 2, mantissa := (33/32) } }

noncomputable def sk192LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (199/128) }, upper := { exponent := 1, mantissa := (25/16) } }

noncomputable def sk192LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3429765663/2608332800) }, upper := { exponent := 0, mantissa := (264/199) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk192LogOuter_valid :
    sk192LogOuterCertificate.check sk192Slice.outerAD.value = true := by
  norm_num [sk192LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk192Slice,
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
private theorem sk192LogK_valid :
    sk192LogKCertificate.check sk192Slice.kAD.value = true := by
  norm_num [sk192LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk192Slice,
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
private theorem sk192LogDArg_valid :
    sk192LogDArgCertificate.check sk192Slice.dArgAD.value = true := by
  norm_num [sk192LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk192Slice,
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

theorem sk192ValidityFacts : SKFacts sk192Slice
    sk192LogOuterCertificate sk192LogKCertificate
    sk192LogDArgCertificate :=
  { domain := by norm_num [sk192Slice]
    kPositive := by
      norm_num [sk192Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk192LogOuter_valid
    logK := sk192LogK_valid
    logDArg := sk192LogDArg_valid }

noncomputable def sk192RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23709975/16777216), upper := (2971803/2097152) }
    logK := { lower := (9516219/8388608), upper := (2389567/2097152) }
    logDArg := { lower := (4593277/16777216), upper := (4741985/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk192LogOuterInput_eq :
    sk192RoundedInputs.logOuter = outerEnclosure 24
      (sk192LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk192LogKInput_eq :
    sk192RoundedInputs.logK = outerEnclosure 24
      (sk192LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk192LogDArgInput_eq :
    sk192RoundedInputs.logDArg = outerEnclosure 24
      (sk192LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk192RoundedFacts : SKRoundedFacts 8
    sk192LogOuterCertificate sk192LogKCertificate
    sk192LogDArgCertificate sk192RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk192LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk192LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk192LogDArgInput_eq }

noncomputable def sk193Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (201/64) }

noncomputable def sk193LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8650351/8388608) }, upper := { exponent := 2, mantissa := (265/256) } }

noncomputable def sk193LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (25/16) }, upper := { exponent := 1, mantissa := (201/128) } }

noncomputable def sk193LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1153369077/878182400) }, upper := { exponent := 0, mantissa := (53/40) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk193LogOuter_valid :
    sk193LogOuterCertificate.check sk193Slice.outerAD.value = true := by
  norm_num [sk193LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk193Slice,
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
private theorem sk193LogK_valid :
    sk193LogKCertificate.check sk193Slice.kAD.value = true := by
  norm_num [sk193LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk193Slice,
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
private theorem sk193LogDArg_valid :
    sk193LogDArgCertificate.check sk193Slice.dArgAD.value = true := by
  norm_num [sk193LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk193Slice,
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

theorem sk193ValidityFacts : SKFacts sk193Slice
    sk193LogOuterCertificate sk193LogKCertificate
    sk193LogDArgCertificate :=
  { domain := by norm_num [sk193Slice]
    kPositive := by
      norm_num [sk193Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk193LogOuter_valid
    logK := sk193LogK_valid
    logDArg := sk193LogDArg_valid }

noncomputable def sk193RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5943411/4194304), upper := (11918927/8388608) }
    logK := { lower := (19116535/16777216), upper := (19200213/16777216) }
    logDArg := { lower := (571659/2097152), upper := (2360659/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk193LogOuterInput_eq :
    sk193RoundedInputs.logOuter = outerEnclosure 24
      (sk193LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk193LogKInput_eq :
    sk193RoundedInputs.logK = outerEnclosure 24
      (sk193LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk193LogDArgInput_eq :
    sk193RoundedInputs.logDArg = outerEnclosure 24
      (sk193LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk193RoundedFacts : SKRoundedFacts 8
    sk193LogOuterCertificate sk193LogKCertificate
    sk193LogDArgCertificate sk193RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk193LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk193LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk193LogDArgInput_eq }

noncomputable def sk194Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (201/64), kHi := (101/32) }

noncomputable def sk194LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8683117/8388608) }, upper := { exponent := 2, mantissa := (133/128) } }

noncomputable def sk194LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (201/128) }, upper := { exponent := 1, mantissa := (101/64) } }

noncomputable def sk194LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1163526621/886964224) }, upper := { exponent := 0, mantissa := (266/201) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk194LogOuter_valid :
    sk194LogOuterCertificate.check sk194Slice.outerAD.value = true := by
  norm_num [sk194LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk194Slice,
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
private theorem sk194LogK_valid :
    sk194LogKCertificate.check sk194Slice.kAD.value = true := by
  norm_num [sk194LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk194Slice,
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
private theorem sk194LogDArg_valid :
    sk194LogDArgCertificate.check sk194Slice.dArgAD.value = true := by
  norm_num [sk194LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk194Slice,
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

theorem sk194ValidityFacts : SKFacts sk194Slice
    sk194LogOuterCertificate sk194LogKCertificate
    sk194LogDArgCertificate :=
  { domain := by norm_num [sk194Slice]
    kPositive := by
      norm_num [sk194Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk194LogOuter_valid
    logK := sk194LogK_valid
    logDArg := sk194LogDArg_valid }

noncomputable def sk194RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11918537/8388608), upper := (23901045/16777216) }
    logK := { lower := (4800053/4194304), upper := (19283475/16777216) }
    logDArg := { lower := (142295/524288), upper := (146901/524288) } }

set_option maxRecDepth 1000000 in
private theorem sk194LogOuterInput_eq :
    sk194RoundedInputs.logOuter = outerEnclosure 24
      (sk194LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk194LogKInput_eq :
    sk194RoundedInputs.logK = outerEnclosure 24
      (sk194LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk194LogDArgInput_eq :
    sk194RoundedInputs.logDArg = outerEnclosure 24
      (sk194LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk194RoundedFacts : SKRoundedFacts 8
    sk194LogOuterCertificate sk194LogKCertificate
    sk194LogDArgCertificate sk194RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk194LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk194LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk194LogDArgInput_eq }

noncomputable def sk195Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (203/64) }

noncomputable def sk195LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8715883/8388608) }, upper := { exponent := 2, mantissa := (267/256) } }

noncomputable def sk195LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (101/64) }, upper := { exponent := 1, mantissa := (203/128) } }

noncomputable def sk195LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3521183559/2687369216) }, upper := { exponent := 0, mantissa := (267/202) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk195LogOuter_valid :
    sk195LogOuterCertificate.check sk195Slice.outerAD.value = true := by
  norm_num [sk195LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk195Slice,
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
private theorem sk195LogK_valid :
    sk195LogKCertificate.check sk195Slice.kAD.value = true := by
  norm_num [sk195LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk195Slice,
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
private theorem sk195LogDArg_valid :
    sk195LogDArgCertificate.check sk195Slice.dArgAD.value = true := by
  norm_num [sk195LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk195Slice,
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

theorem sk195ValidityFacts : SKFacts sk195Slice
    sk195LogOuterCertificate sk195LogKCertificate
    sk195LogDArgCertificate :=
  { domain := by norm_num [sk195Slice]
    kPositive := by
      norm_num [sk195Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk195LogOuter_valid
    logK := sk195LogK_valid
    logDArg := sk195LogDArg_valid }

noncomputable def sk195RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2987533/2097152), upper := (23963999/16777216) }
    logK := { lower := (19283473/16777216), upper := (19366325/16777216) }
    logDArg := { lower := (4533781/16777216), upper := (1170131/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk195LogOuterInput_eq :
    sk195RoundedInputs.logOuter = outerEnclosure 24
      (sk195LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk195LogKInput_eq :
    sk195RoundedInputs.logK = outerEnclosure 24
      (sk195LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk195LogDArgInput_eq :
    sk195RoundedInputs.logDArg = outerEnclosure 24
      (sk195LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk195RoundedFacts : SKRoundedFacts 8
    sk195LogOuterCertificate sk195LogKCertificate
    sk195LogDArgCertificate sk195RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk195LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk195LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk195LogDArgInput_eq }

noncomputable def sk196Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (203/64), kHi := (51/16) }

noncomputable def sk196LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8748649/8388608) }, upper := { exponent := 2, mantissa := (67/64) } }

noncomputable def sk196LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (203/128) }, upper := { exponent := 1, mantissa := (51/32) } }

noncomputable def sk196LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1183972773/904658944) }, upper := { exponent := 0, mantissa := (268/203) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk196LogOuter_valid :
    sk196LogOuterCertificate.check sk196Slice.outerAD.value = true := by
  norm_num [sk196LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk196Slice,
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
private theorem sk196LogK_valid :
    sk196LogKCertificate.check sk196Slice.kAD.value = true := by
  norm_num [sk196LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk196Slice,
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
private theorem sk196LogDArg_valid :
    sk196LogDArgCertificate.check sk196Slice.dArgAD.value = true := by
  norm_num [sk196LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk196Slice,
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

theorem sk196ValidityFacts : SKFacts sk196Slice
    sk196LogOuterCertificate sk196LogKCertificate
    sk196LogDArgCertificate :=
  { domain := by norm_num [sk196Slice]
    kPositive := by
      norm_num [sk196Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk196LogOuter_valid
    logK := sk196LogK_valid
    logDArg := sk196LogDArg_valid }

noncomputable def sk196RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23963217/16777216), upper := (24026717/16777216) }
    logK := { lower := (4841581/4194304), upper := (19448769/16777216) }
    logDArg := { lower := (1128573/4194304), upper := (582549/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk196LogOuterInput_eq :
    sk196RoundedInputs.logOuter = outerEnclosure 24
      (sk196LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk196LogKInput_eq :
    sk196RoundedInputs.logK = outerEnclosure 24
      (sk196LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk196LogDArgInput_eq :
    sk196RoundedInputs.logDArg = outerEnclosure 24
      (sk196LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk196RoundedFacts : SKRoundedFacts 8
    sk196LogOuterCertificate sk196LogKCertificate
    sk196LogDArgCertificate sk196RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk196LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk196LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk196LogDArgInput_eq }

noncomputable def sk197Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (205/64) }

noncomputable def sk197LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8781415/8388608) }, upper := { exponent := 2, mantissa := (269/256) } }

noncomputable def sk197LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (51/32) }, upper := { exponent := 1, mantissa := (205/128) } }

noncomputable def sk197LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1194261381/913571840) }, upper := { exponent := 0, mantissa := (269/204) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk197LogOuter_valid :
    sk197LogOuterCertificate.check sk197Slice.outerAD.value = true := by
  norm_num [sk197LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk197Slice,
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
private theorem sk197LogK_valid :
    sk197LogKCertificate.check sk197Slice.kAD.value = true := by
  norm_num [sk197LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk197Slice,
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
private theorem sk197LogDArg_valid :
    sk197LogDArgCertificate.check sk197Slice.dArgAD.value = true := by
  norm_num [sk197LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk197Slice,
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

theorem sk197ValidityFacts : SKFacts sk197Slice
    sk197LogOuterCertificate sk197LogKCertificate
    sk197LogDArgCertificate :=
  { domain := by norm_num [sk197Slice]
    kPositive := by
      norm_num [sk197Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk197LogOuter_valid
    logK := sk197LogK_valid
    logDArg := sk197LogDArg_valid }

noncomputable def sk197RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12012967/8388608), upper := (24089203/16777216) }
    logK := { lower := (303887/262144), upper := (19530809/16777216) }
    logDArg := { lower := (4494971/16777216), upper := (2320217/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk197LogOuterInput_eq :
    sk197RoundedInputs.logOuter = outerEnclosure 24
      (sk197LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk197LogKInput_eq :
    sk197RoundedInputs.logK = outerEnclosure 24
      (sk197LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk197LogDArgInput_eq :
    sk197RoundedInputs.logDArg = outerEnclosure 24
      (sk197LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk197RoundedFacts : SKRoundedFacts 8
    sk197LogOuterCertificate sk197LogKCertificate
    sk197LogDArgCertificate sk197RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk197LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk197LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk197LogDArgInput_eq }

noncomputable def sk198Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (205/64), kHi := (103/32) }

noncomputable def sk198LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8814181/8388608) }, upper := { exponent := 2, mantissa := (135/128) } }

noncomputable def sk198LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (205/128) }, upper := { exponent := 1, mantissa := (103/64) } }

noncomputable def sk198LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3613781031/2767585280) }, upper := { exponent := 0, mantissa := (54/41) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk198LogOuter_valid :
    sk198LogOuterCertificate.check sk198Slice.outerAD.value = true := by
  norm_num [sk198LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk198Slice,
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
private theorem sk198LogK_valid :
    sk198LogKCertificate.check sk198Slice.kAD.value = true := by
  norm_num [sk198LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk198Slice,
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
private theorem sk198LogDArg_valid :
    sk198LogDArgCertificate.check sk198Slice.dArgAD.value = true := by
  norm_num [sk198LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk198Slice,
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

theorem sk198ValidityFacts : SKFacts sk198Slice
    sk198LogOuterCertificate sk198LogKCertificate
    sk198LogDArgCertificate :=
  { domain := by norm_num [sk198Slice]
    kPositive := by
      norm_num [sk198Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk198LogOuter_valid
    logK := sk198LogK_valid
    logDArg := sk198LogDArg_valid }

noncomputable def sk198RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24088419/16777216), upper := (754733/524288) }
    logK := { lower := (2441351/2097152), upper := (9806225/8388608) }
    logDArg := { lower := (4475815/16777216), upper := (4620647/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk198LogOuterInput_eq :
    sk198RoundedInputs.logOuter = outerEnclosure 24
      (sk198LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk198LogKInput_eq :
    sk198RoundedInputs.logK = outerEnclosure 24
      (sk198LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk198LogDArgInput_eq :
    sk198RoundedInputs.logDArg = outerEnclosure 24
      (sk198LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk198RoundedFacts : SKRoundedFacts 8
    sk198LogOuterCertificate sk198LogKCertificate
    sk198LogDArgCertificate sk198RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk198LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk198LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk198LogDArgInput_eq }

noncomputable def sk199Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (207/64) }

noncomputable def sk199LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8846947/8388608) }, upper := { exponent := 2, mantissa := (271/256) } }

noncomputable def sk199LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (103/64) }, upper := { exponent := 1, mantissa := (207/128) } }

noncomputable def sk199LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (404989887/310509568) }, upper := { exponent := 0, mantissa := (271/206) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk199LogOuter_valid :
    sk199LogOuterCertificate.check sk199Slice.outerAD.value = true := by
  norm_num [sk199LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk199Slice,
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
private theorem sk199LogK_valid :
    sk199LogKCertificate.check sk199Slice.kAD.value = true := by
  norm_num [sk199LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk199Slice,
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
private theorem sk199LogDArg_valid :
    sk199LogDArgCertificate.check sk199Slice.dArgAD.value = true := by
  norm_num [sk199LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk199Slice,
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

theorem sk199ValidityFacts : SKFacts sk199Slice
    sk199LogOuterCertificate sk199LogKCertificate
    sk199LogDArgCertificate :=
  { domain := by norm_num [sk199Slice]
    kPositive := by
      norm_num [sk199Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk199LogOuter_valid
    logK := sk199LogK_valid
    logDArg := sk199LogDArg_valid }

noncomputable def sk199RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24150671/16777216), upper := (24213479/16777216) }
    logK := { lower := (19612449/16777216), upper := (153857/131072) }
    logDArg := { lower := (4456823/16777216), upper := (4601029/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk199LogOuterInput_eq :
    sk199RoundedInputs.logOuter = outerEnclosure 24
      (sk199LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk199LogKInput_eq :
    sk199RoundedInputs.logK = outerEnclosure 24
      (sk199LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk199LogDArgInput_eq :
    sk199RoundedInputs.logDArg = outerEnclosure 24
      (sk199LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk199RoundedFacts : SKRoundedFacts 8
    sk199LogOuterCertificate sk199LogKCertificate
    sk199LogDArgCertificate sk199RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk199LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk199LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk199LogDArgInput_eq }

noncomputable def sk200Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (207/64), kHi := (13/4) }

noncomputable def sk200LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8879713/8388608) }, upper := { exponent := 2, mantissa := (17/16) } }

noncomputable def sk200LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (207/128) }, upper := { exponent := 1, mantissa := (13/8) } }

noncomputable def sk200LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (408463111/313524224) }, upper := { exponent := 0, mantissa := (272/207) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk200LogOuter_valid :
    sk200LogOuterCertificate.check sk200Slice.outerAD.value = true := by
  norm_num [sk200LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk200Slice,
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
private theorem sk200LogK_valid :
    sk200LogKCertificate.check sk200Slice.kAD.value = true := by
  norm_num [sk200LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk200Slice,
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
private theorem sk200LogDArg_valid :
    sk200LogDArgCertificate.check sk200Slice.dArgAD.value = true := by
  norm_num [sk200LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk200Slice,
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

theorem sk200ValidityFacts : SKFacts sk200Slice
    sk200LogOuterCertificate sk200LogKCertificate
    sk200LogDArgCertificate :=
  { domain := by norm_num [sk200Slice]
    kPositive := by
      norm_num [sk200Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk200LogOuter_valid
    logK := sk200LogK_valid
    logDArg := sk200LogDArg_valid }

noncomputable def sk200RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24212693/16777216), upper := (24275273/16777216) }
    logK := { lower := (19693695/16777216), upper := (9887275/8388608) }
    logDArg := { lower := (554749/2097152), upper := (2290789/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk200LogOuterInput_eq :
    sk200RoundedInputs.logOuter = outerEnclosure 24
      (sk200LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk200LogKInput_eq :
    sk200RoundedInputs.logK = outerEnclosure 24
      (sk200LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk200LogDArgInput_eq :
    sk200RoundedInputs.logDArg = outerEnclosure 24
      (sk200LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk200RoundedFacts : SKRoundedFacts 8
    sk200LogOuterCertificate sk200LogKCertificate
    sk200LogDArgCertificate sk200RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk200LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk200LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk200LogDArgInput_eq }

noncomputable def sk201Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (209/64) }

noncomputable def sk201LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8912479/8388608) }, upper := { exponent := 2, mantissa := (273/256) } }

noncomputable def sk201LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (13/8) }, upper := { exponent := 1, mantissa := (209/128) } }

noncomputable def sk201LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3707558079/2848980992) }, upper := { exponent := 0, mantissa := (21/16) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk201LogOuter_valid :
    sk201LogOuterCertificate.check sk201Slice.outerAD.value = true := by
  norm_num [sk201LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk201Slice,
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
private theorem sk201LogK_valid :
    sk201LogKCertificate.check sk201Slice.kAD.value = true := by
  norm_num [sk201LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk201Slice,
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
private theorem sk201LogDArg_valid :
    sk201LogDArgCertificate.check sk201Slice.dArgAD.value = true := by
  norm_num [sk201LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk201Slice,
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

theorem sk201ValidityFacts : SKFacts sk201Slice
    sk201LogOuterCertificate sk201LogKCertificate
    sk201LogDArgCertificate :=
  { domain := by norm_num [sk201Slice]
    kPositive := by
      norm_num [sk201Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk201LogOuter_valid
    logK := sk201LogK_valid
    logDArg := sk201LogDArg_valid }

noncomputable def sk201RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24274487/16777216), upper := (24336841/16777216) }
    logK := { lower := (19774549/16777216), upper := (19855017/16777216) }
    logDArg := { lower := (4419321/16777216), upper := (4562291/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk201LogOuterInput_eq :
    sk201RoundedInputs.logOuter = outerEnclosure 24
      (sk201LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk201LogKInput_eq :
    sk201RoundedInputs.logK = outerEnclosure 24
      (sk201LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk201LogDArgInput_eq :
    sk201RoundedInputs.logDArg = outerEnclosure 24
      (sk201LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk201RoundedFacts : SKRoundedFacts 8
    sk201LogOuterCertificate sk201LogKCertificate
    sk201LogDArgCertificate sk201RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk201LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk201LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk201LogDArgInput_eq }

noncomputable def sk202Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (209/64), kHi := (105/32) }

noncomputable def sk202LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8945245/8388608) }, upper := { exponent := 2, mantissa := (137/128) } }

noncomputable def sk202LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (209/128) }, upper := { exponent := 1, mantissa := (105/64) } }

noncomputable def sk202LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (113305431/87162880) }, upper := { exponent := 0, mantissa := (274/209) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk202LogOuter_valid :
    sk202LogOuterCertificate.check sk202Slice.outerAD.value = true := by
  norm_num [sk202LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk202Slice,
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
private theorem sk202LogK_valid :
    sk202LogKCertificate.check sk202Slice.kAD.value = true := by
  norm_num [sk202LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk202Slice,
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
private theorem sk202LogDArg_valid :
    sk202LogDArgCertificate.check sk202Slice.dArgAD.value = true := by
  norm_num [sk202LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk202Slice,
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

theorem sk202ValidityFacts : SKFacts sk202Slice
    sk202LogOuterCertificate sk202LogKCertificate
    sk202LogDArgCertificate :=
  { domain := by norm_num [sk202Slice]
    kPositive := by
      norm_num [sk202Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk202LogOuter_valid
    logK := sk202LogK_valid
    logDArg := sk202LogDArg_valid }

noncomputable def sk202RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12168027/8388608), upper := (3049773/2097152) }
    logK := { lower := (19855015/16777216), upper := (19935099/16777216) }
    logDArg := { lower := (4400807/16777216), upper := (4543167/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk202LogOuterInput_eq :
    sk202RoundedInputs.logOuter = outerEnclosure 24
      (sk202LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk202LogKInput_eq :
    sk202RoundedInputs.logK = outerEnclosure 24
      (sk202LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk202LogDArgInput_eq :
    sk202RoundedInputs.logDArg = outerEnclosure 24
      (sk202LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk202RoundedFacts : SKRoundedFacts 8
    sk202LogOuterCertificate sk202LogKCertificate
    sk202LogDArgCertificate sk202RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk202LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk202LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk202LogDArgInput_eq }

noncomputable def sk203Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (211/64) }

noncomputable def sk203LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (8978011/8388608) }, upper := { exponent := 2, mantissa := (275/256) } }

noncomputable def sk203LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (105/64) }, upper := { exponent := 1, mantissa := (211/128) } }

noncomputable def sk203LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1256910477/967966720) }, upper := { exponent := 0, mantissa := (55/42) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk203LogOuter_valid :
    sk203LogOuterCertificate.check sk203Slice.outerAD.value = true := by
  norm_num [sk203LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk203Slice,
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
private theorem sk203LogK_valid :
    sk203LogKCertificate.check sk203Slice.kAD.value = true := by
  norm_num [sk203LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk203Slice,
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
private theorem sk203LogDArg_valid :
    sk203LogDArgCertificate.check sk203Slice.dArgAD.value = true := by
  norm_num [sk203LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk203Slice,
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

theorem sk203ValidityFacts : SKFacts sk203Slice
    sk203LogOuterCertificate sk203LogKCertificate
    sk203LogDArgCertificate :=
  { domain := by norm_num [sk203Slice]
    kPositive := by
      norm_num [sk203Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk203LogOuter_valid
    logK := sk203LogK_valid
    logDArg := sk203LogDArg_valid }

noncomputable def sk203RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6099349/4194304), upper := (24459303/16777216) }
    logK := { lower := (9967549/8388608), upper := (20014801/16777216) }
    logDArg := { lower := (273903/1048576), upper := (1131051/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk203LogOuterInput_eq :
    sk203RoundedInputs.logOuter = outerEnclosure 24
      (sk203LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk203LogKInput_eq :
    sk203RoundedInputs.logK = outerEnclosure 24
      (sk203LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk203LogDArgInput_eq :
    sk203RoundedInputs.logDArg = outerEnclosure 24
      (sk203LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk203RoundedFacts : SKRoundedFacts 8
    sk203LogOuterCertificate sk203LogKCertificate
    sk203LogDArgCertificate sk203RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk203LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk203LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk203LogDArgInput_eq }

noncomputable def sk204Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (211/64), kHi := (53/16) }

noncomputable def sk204LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9010777/8388608) }, upper := { exponent := 2, mantissa := (69/64) } }

noncomputable def sk204LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (211/128) }, upper := { exponent := 1, mantissa := (53/32) } }

noncomputable def sk204LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3802514703/2931556352) }, upper := { exponent := 0, mantissa := (276/211) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk204LogOuter_valid :
    sk204LogOuterCertificate.check sk204Slice.outerAD.value = true := by
  norm_num [sk204LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk204Slice,
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
private theorem sk204LogK_valid :
    sk204LogKCertificate.check sk204Slice.kAD.value = true := by
  norm_num [sk204LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk204Slice,
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
private theorem sk204LogDArg_valid :
    sk204LogDArgCertificate.check sk204Slice.dArgAD.value = true := by
  norm_num [sk204LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk204Slice,
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

theorem sk204ValidityFacts : SKFacts sk204Slice
    sk204LogOuterCertificate sk204LogKCertificate
    sk204LogDArgCertificate :=
  { domain := by norm_num [sk204Slice]
    kPositive := by
      norm_num [sk204Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk204LogOuter_valid
    logK := sk204LogK_valid
    logDArg := sk204LogDArg_valid }

noncomputable def sk204RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12229257/8388608), upper := (24520201/16777216) }
    logK := { lower := (1250925/1048576), upper := (10047063/8388608) }
    logDArg := { lower := (2182121/8388608), upper := (563175/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk204LogOuterInput_eq :
    sk204RoundedInputs.logOuter = outerEnclosure 24
      (sk204LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk204LogKInput_eq :
    sk204RoundedInputs.logK = outerEnclosure 24
      (sk204LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk204LogDArgInput_eq :
    sk204RoundedInputs.logDArg = outerEnclosure 24
      (sk204LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk204RoundedFacts : SKRoundedFacts 8
    sk204LogOuterCertificate sk204LogKCertificate
    sk204LogDArgCertificate sk204RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk204LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk204LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk204LogDArgInput_eq }

noncomputable def sk205Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (215/64) }

noncomputable def sk205LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9109075/8388608) }, upper := { exponent := 2, mantissa := (279/256) } }

noncomputable def sk205LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (107/64) }, upper := { exponent := 1, mantissa := (215/128) } }

noncomputable def sk205LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3898650903/3015311360) }, upper := { exponent := 0, mantissa := (279/214) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk205LogOuter_valid :
    sk205LogOuterCertificate.check sk205Slice.outerAD.value = true := by
  norm_num [sk205LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk205Slice,
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
private theorem sk205LogK_valid :
    sk205LogKCertificate.check sk205Slice.kAD.value = true := by
  norm_num [sk205LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk205Slice,
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
private theorem sk205LogDArg_valid :
    sk205LogDArgCertificate.check sk205Slice.dArgAD.value = true := by
  norm_num [sk205LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk205Slice,
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

theorem sk205ValidityFacts : SKFacts sk205Slice
    sk205LogOuterCertificate sk205LogKCertificate
    sk205LogDArgCertificate :=
  { domain := by norm_num [sk205Slice]
    kPositive := by
      norm_num [sk205Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk205LogOuter_valid
    logK := sk205LogK_valid
    logDArg := sk205LogDArg_valid }

noncomputable def sk205RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24640545/16777216), upper := (12350789/8388608) }
    logK := { lower := (10125829/8388608), upper := (20329875/16777216) }
    logDArg := { lower := (4310527/16777216), upper := (2224959/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk205LogOuterInput_eq :
    sk205RoundedInputs.logOuter = outerEnclosure 24
      (sk205LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk205LogKInput_eq :
    sk205RoundedInputs.logK = outerEnclosure 24
      (sk205LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk205LogDArgInput_eq :
    sk205RoundedInputs.logDArg = outerEnclosure 24
      (sk205LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk205RoundedFacts : SKRoundedFacts 8
    sk205LogOuterCertificate sk205LogKCertificate
    sk205LogDArgCertificate sk205RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk205LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk205LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk205LogDArgInput_eq }

noncomputable def sk206Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (215/64), kHi := (27/8) }

noncomputable def sk206LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9141841/8388608) }, upper := { exponent := 2, mantissa := (35/32) } }

noncomputable def sk206LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (215/128) }, upper := { exponent := 1, mantissa := (27/16) } }

noncomputable def sk206LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (145591053/112721920) }, upper := { exponent := 0, mantissa := (56/43) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk206LogOuter_valid :
    sk206LogOuterCertificate.check sk206Slice.outerAD.value = true := by
  norm_num [sk206LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk206Slice,
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
private theorem sk206LogK_valid :
    sk206LogKCertificate.check sk206Slice.kAD.value = true := by
  norm_num [sk206LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk206Slice,
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
private theorem sk206LogDArg_valid :
    sk206LogDArgCertificate.check sk206Slice.dArgAD.value = true := by
  norm_num [sk206LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk206Slice,
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

theorem sk206ValidityFacts : SKFacts sk206Slice
    sk206LogOuterCertificate sk206LogKCertificate
    sk206LogDArgCertificate :=
  { domain := by norm_num [sk206Slice]
    kPositive := by
      norm_num [sk206Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk206LogOuter_valid
    logK := sk206LogK_valid
    logDArg := sk206LogDArg_valid }

noncomputable def sk206RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24700785/16777216), upper := (6190401/4194304) }
    logK := { lower := (10164937/8388608), upper := (1275483/1048576) }
    logDArg := { lower := (1073229/4194304), upper := (4431729/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk206LogOuterInput_eq :
    sk206RoundedInputs.logOuter = outerEnclosure 24
      (sk206LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk206LogKInput_eq :
    sk206RoundedInputs.logK = outerEnclosure 24
      (sk206LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk206LogDArgInput_eq :
    sk206RoundedInputs.logDArg = outerEnclosure 24
      (sk206LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk206RoundedFacts : SKRoundedFacts 8
    sk206LogOuterCertificate sk206LogKCertificate
    sk206LogDArgCertificate sk206RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk206LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk206LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk206LogDArgInput_eq }

noncomputable def sk207Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (213/64) }

noncomputable def sk207LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9043543/8388608) }, upper := { exponent := 2, mantissa := (277/256) } }

noncomputable def sk207LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (53/32) }, upper := { exponent := 1, mantissa := (213/128) } }

noncomputable def sk207LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1278143013/986447872) }, upper := { exponent := 0, mantissa := (277/212) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk207LogOuter_valid :
    sk207LogOuterCertificate.check sk207Slice.outerAD.value = true := by
  norm_num [sk207LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk207Slice,
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
private theorem sk207LogK_valid :
    sk207LogKCertificate.check sk207Slice.kAD.value = true := by
  norm_num [sk207LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk207Slice,
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
private theorem sk207LogDArg_valid :
    sk207LogDArgCertificate.check sk207Slice.dArgAD.value = true := by
  norm_num [sk207LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk207Slice,
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

theorem sk207ValidityFacts : SKFacts sk207Slice
    sk207LogOuterCertificate sk207LogKCertificate
    sk207LogDArgCertificate :=
  { domain := by norm_num [sk207Slice]
    kPositive := by
      norm_num [sk207Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk207LogOuter_valid
    logK := sk207LogK_valid
    logDArg := sk207LogDArg_valid }

noncomputable def sk207RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24519411/16777216), upper := (12290439/8388608) }
    logK := { lower := (20094125/16777216), upper := (10086539/8388608) }
    logDArg := { lower := (1086547/4194304), upper := (140211/524288) } }

set_option maxRecDepth 1000000 in
private theorem sk207LogOuterInput_eq :
    sk207RoundedInputs.logOuter = outerEnclosure 24
      (sk207LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk207LogKInput_eq :
    sk207RoundedInputs.logK = outerEnclosure 24
      (sk207LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk207LogDArgInput_eq :
    sk207RoundedInputs.logDArg = outerEnclosure 24
      (sk207LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk207RoundedFacts : SKRoundedFacts 8
    sk207LogOuterCertificate sk207LogKCertificate
    sk207LogDArgCertificate sk207RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk207LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk207LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk207LogDArgInput_eq }

noncomputable def sk208Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (213/64), kHi := (107/32) }

noncomputable def sk208LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9076309/8388608) }, upper := { exponent := 2, mantissa := (139/128) } }

noncomputable def sk208LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (213/128) }, upper := { exponent := 1, mantissa := (107/64) } }

noncomputable def sk208LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1288824813/995753984) }, upper := { exponent := 0, mantissa := (278/213) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk208LogOuter_valid :
    sk208LogOuterCertificate.check sk208Slice.outerAD.value = true := by
  norm_num [sk208LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk208Slice,
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
private theorem sk208LogK_valid :
    sk208LogKCertificate.check sk208Slice.kAD.value = true := by
  norm_num [sk208LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk208Slice,
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
private theorem sk208LogDArg_valid :
    sk208LogDArgCertificate.check sk208Slice.dArgAD.value = true := by
  norm_num [sk208LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk208Slice,
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

theorem sk208ValidityFacts : SKFacts sk208Slice
    sk208LogOuterCertificate sk208LogKCertificate
    sk208LogDArgCertificate :=
  { domain := by norm_num [sk208Slice]
    kPositive := by
      norm_num [sk208Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk208LogOuter_valid
    logK := sk208LogK_valid
    logDArg := sk208LogDArg_valid }

noncomputable def sk208RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24580087/16777216), upper := (3080167/2097152) }
    logK := { lower := (5043269/4194304), upper := (5062915/4194304) }
    logDArg := { lower := (1082071/4194304), upper := (4468259/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk208LogOuterInput_eq :
    sk208RoundedInputs.logOuter = outerEnclosure 24
      (sk208LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk208LogKInput_eq :
    sk208RoundedInputs.logK = outerEnclosure 24
      (sk208LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk208LogDArgInput_eq :
    sk208RoundedInputs.logDArg = outerEnclosure 24
      (sk208LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk208RoundedFacts : SKRoundedFacts 8
    sk208LogOuterCertificate sk208LogKCertificate
    sk208LogDArgCertificate sk208RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk208LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk208LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk208LogDArgInput_eq }

noncomputable def sk209Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64) }

noncomputable def sk209LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9633331/8388608) }, upper := { exponent := 2, mantissa := (295/256) } }

noncomputable def sk209LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (115/64) }, upper := { exponent := 1, mantissa := (231/128) } }

noncomputable def sk209LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1477099677/1160642560) }, upper := { exponent := 0, mantissa := (59/46) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk209LogOuter_valid :
    sk209LogOuterCertificate.check sk209Slice.outerAD.value = true := by
  norm_num [sk209LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk209Slice,
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
private theorem sk209LogK_valid :
    sk209LogKCertificate.check sk209Slice.kAD.value = true := by
  norm_num [sk209LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk209Slice,
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
private theorem sk209LogDArg_valid :
    sk209LogDArgCertificate.check sk209Slice.dArgAD.value = true := by
  norm_num [sk209LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk209Slice,
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

theorem sk209ValidityFacts : SKFacts sk209Slice
    sk209LogOuterCertificate sk209LogKCertificate
    sk209LogDArgCertificate :=
  { domain := by norm_num [sk209Slice]
    kPositive := by
      norm_num [sk209Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk209LogOuter_valid
    logK := sk209LogK_valid
    logDArg := sk209LogDArg_valid }

noncomputable def sk209RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12789681/8388608), upper := (25637135/16777216) }
    logK := { lower := (21461351/16777216), upper := (10767069/8388608) }
    logDArg := { lower := (4045099/16777216), upper := (4175783/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk209LogOuterInput_eq :
    sk209RoundedInputs.logOuter = outerEnclosure 24
      (sk209LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk209LogKInput_eq :
    sk209RoundedInputs.logK = outerEnclosure 24
      (sk209LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk209LogDArgInput_eq :
    sk209RoundedInputs.logDArg = outerEnclosure 24
      (sk209LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk209RoundedFacts : SKRoundedFacts 8
    sk209LogOuterCertificate sk209LogKCertificate
    sk209LogDArgCertificate sk209RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk209LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk209LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk209LogDArgInput_eq }

noncomputable def sk210Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8) }

noncomputable def sk210LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9666097/8388608) }, upper := { exponent := 2, mantissa := (37/32) } }

noncomputable def sk210LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (231/128) }, upper := { exponent := 1, mantissa := (29/16) } }

noncomputable def sk210LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (135324351/106430464) }, upper := { exponent := 0, mantissa := (296/231) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk210LogOuter_valid :
    sk210LogOuterCertificate.check sk210Slice.outerAD.value = true := by
  norm_num [sk210LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk210Slice,
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
private theorem sk210LogK_valid :
    sk210LogKCertificate.check sk210Slice.kAD.value = true := by
  norm_num [sk210LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk210Slice,
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
private theorem sk210LogDArg_valid :
    sk210LogDArgCertificate.check sk210Slice.dArgAD.value = true := by
  norm_num [sk210LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk210Slice,
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

theorem sk210ValidityFacts : SKFacts sk210Slice
    sk210LogOuterCertificate sk210LogKCertificate
    sk210LogDArgCertificate :=
  { domain := by norm_num [sk210Slice]
    kPositive := by
      norm_num [sk210Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk210LogOuter_valid
    logK := sk210LogK_valid
    logDArg := sk210LogDArg_valid }

noncomputable def sk210RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12818165/8388608), upper := (25693911/16777216) }
    logK := { lower := (21534137/16777216), upper := (10803305/8388608) }
    logDArg := { lower := (1007399/4194304), upper := (4159773/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk210LogOuterInput_eq :
    sk210RoundedInputs.logOuter = outerEnclosure 24
      (sk210LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk210LogKInput_eq :
    sk210RoundedInputs.logK = outerEnclosure 24
      (sk210LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk210LogDArgInput_eq :
    sk210RoundedInputs.logDArg = outerEnclosure 24
      (sk210LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk210RoundedFacts : SKRoundedFacts 8
    sk210LogOuterCertificate sk210LogKCertificate
    sk210LogDArgCertificate sk210RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk210LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk210LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk210LogDArgInput_eq }

noncomputable def sk211Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64) }

noncomputable def sk211LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9502267/8388608) }, upper := { exponent := 2, mantissa := (291/256) } }

noncomputable def sk211LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (113/64) }, upper := { exponent := 1, mantissa := (227/128) } }

noncomputable def sk211LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4294991463/3362127872) }, upper := { exponent := 0, mantissa := (291/226) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk211LogOuter_valid :
    sk211LogOuterCertificate.check sk211Slice.outerAD.value = true := by
  norm_num [sk211LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk211Slice,
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
private theorem sk211LogK_valid :
    sk211LogKCertificate.check sk211Slice.kAD.value = true := by
  norm_num [sk211LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk211Slice,
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
private theorem sk211LogDArg_valid :
    sk211LogDArgCertificate.check sk211Slice.dArgAD.value = true := by
  norm_num [sk211LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk211Slice,
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

theorem sk211ValidityFacts : SKFacts sk211Slice
    sk211LogOuterCertificate sk211LogKCertificate
    sk211LogDArgCertificate :=
  { domain := by norm_num [sk211Slice]
    kPositive := by
      norm_num [sk211Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk211LogOuter_valid
    logK := sk211LogK_valid
    logDArg := sk211LogDArg_valid }

noncomputable def sk211RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25349537/16777216), upper := (25408091/16777216) }
    logK := { lower := (10583503/8388608), upper := (21241079/16777216) }
    logDArg := { lower := (4108329/16777216), upper := (1060271/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk211LogOuterInput_eq :
    sk211RoundedInputs.logOuter = outerEnclosure 24
      (sk211LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk211LogKInput_eq :
    sk211RoundedInputs.logK = outerEnclosure 24
      (sk211LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk211LogDArgInput_eq :
    sk211RoundedInputs.logDArg = outerEnclosure 24
      (sk211LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk211RoundedFacts : SKRoundedFacts 8
    sk211LogOuterCertificate sk211LogKCertificate
    sk211LogDArgCertificate sk211RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk211LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk211LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk211LogDArgInput_eq }

noncomputable def sk212Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16) }

noncomputable def sk212LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9535033/8388608) }, upper := { exponent := 2, mantissa := (73/64) } }

noncomputable def sk212LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (227/128) }, upper := { exponent := 1, mantissa := (57/32) } }

noncomputable def sk212LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1442957253/1130627072) }, upper := { exponent := 0, mantissa := (292/227) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk212LogOuter_valid :
    sk212LogOuterCertificate.check sk212Slice.outerAD.value = true := by
  norm_num [sk212LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk212Slice,
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
private theorem sk212LogK_valid :
    sk212LogKCertificate.check sk212Slice.kAD.value = true := by
  norm_num [sk212LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk212Slice,
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
private theorem sk212LogDArg_valid :
    sk212LogDArgCertificate.check sk212Slice.dArgAD.value = true := by
  norm_num [sk212LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk212Slice,
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

theorem sk212ValidityFacts : SKFacts sk212Slice
    sk212LogOuterCertificate sk212LogKCertificate
    sk212LogDArgCertificate :=
  { domain := by norm_num [sk212Slice]
    kPositive := by
      norm_num [sk212Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk212LogOuter_valid
    logK := sk212LogK_valid
    logDArg := sk212LogDArg_valid }

noncomputable def sk212RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25407289/16777216), upper := (12732823/8388608) }
    logK := { lower := (10620539/8388608), upper := (21314825/16777216) }
    logDArg := { lower := (255771/1048576), upper := (4224567/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk212LogOuterInput_eq :
    sk212RoundedInputs.logOuter = outerEnclosure 24
      (sk212LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk212LogKInput_eq :
    sk212RoundedInputs.logK = outerEnclosure 24
      (sk212LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk212LogDArgInput_eq :
    sk212RoundedInputs.logDArg = outerEnclosure 24
      (sk212LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk212RoundedFacts : SKRoundedFacts 8
    sk212LogOuterCertificate sk212LogKCertificate
    sk212LogDArgCertificate sk212RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk212LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk212LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk212LogDArgInput_eq }

noncomputable def sk213Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64) }

noncomputable def sk213LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9436735/8388608) }, upper := { exponent := 2, mantissa := (289/256) } }

noncomputable def sk213LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (7/4) }, upper := { exponent := 1, mantissa := (225/128) } }

noncomputable def sk213LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (469736007/367001600) }, upper := { exponent := 0, mantissa := (289/224) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk213LogOuter_valid :
    sk213LogOuterCertificate.check sk213Slice.outerAD.value = true := by
  norm_num [sk213LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk213Slice,
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
private theorem sk213LogK_valid :
    sk213LogKCertificate.check sk213Slice.kAD.value = true := by
  norm_num [sk213LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk213Slice,
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
private theorem sk213LogDArg_valid :
    sk213LogDArgCertificate.check sk213Slice.dArgAD.value = true := by
  norm_num [sk213LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk213Slice,
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

theorem sk213ValidityFacts : SKFacts sk213Slice
    sk213LogOuterCertificate sk213LogKCertificate
    sk213LogDArgCertificate :=
  { domain := by norm_num [sk213Slice]
    kPositive := by
      norm_num [sk213Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk213LogOuter_valid
    logK := sk213LogK_valid
    logDArg := sk213LogDArg_valid }

noncomputable def sk213RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25233433/16777216), upper := (12646193/8388608) }
    logK := { lower := (10508937/8388608), upper := (21092607/16777216) }
    logDArg := { lower := (2070347/8388608), upper := (2137255/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk213LogOuterInput_eq :
    sk213RoundedInputs.logOuter = outerEnclosure 24
      (sk213LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk213LogKInput_eq :
    sk213RoundedInputs.logK = outerEnclosure 24
      (sk213LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk213LogDArgInput_eq :
    sk213RoundedInputs.logDArg = outerEnclosure 24
      (sk213LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk213RoundedFacts : SKRoundedFacts 8
    sk213LogOuterCertificate sk213LogKCertificate
    sk213LogDArgCertificate sk213RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk213LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk213LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk213LogDArgInput_eq }

noncomputable def sk214Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32) }

noncomputable def sk214LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9469501/8388608) }, upper := { exponent := 2, mantissa := (145/128) } }

noncomputable def sk214LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (225/128) }, upper := { exponent := 1, mantissa := (113/64) } }

noncomputable def sk214LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (473471359/370278400) }, upper := { exponent := 0, mantissa := (58/45) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk214LogOuter_valid :
    sk214LogOuterCertificate.check sk214Slice.outerAD.value = true := by
  norm_num [sk214LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk214Slice,
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
private theorem sk214LogK_valid :
    sk214LogKCertificate.check sk214Slice.kAD.value = true := by
  norm_num [sk214LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk214Slice,
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
private theorem sk214LogDArg_valid :
    sk214LogDArgCertificate.check sk214Slice.dArgAD.value = true := by
  norm_num [sk214LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk214Slice,
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

theorem sk214ValidityFacts : SKFacts sk214Slice
    sk214LogOuterCertificate sk214LogKCertificate
    sk214LogDArgCertificate :=
  { domain := by norm_num [sk214Slice]
    kPositive := by
      norm_num [sk214Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk214LogOuter_valid
    logK := sk214LogK_valid
    logDArg := sk214LogDArg_valid }

noncomputable def sk214RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25291585/16777216), upper := (12675169/8388608) }
    logK := { lower := (10546303/8388608), upper := (21167007/16777216) }
    logDArg := { lower := (128889/524288), upper := (4257731/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk214LogOuterInput_eq :
    sk214RoundedInputs.logOuter = outerEnclosure 24
      (sk214LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk214LogKInput_eq :
    sk214RoundedInputs.logK = outerEnclosure 24
      (sk214LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk214LogDArgInput_eq :
    sk214RoundedInputs.logDArg = outerEnclosure 24
      (sk214LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk214RoundedFacts : SKRoundedFacts 8
    sk214LogOuterCertificate sk214LogKCertificate
    sk214LogDArgCertificate sk214RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk214LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk214LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk214LogDArgInput_eq }

noncomputable def sk215Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64) }

noncomputable def sk215LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9567799/8388608) }, upper := { exponent := 2, mantissa := (293/256) } }

noncomputable def sk215LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (57/32) }, upper := { exponent := 1, mantissa := (229/128) } }

noncomputable def sk215LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1454294373/1140588544) }, upper := { exponent := 0, mantissa := (293/228) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk215LogOuter_valid :
    sk215LogOuterCertificate.check sk215Slice.outerAD.value = true := by
  norm_num [sk215LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk215Slice,
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
private theorem sk215LogK_valid :
    sk215LogKCertificate.check sk215Slice.kAD.value = true := by
  norm_num [sk215LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk215Slice,
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
private theorem sk215LogDArg_valid :
    sk215LogDArgCertificate.check sk215Slice.dArgAD.value = true := by
  norm_num [sk215LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk215Slice,
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

theorem sk215ValidityFacts : SKFacts sk215Slice
    sk215LogOuterCertificate sk215LogKCertificate
    sk215LogDArgCertificate :=
  { domain := by norm_num [sk215Slice]
    kPositive := by
      norm_num [sk215Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk215LogOuter_valid
    logK := sk215LogK_valid
    logDArg := sk215LogDArg_valid }

noncomputable def sk215RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25464843/16777216), upper := (6380751/4194304) }
    logK := { lower := (2664353/2097152), upper := (21388249/16777216) }
    logDArg := { lower := (4076467/16777216), upper := (4208179/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk215LogOuterInput_eq :
    sk215RoundedInputs.logOuter = outerEnclosure 24
      (sk215LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk215LogKInput_eq :
    sk215RoundedInputs.logK = outerEnclosure 24
      (sk215LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk215LogDArgInput_eq :
    sk215RoundedInputs.logDArg = outerEnclosure 24
      (sk215LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk215RoundedFacts : SKRoundedFacts 8
    sk215LogOuterCertificate sk215LogKCertificate
    sk215LogDArgCertificate sk215RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk215LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk215LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk215LogDArgInput_eq }

noncomputable def sk216Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32) }

noncomputable def sk216LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9600565/8388608) }, upper := { exponent := 2, mantissa := (147/128) } }

noncomputable def sk216LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (229/128) }, upper := { exponent := 1, mantissa := (115/64) } }

noncomputable def sk216LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4397025543/3451781120) }, upper := { exponent := 0, mantissa := (294/229) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk216LogOuter_valid :
    sk216LogOuterCertificate.check sk216Slice.outerAD.value = true := by
  norm_num [sk216LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk216Slice,
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
private theorem sk216LogK_valid :
    sk216LogKCertificate.check sk216Slice.kAD.value = true := by
  norm_num [sk216LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk216Slice,
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
private theorem sk216LogDArg_valid :
    sk216LogDArgCertificate.check sk216Slice.dArgAD.value = true := by
  norm_num [sk216LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk216Slice,
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

theorem sk216ValidityFacts : SKFacts sk216Slice
    sk216LogOuterCertificate sk216LogKCertificate
    sk216LogDArgCertificate :=
  { domain := by norm_num [sk216Slice]
    kPositive := by
      norm_num [sk216Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk216LogOuter_valid
    logK := sk216LogK_valid
    logDArg := sk216LogDArg_valid }

noncomputable def sk216RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3190275/2097152), upper := (25580167/16777216) }
    logK := { lower := (21388247/16777216), upper := (2682669/2097152) }
    logDArg := { lower := (2030361/8388608), upper := (2095959/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk216LogOuterInput_eq :
    sk216RoundedInputs.logOuter = outerEnclosure 24
      (sk216LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk216LogKInput_eq :
    sk216RoundedInputs.logK = outerEnclosure 24
      (sk216LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk216LogDArgInput_eq :
    sk216RoundedInputs.logDArg = outerEnclosure 24
      (sk216LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk216RoundedFacts : SKRoundedFacts 8
    sk216LogOuterCertificate sk216LogKCertificate
    sk216LogDArgCertificate sk216RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk216LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk216LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk216LogDArgInput_eq }

noncomputable def sk217Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64) }

noncomputable def sk217LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9698863/8388608) }, upper := { exponent := 2, mantissa := (297/256) } }

noncomputable def sk217LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (29/16) }, upper := { exponent := 1, mantissa := (233/128) } }

noncomputable def sk217LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4500239199/3542614016) }, upper := { exponent := 0, mantissa := (297/232) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk217LogOuter_valid :
    sk217LogOuterCertificate.check sk217Slice.outerAD.value = true := by
  norm_num [sk217LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk217Slice,
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
private theorem sk217LogK_valid :
    sk217LogKCertificate.check sk217Slice.kAD.value = true := by
  norm_num [sk217LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk217Slice,
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
private theorem sk217LogDArg_valid :
    sk217LogDArgCertificate.check sk217Slice.dArgAD.value = true := by
  norm_num [sk217LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk217Slice,
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

theorem sk217ValidityFacts : SKFacts sk217Slice
    sk217LogOuterCertificate sk217LogKCertificate
    sk217LogDArgCertificate :=
  { domain := by norm_num [sk217Slice]
    kPositive := by
      norm_num [sk217Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk217LogOuter_valid
    logK := sk217LogK_valid
    logDArg := sk217LogDArg_valid }

noncomputable def sk217RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25693105/16777216), upper := (25750495/16777216) }
    logK := { lower := (21606609/16777216), upper := (21678771/16777216) }
    logDArg := { lower := (4014211/16777216), upper := (4143885/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk217LogOuterInput_eq :
    sk217RoundedInputs.logOuter = outerEnclosure 24
      (sk217LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk217LogKInput_eq :
    sk217RoundedInputs.logK = outerEnclosure 24
      (sk217LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk217LogDArgInput_eq :
    sk217RoundedInputs.logDArg = outerEnclosure 24
      (sk217LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk217RoundedFacts : SKRoundedFacts 8
    sk217LogOuterCertificate sk217LogKCertificate
    sk217LogDArgCertificate sk217RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk217LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk217LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk217LogDArgInput_eq }

noncomputable def sk218Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32) }

noncomputable def sk218LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9731629/8388608) }, upper := { exponent := 2, mantissa := (149/128) } }

noncomputable def sk218LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (233/128) }, upper := { exponent := 1, mantissa := (117/64) } }

noncomputable def sk218LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (503878431/397017088) }, upper := { exponent := 0, mantissa := (298/233) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk218LogOuter_valid :
    sk218LogOuterCertificate.check sk218Slice.outerAD.value = true := by
  norm_num [sk218LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk218Slice,
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
private theorem sk218LogK_valid :
    sk218LogKCertificate.check sk218Slice.kAD.value = true := by
  norm_num [sk218LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk218Slice,
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
private theorem sk218LogDArg_valid :
    sk218LogDArgCertificate.check sk218Slice.dArgAD.value = true := by
  norm_num [sk218LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk218Slice,
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

theorem sk218ValidityFacts : SKFacts sk218Slice
    sk218LogOuterCertificate sk218LogKCertificate
    sk218LogDArgCertificate :=
  { domain := by norm_num [sk218Slice]
    kPositive := by
      norm_num [sk218Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk218LogOuter_valid
    logK := sk218LogK_valid
    logDArg := sk218LogDArg_valid }

noncomputable def sk218RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25749689/16777216), upper := (25806889/16777216) }
    logK := { lower := (21678769/16777216), upper := (10875311/8388608) }
    logDArg := { lower := (3998945/16777216), upper := (4128119/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk218LogOuterInput_eq :
    sk218RoundedInputs.logOuter = outerEnclosure 24
      (sk218LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk218LogKInput_eq :
    sk218RoundedInputs.logK = outerEnclosure 24
      (sk218LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk218LogDArgInput_eq :
    sk218RoundedInputs.logDArg = outerEnclosure 24
      (sk218LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk218RoundedFacts : SKRoundedFacts 8
    sk218LogOuterCertificate sk218LogKCertificate
    sk218LogDArgCertificate sk218RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk218LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk218LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk218LogDArgInput_eq }

noncomputable def sk219Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64) }

noncomputable def sk219LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9764395/8388608) }, upper := { exponent := 2, mantissa := (299/256) } }

noncomputable def sk219LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (117/64) }, upper := { exponent := 1, mantissa := (235/128) } }

noncomputable def sk219LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (507744847/400424960) }, upper := { exponent := 0, mantissa := (23/18) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk219LogOuter_valid :
    sk219LogOuterCertificate.check sk219Slice.outerAD.value = true := by
  norm_num [sk219LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk219Slice,
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
private theorem sk219LogK_valid :
    sk219LogKCertificate.check sk219Slice.kAD.value = true := by
  norm_num [sk219LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk219Slice,
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
private theorem sk219LogDArg_valid :
    sk219LogDArgCertificate.check sk219Slice.dArgAD.value = true := by
  norm_num [sk219LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk219Slice,
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

theorem sk219ValidityFacts : SKFacts sk219Slice
    sk219LogOuterCertificate sk219LogKCertificate
    sk219LogDArgCertificate :=
  { domain := by norm_num [sk219Slice]
    kPositive := by
      norm_num [sk219Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk219LogOuter_valid
    logK := sk219LogK_valid
    logDArg := sk219LogDArg_valid }

noncomputable def sk219RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12903041/8388608), upper := (12931547/8388608) }
    logK := { lower := (5437655/4194304), upper := (10911083/8388608) }
    logDArg := { lower := (1991897/8388608), upper := (4112473/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk219LogOuterInput_eq :
    sk219RoundedInputs.logOuter = outerEnclosure 24
      (sk219LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk219LogKInput_eq :
    sk219RoundedInputs.logK = outerEnclosure 24
      (sk219LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk219LogDArgInput_eq :
    sk219RoundedInputs.logDArg = outerEnclosure 24
      (sk219LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk219RoundedFacts : SKRoundedFacts 8
    sk219LogOuterCertificate sk219LogKCertificate
    sk219LogDArgCertificate sk219RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk219LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk219LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk219LogDArgInput_eq }

noncomputable def sk220Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16) }

noncomputable def sk220LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9797161/8388608) }, upper := { exponent := 2, mantissa := (75/64) } }

noncomputable def sk220LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (235/128) }, upper := { exponent := 1, mantissa := (59/32) } }

noncomputable def sk220LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4604632431/3634626560) }, upper := { exponent := 0, mantissa := (60/47) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk220LogOuter_valid :
    sk220LogOuterCertificate.check sk220Slice.outerAD.value = true := by
  norm_num [sk220LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk220Slice,
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
private theorem sk220LogK_valid :
    sk220LogKCertificate.check sk220Slice.kAD.value = true := by
  norm_num [sk220LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk220Slice,
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
private theorem sk220LogDArg_valid :
    sk220LogDArgCertificate.check sk220Slice.dArgAD.value = true := by
  norm_num [sk220LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk220Slice,
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

theorem sk220ValidityFacts : SKFacts sk220Slice
    sk220LogOuterCertificate sk220LogKCertificate
    sk220LogDArgCertificate :=
  { domain := by norm_num [sk220Slice]
    kPositive := by
      norm_num [sk220Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk220LogOuter_valid
    logK := sk220LogK_valid
    logDArg := sk220LogDArg_valid }

noncomputable def sk220RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12931143/8388608), upper := (3239889/2097152) }
    logK := { lower := (21822165/16777216), upper := (21893407/16777216) }
    logDArg := { lower := (3968759/16777216), upper := (2048473/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk220LogOuterInput_eq :
    sk220RoundedInputs.logOuter = outerEnclosure 24
      (sk220LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk220LogKInput_eq :
    sk220RoundedInputs.logK = outerEnclosure 24
      (sk220LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk220LogDArgInput_eq :
    sk220RoundedInputs.logDArg = outerEnclosure 24
      (sk220LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk220RoundedFacts : SKRoundedFacts 8
    sk220LogOuterCertificate sk220LogKCertificate
    sk220LogDArgCertificate sk220RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk220LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk220LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk220LogDArgInput_eq }

noncomputable def sk221Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64) }

noncomputable def sk221LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9829927/8388608) }, upper := { exponent := 2, mantissa := (301/256) } }

noncomputable def sk221LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (59/32) }, upper := { exponent := 1, mantissa := (237/128) } }

noncomputable def sk221LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1546564101/1221853184) }, upper := { exponent := 0, mantissa := (301/236) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk221LogOuter_valid :
    sk221LogOuterCertificate.check sk221Slice.outerAD.value = true := by
  norm_num [sk221LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk221Slice,
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
private theorem sk221LogK_valid :
    sk221LogKCertificate.check sk221Slice.kAD.value = true := by
  norm_num [sk221LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk221Slice,
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
private theorem sk221LogDArg_valid :
    sk221LogDArgCertificate.check sk221Slice.dArgAD.value = true := by
  norm_num [sk221LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk221Slice,
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

theorem sk221ValidityFacts : SKFacts sk221Slice
    sk221LogOuterCertificate sk221LogKCertificate
    sk221LogDArgCertificate :=
  { domain := by norm_num [sk221Slice]
    kPositive := by
      norm_num [sk221Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk221LogOuter_valid
    logK := sk221LogK_valid
    logDArg := sk221LogDArg_valid }

noncomputable def sk221RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25918303/16777216), upper := (25974943/16777216) }
    logK := { lower := (10946703/8388608), upper := (21964347/16777216) }
    logDArg := { lower := (3953837/16777216), upper := (31887/131072) } }

set_option maxRecDepth 1000000 in
private theorem sk221LogOuterInput_eq :
    sk221RoundedInputs.logOuter = outerEnclosure 24
      (sk221LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk221LogKInput_eq :
    sk221RoundedInputs.logK = outerEnclosure 24
      (sk221LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk221LogDArgInput_eq :
    sk221RoundedInputs.logDArg = outerEnclosure 24
      (sk221LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk221RoundedFacts : SKRoundedFacts 8
    sk221LogOuterCertificate sk221LogKCertificate
    sk221LogDArgCertificate sk221RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk221LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk221LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk221LogDArgInput_eq }

noncomputable def sk222Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32) }

noncomputable def sk222LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9862693/8388608) }, upper := { exponent := 2, mantissa := (151/128) } }

noncomputable def sk222LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (237/128) }, upper := { exponent := 1, mantissa := (119/64) } }

noncomputable def sk222LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1558294413/1232207872) }, upper := { exponent := 0, mantissa := (302/237) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk222LogOuter_valid :
    sk222LogOuterCertificate.check sk222Slice.outerAD.value = true := by
  norm_num [sk222LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk222Slice,
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
private theorem sk222LogK_valid :
    sk222LogKCertificate.check sk222Slice.kAD.value = true := by
  norm_num [sk222LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk222Slice,
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
private theorem sk222LogDArg_valid :
    sk222LogDArgCertificate.check sk222Slice.dArgAD.value = true := by
  norm_num [sk222LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk222Slice,
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

theorem sk222ValidityFacts : SKFacts sk222Slice
    sk222LogOuterCertificate sk222LogKCertificate
    sk222LogDArgCertificate :=
  { domain := by norm_num [sk222Slice]
    kPositive := by
      norm_num [sk222Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk222LogOuter_valid
    logK := sk222LogK_valid
    logDArg := sk222LogDArg_valid }

noncomputable def sk222RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (25974133/16777216), upper := (26030589/16777216) }
    logK := { lower := (10982173/8388608), upper := (5508747/4194304) }
    logDArg := { lower := (3939027/16777216), upper := (2033121/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk222LogOuterInput_eq :
    sk222RoundedInputs.logOuter = outerEnclosure 24
      (sk222LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk222LogKInput_eq :
    sk222RoundedInputs.logK = outerEnclosure 24
      (sk222LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk222LogDArgInput_eq :
    sk222RoundedInputs.logDArg = outerEnclosure 24
      (sk222LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk222RoundedFacts : SKRoundedFacts 8
    sk222LogOuterCertificate sk222LogKCertificate
    sk222LogDArgCertificate sk222RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk222LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk222LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk222LogDArgInput_eq }

noncomputable def sk223Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64) }

noncomputable def sk223LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9895459/8388608) }, upper := { exponent := 2, mantissa := (303/256) } }

noncomputable def sk223LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (119/64) }, upper := { exponent := 1, mantissa := (239/128) } }

noncomputable def sk223LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4710205239/3727818752) }, upper := { exponent := 0, mantissa := (303/238) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk223LogOuter_valid :
    sk223LogOuterCertificate.check sk223Slice.outerAD.value = true := by
  norm_num [sk223LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk223Slice,
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
private theorem sk223LogK_valid :
    sk223LogKCertificate.check sk223Slice.kAD.value = true := by
  norm_num [sk223LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk223Slice,
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
private theorem sk223LogDArg_valid :
    sk223LogDArgCertificate.check sk223Slice.dArgAD.value = true := by
  norm_num [sk223LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk223Slice,
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

theorem sk223ValidityFacts : SKFacts sk223Slice
    sk223LogOuterCertificate sk223LogKCertificate
    sk223LogDArgCertificate :=
  { domain := by norm_num [sk223Slice]
    kPositive := by
      norm_num [sk223Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk223LogOuter_valid
    logK := sk223LogK_valid
    logDArg := sk223LogDArg_valid }

noncomputable def sk223RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13014889/8388608), upper := (26086051/16777216) }
    logK := { lower := (22034987/16777216), upper := (22105333/16777216) }
    logDArg := { lower := (490541/2097152), upper := (4051063/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk223LogOuterInput_eq :
    sk223RoundedInputs.logOuter = outerEnclosure 24
      (sk223LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk223LogKInput_eq :
    sk223RoundedInputs.logK = outerEnclosure 24
      (sk223LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk223LogDArgInput_eq :
    sk223RoundedInputs.logDArg = outerEnclosure 24
      (sk223LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk223RoundedFacts : SKRoundedFacts 8
    sk223LogOuterCertificate sk223LogKCertificate
    sk223LogDArgCertificate sk223RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk223LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk223LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk223LogDArgInput_eq }

noncomputable def sk224Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4) }

noncomputable def sk224LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9928225/8388608) }, upper := { exponent := 2, mantissa := (19/16) } }

noncomputable def sk224LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (239/128) }, upper := { exponent := 1, mantissa := (15/8) } }

noncomputable def sk224LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1581886101/1253048320) }, upper := { exponent := 0, mantissa := (304/239) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk224LogOuter_valid :
    sk224LogOuterCertificate.check sk224Slice.outerAD.value = true := by
  norm_num [sk224LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk224Slice,
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
private theorem sk224LogK_valid :
    sk224LogKCertificate.check sk224Slice.kAD.value = true := by
  norm_num [sk224LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk224Slice,
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
private theorem sk224LogDArg_valid :
    sk224LogDArgCertificate.check sk224Slice.dArgAD.value = true := by
  norm_num [sk224LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk224Slice,
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

theorem sk224ValidityFacts : SKFacts sk224Slice
    sk224LogOuterCertificate sk224LogKCertificate
    sk224LogDArgCertificate :=
  { domain := by norm_num [sk224Slice]
    kPositive := by
      norm_num [sk224Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk224LogOuter_valid
    logK := sk224LogK_valid
    logDArg := sk224LogDArg_valid }

noncomputable def sk224RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3260655/2097152), upper := (13070665/8388608) }
    logK := { lower := (5526333/4194304), upper := (2771923/2097152) }
    logDArg := { lower := (3909739/16777216), upper := (4035997/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk224LogOuterInput_eq :
    sk224RoundedInputs.logOuter = outerEnclosure 24
      (sk224LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk224LogKInput_eq :
    sk224RoundedInputs.logK = outerEnclosure 24
      (sk224LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk224LogDArgInput_eq :
    sk224RoundedInputs.logDArg = outerEnclosure 24
      (sk224LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk224RoundedFacts : SKRoundedFacts 8
    sk224LogOuterCertificate sk224LogKCertificate
    sk224LogDArgCertificate sk224RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk224LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk224LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk224LogDArgInput_eq }

noncomputable def sk225Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64) }

noncomputable def sk225LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9960991/8388608) }, upper := { exponent := 2, mantissa := (305/256) } }

noncomputable def sk225LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (15/8) }, upper := { exponent := 1, mantissa := (241/128) } }

noncomputable def sk225LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1593747477/1263534080) }, upper := { exponent := 0, mantissa := (61/48) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk225LogOuter_valid :
    sk225LogOuterCertificate.check sk225Slice.outerAD.value = true := by
  norm_num [sk225LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk225Slice,
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
private theorem sk225LogK_valid :
    sk225LogKCertificate.check sk225Slice.kAD.value = true := by
  norm_num [sk225LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk225Slice,
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
private theorem sk225LogDArg_valid :
    sk225LogDArgCertificate.check sk225Slice.dArgAD.value = true := by
  norm_num [sk225LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk225Slice,
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

theorem sk225ValidityFacts : SKFacts sk225Slice
    sk225LogOuterCertificate sk225LogKCertificate
    sk225LogDArgCertificate :=
  { domain := by norm_num [sk225Slice]
    kPositive := by
      norm_num [sk225Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk225LogOuter_valid
    logK := sk225LogK_valid
    logDArg := sk225LogDArg_valid }

noncomputable def sk225RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13070259/8388608), upper := (6549107/4194304) }
    logK := { lower := (22175383/16777216), upper := (2780643/2097152) }
    logDArg := { lower := (1947629/8388608), upper := (1005261/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk225LogOuterInput_eq :
    sk225RoundedInputs.logOuter = outerEnclosure 24
      (sk225LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk225LogKInput_eq :
    sk225RoundedInputs.logK = outerEnclosure 24
      (sk225LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk225LogDArgInput_eq :
    sk225RoundedInputs.logDArg = outerEnclosure 24
      (sk225LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk225RoundedFacts : SKRoundedFacts 8
    sk225LogOuterCertificate sk225LogKCertificate
    sk225LogDArgCertificate sk225RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk225LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk225LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk225LogDArgInput_eq }

noncomputable def sk226Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32) }

noncomputable def sk226LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (9993757/8388608) }, upper := { exponent := 2, mantissa := (153/128) } }

noncomputable def sk226LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (241/128) }, upper := { exponent := 1, mantissa := (121/64) } }

noncomputable def sk226LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4816957623/3822190592) }, upper := { exponent := 0, mantissa := (306/241) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk226LogOuter_valid :
    sk226LogOuterCertificate.check sk226Slice.outerAD.value = true := by
  norm_num [sk226LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk226Slice,
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
private theorem sk226LogK_valid :
    sk226LogKCertificate.check sk226Slice.kAD.value = true := by
  norm_num [sk226LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk226Slice,
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
private theorem sk226LogDArg_valid :
    sk226LogDArgCertificate.check sk226Slice.dArgAD.value = true := by
  norm_num [sk226LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk226Slice,
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

theorem sk226ValidityFacts : SKFacts sk226Slice
    sk226LogOuterCertificate sk226LogKCertificate
    sk226LogDArgCertificate :=
  { domain := by norm_num [sk226Slice]
    kPositive := by
      norm_num [sk226Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk226LogOuter_valid
    logK := sk226LogK_valid
    logDArg := sk226LogDArg_valid }

noncomputable def sk226RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26195615/16777216), upper := (26251345/16777216) }
    logK := { lower := (22245143/16777216), upper := (22314615/16777216) }
    logDArg := { lower := (3880885/16777216), upper := (4006201/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk226LogOuterInput_eq :
    sk226RoundedInputs.logOuter = outerEnclosure 24
      (sk226LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk226LogKInput_eq :
    sk226RoundedInputs.logK = outerEnclosure 24
      (sk226LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk226LogDArgInput_eq :
    sk226RoundedInputs.logDArg = outerEnclosure 24
      (sk226LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk226RoundedFacts : SKRoundedFacts 8
    sk226LogOuterCertificate sk226LogKCertificate
    sk226LogDArgCertificate sk226RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk226LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk226LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk226LogDArgInput_eq }

noncomputable def sk227Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64) }

noncomputable def sk227LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10026523/8388608) }, upper := { exponent := 2, mantissa := (307/256) } }

noncomputable def sk227LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (121/64) }, upper := { exponent := 1, mantissa := (243/128) } }

noncomputable def sk227LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (5446469/4325376) }, upper := { exponent := 0, mantissa := (307/242) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk227LogOuter_valid :
    sk227LogOuterCertificate.check sk227Slice.outerAD.value = true := by
  norm_num [sk227LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk227Slice,
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
private theorem sk227LogK_valid :
    sk227LogKCertificate.check sk227Slice.kAD.value = true := by
  norm_num [sk227LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk227Slice,
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
private theorem sk227LogDArg_valid :
    sk227LogDArgCertificate.check sk227Slice.dArgAD.value = true := by
  norm_num [sk227LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk227Slice,
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

theorem sk227ValidityFacts : SKFacts sk227Slice
    sk227LogOuterCertificate sk227LogKCertificate
    sk227LogDArgCertificate :=
  { domain := by norm_num [sk227Slice]
    kPositive := by
      norm_num [sk227Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk227LogOuter_valid
    logK := sk227LogK_valid
    logDArg := sk227LogDArg_valid }

noncomputable def sk227RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6562633/4194304), upper := (26306083/16777216) }
    logK := { lower := (11157307/8388608), upper := (22383799/16777216) }
    logDArg := { lower := (1933309/8388608), upper := (997867/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk227LogOuterInput_eq :
    sk227RoundedInputs.logOuter = outerEnclosure 24
      (sk227LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk227LogKInput_eq :
    sk227RoundedInputs.logK = outerEnclosure 24
      (sk227LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk227LogDArgInput_eq :
    sk227RoundedInputs.logDArg = outerEnclosure 24
      (sk227LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk227RoundedFacts : SKRoundedFacts 8
    sk227LogOuterCertificate sk227LogKCertificate
    sk227LogDArgCertificate sk227RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk227LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk227LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk227LogDArgInput_eq }

noncomputable def sk228Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16) }

noncomputable def sk228LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10059289/8388608) }, upper := { exponent := 2, mantissa := (77/64) } }

noncomputable def sk228LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (243/128) }, upper := { exponent := 1, mantissa := (61/32) } }

noncomputable def sk228LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (543197911/431751168) }, upper := { exponent := 0, mantissa := (308/243) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk228LogOuter_valid :
    sk228LogOuterCertificate.check sk228Slice.outerAD.value = true := by
  norm_num [sk228LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk228Slice,
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
private theorem sk228LogK_valid :
    sk228LogKCertificate.check sk228Slice.kAD.value = true := by
  norm_num [sk228LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk228Slice,
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
private theorem sk228LogDArg_valid :
    sk228LogDArgCertificate.check sk228Slice.dArgAD.value = true := by
  norm_num [sk228LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk228Slice,
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

theorem sk228ValidityFacts : SKFacts sk228Slice
    sk228LogOuterCertificate sk228LogKCertificate
    sk228LogDArgCertificate :=
  { domain := by norm_num [sk228Slice]
    kPositive := by
      norm_num [sk228Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk228LogOuter_valid
    logK := sk228LogK_valid
    logDArg := sk228LogDArg_valid }

noncomputable def sk228RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26305269/16777216), upper := (26360643/16777216) }
    logK := { lower := (11191899/8388608), upper := (5613175/4194304) }
    logDArg := { lower := (481557/2097152), upper := (994211/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk228LogOuterInput_eq :
    sk228RoundedInputs.logOuter = outerEnclosure 24
      (sk228LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk228LogKInput_eq :
    sk228RoundedInputs.logK = outerEnclosure 24
      (sk228LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk228LogDArgInput_eq :
    sk228RoundedInputs.logDArg = outerEnclosure 24
      (sk228LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk228RoundedFacts : SKRoundedFacts 8
    sk228LogOuterCertificate sk228LogKCertificate
    sk228LogDArgCertificate sk228RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk228LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk228LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk228LogDArgInput_eq }

noncomputable def sk229Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64) }

noncomputable def sk229LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10092055/8388608) }, upper := { exponent := 2, mantissa := (309/256) } }

noncomputable def sk229LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (61/32) }, upper := { exponent := 1, mantissa := (245/128) } }

noncomputable def sk229LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (4924889583/3917742080) }, upper := { exponent := 0, mantissa := (309/244) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk229LogOuter_valid :
    sk229LogOuterCertificate.check sk229Slice.outerAD.value = true := by
  norm_num [sk229LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk229Slice,
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
private theorem sk229LogK_valid :
    sk229LogKCertificate.check sk229Slice.kAD.value = true := by
  norm_num [sk229LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk229Slice,
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
private theorem sk229LogDArg_valid :
    sk229LogDArgCertificate.check sk229Slice.dArgAD.value = true := by
  norm_num [sk229LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk229Slice,
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

theorem sk229ValidityFacts : SKFacts sk229Slice
    sk229LogOuterCertificate sk229LogKCertificate
    sk229LogDArgCertificate :=
  { domain := by norm_num [sk229Slice]
    kPositive := by
      norm_num [sk229Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk229LogOuter_valid
    logK := sk229LogK_valid
    logDArg := sk229LogDArg_valid }

noncomputable def sk229RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26359829/16777216), upper := (13207513/8388608) }
    logK := { lower := (11226349/8388608), upper := (11260659/8388608) }
    logDArg := { lower := (1919199/8388608), upper := (3962327/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk229LogOuterInput_eq :
    sk229RoundedInputs.logOuter = outerEnclosure 24
      (sk229LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk229LogKInput_eq :
    sk229RoundedInputs.logK = outerEnclosure 24
      (sk229LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk229LogDArgInput_eq :
    sk229RoundedInputs.logDArg = outerEnclosure 24
      (sk229LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk229RoundedFacts : SKRoundedFacts 8
    sk229LogOuterCertificate sk229LogKCertificate
    sk229LogDArgCertificate sk229RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk229LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk229LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk229LogDArgInput_eq }

noncomputable def sk230Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32) }

noncomputable def sk230LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10124821/8388608) }, upper := { exponent := 2, mantissa := (155/128) } }

noncomputable def sk230LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (245/128) }, upper := { exponent := 1, mantissa := (123/64) } }

noncomputable def sk230LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1653709677/1316618240) }, upper := { exponent := 0, mantissa := (62/49) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk230LogOuter_valid :
    sk230LogOuterCertificate.check sk230Slice.outerAD.value = true := by
  norm_num [sk230LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk230Slice,
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
private theorem sk230LogK_valid :
    sk230LogKCertificate.check sk230Slice.kAD.value = true := by
  norm_num [sk230LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk230Slice,
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
private theorem sk230LogDArg_valid :
    sk230LogDArgCertificate.check sk230Slice.dArgAD.value = true := by
  norm_num [sk230LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk230Slice,
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

theorem sk230ValidityFacts : SKFacts sk230Slice
    sk230LogOuterCertificate sk230LogKCertificate
    sk230LogDArgCertificate :=
  { domain := by norm_num [sk230Slice]
    kPositive := by
      norm_num [sk230Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk230LogOuter_valid
    logK := sk230LogK_valid
    logDArg := sk230LogDArg_valid }

noncomputable def sk230RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26414211/16777216), upper := (13234617/8388608) }
    logK := { lower := (22521317/16777216), upper := (22589657/16777216) }
    logDArg := { lower := (1912221/8388608), upper := (986979/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk230LogOuterInput_eq :
    sk230RoundedInputs.logOuter = outerEnclosure 24
      (sk230LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk230LogKInput_eq :
    sk230RoundedInputs.logK = outerEnclosure 24
      (sk230LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk230LogDArgInput_eq :
    sk230RoundedInputs.logDArg = outerEnclosure 24
      (sk230LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk230RoundedFacts : SKRoundedFacts 8
    sk230LogOuterCertificate sk230LogKCertificate
    sk230LogDArgCertificate sk230RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk230LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk230LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk230LogDArgInput_eq }

noncomputable def sk231Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64) }

noncomputable def sk231LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10157587/8388608) }, upper := { exponent := 2, mantissa := (311/256) } }

noncomputable def sk231LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (123/64) }, upper := { exponent := 1, mantissa := (247/128) } }

noncomputable def sk231LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1665833181/1327366144) }, upper := { exponent := 0, mantissa := (311/246) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk231LogOuter_valid :
    sk231LogOuterCertificate.check sk231Slice.outerAD.value = true := by
  norm_num [sk231LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk231Slice,
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
private theorem sk231LogK_valid :
    sk231LogKCertificate.check sk231Slice.kAD.value = true := by
  norm_num [sk231LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk231Slice,
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
private theorem sk231LogDArg_valid :
    sk231LogDArgCertificate.check sk231Slice.dArgAD.value = true := by
  norm_num [sk231LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk231Slice,
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

theorem sk231ValidityFacts : SKFacts sk231Slice
    sk231LogOuterCertificate sk231LogKCertificate
    sk231LogDArgCertificate :=
  { domain := by norm_num [sk231Slice]
    kPositive := by
      norm_num [sk231Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk231LogOuter_valid
    logK := sk231LogK_valid
    logDArg := sk231LogDArg_valid }

noncomputable def sk231RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13234209/8388608), upper := (26523267/16777216) }
    logK := { lower := (2823707/2097152), upper := (22657719/16777216) }
    logDArg := { lower := (952647/4194304), upper := (1966805/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk231LogOuterInput_eq :
    sk231RoundedInputs.logOuter = outerEnclosure 24
      (sk231LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk231LogKInput_eq :
    sk231RoundedInputs.logK = outerEnclosure 24
      (sk231LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk231LogDArgInput_eq :
    sk231RoundedInputs.logDArg = outerEnclosure 24
      (sk231LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk231RoundedFacts : SKRoundedFacts 8
    sk231LogOuterCertificate sk231LogKCertificate
    sk231LogDArgCertificate sk231RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk231LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk231LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk231LogDArgInput_eq }

noncomputable def sk232Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8) }

noncomputable def sk232LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10190353/8388608) }, upper := { exponent := 2, mantissa := (39/32) } }

noncomputable def sk232LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (247/128) }, upper := { exponent := 1, mantissa := (31/16) } }

noncomputable def sk232LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (5034001119/4014473216) }, upper := { exponent := 0, mantissa := (24/19) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk232LogOuter_valid :
    sk232LogOuterCertificate.check sk232Slice.outerAD.value = true := by
  norm_num [sk232LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk232Slice,
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
private theorem sk232LogK_valid :
    sk232LogKCertificate.check sk232Slice.kAD.value = true := by
  norm_num [sk232LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk232Slice,
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
private theorem sk232LogDArg_valid :
    sk232LogDArgCertificate.check sk232Slice.dArgAD.value = true := by
  norm_num [sk232LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk232Slice,
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

theorem sk232ValidityFacts : SKFacts sk232Slice
    sk232LogOuterCertificate sk232LogKCertificate
    sk232LogDArgCertificate :=
  { domain := by norm_num [sk232Slice]
    kPositive := by
      norm_num [sk232Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk232LogOuter_valid
    logK := sk232LogK_valid
    logDArg := sk232LogDArg_valid }

noncomputable def sk232RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13261225/8388608), upper := (13288563/8388608) }
    logK := { lower := (11328859/8388608), upper := (11362753/8388608) }
    logDArg := { lower := (1898417/8388608), upper := (3919407/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk232LogOuterInput_eq :
    sk232RoundedInputs.logOuter = outerEnclosure 24
      (sk232LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk232LogKInput_eq :
    sk232RoundedInputs.logK = outerEnclosure 24
      (sk232LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk232LogDArgInput_eq :
    sk232RoundedInputs.logDArg = outerEnclosure 24
      (sk232LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk232RoundedFacts : SKRoundedFacts 8
    sk232LogOuterCertificate sk232LogKCertificate
    sk232LogDArgCertificate sk232RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk232LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk232LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk232LogDArgInput_eq }

noncomputable def sk233Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64) }

noncomputable def sk233LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10223119/8388608) }, upper := { exponent := 2, mantissa := (313/256) } }

noncomputable def sk233LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (31/16) }, upper := { exponent := 1, mantissa := (249/128) } }

noncomputable def sk233LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (20363991/16252928) }, upper := { exponent := 0, mantissa := (313/248) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk233LogOuter_valid :
    sk233LogOuterCertificate.check sk233Slice.outerAD.value = true := by
  norm_num [sk233LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk233Slice,
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
private theorem sk233LogK_valid :
    sk233LogKCertificate.check sk233Slice.kAD.value = true := by
  norm_num [sk233LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk233Slice,
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
private theorem sk233LogDArg_valid :
    sk233LogDArgCertificate.check sk233Slice.dArgAD.value = true := by
  norm_num [sk233LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk233Slice,
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

theorem sk233ValidityFacts : SKFacts sk233Slice
    sk233LogOuterCertificate sk233LogKCertificate
    sk233LogDArgCertificate :=
  { domain := by norm_num [sk233Slice]
    kPositive := by
      norm_num [sk233Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk233LogOuter_valid
    logK := sk233LogK_valid
    logDArg := sk233LogDArg_valid }

noncomputable def sk233RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26576309/16777216), upper := (26630813/16777216) }
    logK := { lower := (22725505/16777216), upper := (5698255/4194304) }
    logDArg := { lower := (945795/4194304), upper := (976327/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk233LogOuterInput_eq :
    sk233RoundedInputs.logOuter = outerEnclosure 24
      (sk233LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk233LogKInput_eq :
    sk233RoundedInputs.logK = outerEnclosure 24
      (sk233LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk233LogDArgInput_eq :
    sk233RoundedInputs.logDArg = outerEnclosure 24
      (sk233LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk233RoundedFacts : SKRoundedFacts 8
    sk233LogOuterCertificate sk233LogKCertificate
    sk233LogDArgCertificate sk233RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk233LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk233LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk233LogDArgInput_eq }

noncomputable def sk234Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32) }

noncomputable def sk234LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10255885/8388608) }, upper := { exponent := 2, mantissa := (157/128) } }

noncomputable def sk234LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (249/128) }, upper := { exponent := 1, mantissa := (125/64) } }

noncomputable def sk234LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1702465821/1359872000) }, upper := { exponent := 0, mantissa := (314/249) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk234LogOuter_valid :
    sk234LogOuterCertificate.check sk234Slice.outerAD.value = true := by
  norm_num [sk234LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk234Slice,
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
private theorem sk234LogK_valid :
    sk234LogKCertificate.check sk234Slice.kAD.value = true := by
  norm_num [sk234LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk234Slice,
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
private theorem sk234LogDArg_valid :
    sk234LogDArgCertificate.check sk234Slice.dArgAD.value = true := by
  norm_num [sk234LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk234Slice,
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

theorem sk234ValidityFacts : SKFacts sk234Slice
    sk234LogOuterCertificate sk234LogKCertificate
    sk234LogDArgCertificate :=
  { domain := by norm_num [sk234Slice]
    kPositive := by
      norm_num [sk234Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk234LogOuter_valid
    logK := sk234LogK_valid
    logDArg := sk234LogDArg_valid }

noncomputable def sk234RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26629995/16777216), upper := (26684329/16777216) }
    logK := { lower := (22793019/16777216), upper := (2857533/2097152) }
    logDArg := { lower := (471203/2097152), upper := (3891309/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk234LogOuterInput_eq :
    sk234RoundedInputs.logOuter = outerEnclosure 24
      (sk234LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk234LogKInput_eq :
    sk234RoundedInputs.logK = outerEnclosure 24
      (sk234LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk234LogDArgInput_eq :
    sk234RoundedInputs.logDArg = outerEnclosure 24
      (sk234LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk234RoundedFacts : SKRoundedFacts 8
    sk234LogOuterCertificate sk234LogKCertificate
    sk234LogDArgCertificate sk234RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk234LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk234LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk234LogDArgInput_eq }

noncomputable def sk235Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64) }

noncomputable def sk235LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10288651/8388608) }, upper := { exponent := 2, mantissa := (315/256) } }

noncomputable def sk235LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (125/64) }, upper := { exponent := 1, mantissa := (251/128) } }

noncomputable def sk235LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (5144292231/4112384000) }, upper := { exponent := 0, mantissa := (63/50) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk235LogOuter_valid :
    sk235LogOuterCertificate.check sk235Slice.outerAD.value = true := by
  norm_num [sk235LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk235Slice,
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
private theorem sk235LogK_valid :
    sk235LogKCertificate.check sk235Slice.kAD.value = true := by
  norm_num [sk235LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk235Slice,
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
private theorem sk235LogDArg_valid :
    sk235LogDArgCertificate.check sk235Slice.dArgAD.value = true := by
  norm_num [sk235LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk235Slice,
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

theorem sk235ValidityFacts : SKFacts sk235Slice
    sk235LogOuterCertificate sk235LogKCertificate
    sk235LogDArgCertificate :=
  { domain := by norm_num [sk235Slice]
    kPositive := by
      norm_num [sk235Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk235LogOuter_valid
    logK := sk235LogK_valid
    logDArg := sk235LogDArg_valid }

noncomputable def sk235RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26683511/16777216), upper := (26737675/16777216) }
    logK := { lower := (11430131/8388608), upper := (22927239/16777216) }
    logDArg := { lower := (3756165/16777216), upper := (969353/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk235LogOuterInput_eq :
    sk235RoundedInputs.logOuter = outerEnclosure 24
      (sk235LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk235LogKInput_eq :
    sk235RoundedInputs.logK = outerEnclosure 24
      (sk235LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk235LogDArgInput_eq :
    sk235RoundedInputs.logDArg = outerEnclosure 24
      (sk235LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk235RoundedFacts : SKRoundedFacts 8
    sk235LogOuterCertificate sk235LogKCertificate
    sk235LogDArgCertificate sk235RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk235LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk235LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk235LogDArgInput_eq }

noncomputable def sk236Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16) }

noncomputable def sk236LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10321417/8388608) }, upper := { exponent := 2, mantissa := (79/64) } }

noncomputable def sk236LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (251/128) }, upper := { exponent := 1, mantissa := (63/32) } }

noncomputable def sk236LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (575702007/460587008) }, upper := { exponent := 0, mantissa := (316/251) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk236LogOuter_valid :
    sk236LogOuterCertificate.check sk236Slice.outerAD.value = true := by
  norm_num [sk236LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk236Slice,
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
private theorem sk236LogK_valid :
    sk236LogKCertificate.check sk236Slice.kAD.value = true := by
  norm_num [sk236LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk236Slice,
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
private theorem sk236LogDArg_valid :
    sk236LogDArgCertificate.check sk236Slice.dArgAD.value = true := by
  norm_num [sk236LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk236Slice,
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

theorem sk236ValidityFacts : SKFacts sk236Slice
    sk236LogOuterCertificate sk236LogKCertificate
    sk236LogDArgCertificate :=
  { domain := by norm_num [sk236Slice]
    kPositive := by
      norm_num [sk236Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk236LogOuter_valid
    logK := sk236LogK_valid
    logDArg := sk236LogDArg_valid }

noncomputable def sk236RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (3342107/2097152), upper := (6697713/4194304) }
    logK := { lower := (22927237/16777216), upper := (22993947/16777216) }
    logDArg := { lower := (1871401/8388608), upper := (3863613/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk236LogOuterInput_eq :
    sk236RoundedInputs.logOuter = outerEnclosure 24
      (sk236LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk236LogKInput_eq :
    sk236RoundedInputs.logK = outerEnclosure 24
      (sk236LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk236LogDArgInput_eq :
    sk236RoundedInputs.logDArg = outerEnclosure 24
      (sk236LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk236RoundedFacts : SKRoundedFacts 8
    sk236LogOuterCertificate sk236LogKCertificate
    sk236LogDArgCertificate sk236RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk236LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk236LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk236LogDArgInput_eq }

noncomputable def sk237Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64) }

noncomputable def sk237LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10354183/8388608) }, upper := { exponent := 2, mantissa := (317/256) } }

noncomputable def sk237LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (63/32) }, upper := { exponent := 1, mantissa := (253/128) } }

noncomputable def sk237LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (579830551/464257024) }, upper := { exponent := 0, mantissa := (317/252) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk237LogOuter_valid :
    sk237LogOuterCertificate.check sk237Slice.outerAD.value = true := by
  norm_num [sk237LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk237Slice,
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
private theorem sk237LogK_valid :
    sk237LogKCertificate.check sk237Slice.kAD.value = true := by
  norm_num [sk237LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk237Slice,
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
private theorem sk237LogDArg_valid :
    sk237LogDArgCertificate.check sk237Slice.dArgAD.value = true := by
  norm_num [sk237LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk237Slice,
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

theorem sk237ValidityFacts : SKFacts sk237Slice
    sk237LogOuterCertificate sk237LogKCertificate
    sk237LogDArgCertificate :=
  { domain := by norm_num [sk237Slice]
    kPositive := by
      norm_num [sk237Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk237LogOuter_valid
    logK := sk237LogK_valid
    logDArg := sk237LogDArg_valid }

noncomputable def sk237RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1674377/1048576), upper := (6710965/4194304) }
    logK := { lower := (11496973/8388608), upper := (2882549/2097152) }
    logDArg := { lower := (1864767/8388608), upper := (3849913/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk237LogOuterInput_eq :
    sk237RoundedInputs.logOuter = outerEnclosure 24
      (sk237LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk237LogKInput_eq :
    sk237RoundedInputs.logK = outerEnclosure 24
      (sk237LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk237LogDArgInput_eq :
    sk237RoundedInputs.logDArg = outerEnclosure 24
      (sk237LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk237RoundedFacts : SKRoundedFacts 8
    sk237LogOuterCertificate sk237LogKCertificate
    sk237LogDArgCertificate sk237RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk237LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk237LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk237LogDArgInput_eq }

noncomputable def sk238Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32) }

noncomputable def sk238LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10386949/8388608) }, upper := { exponent := 2, mantissa := (159/128) } }

noncomputable def sk238LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (253/128) }, upper := { exponent := 1, mantissa := (127/64) } }

noncomputable def sk238LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (477796629/382861312) }, upper := { exponent := 0, mantissa := (318/253) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk238LogOuter_valid :
    sk238LogOuterCertificate.check sk238Slice.outerAD.value = true := by
  norm_num [sk238LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk238Slice,
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
private theorem sk238LogK_valid :
    sk238LogKCertificate.check sk238Slice.kAD.value = true := by
  norm_num [sk238LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk238Slice,
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
private theorem sk238LogDArg_valid :
    sk238LogDArgCertificate.check sk238Slice.dArgAD.value = true := by
  norm_num [sk238LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk238Slice,
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

theorem sk238ValidityFacts : SKFacts sk238Slice
    sk238LogOuterCertificate sk238LogKCertificate
    sk238LogDArgCertificate :=
  { domain := by norm_num [sk238Slice]
    kPositive := by
      norm_num [sk238Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk238LogOuter_valid
    logK := sk238LogK_valid
    logDArg := sk238LogDArg_valid }

noncomputable def sk238RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (838845/524288), upper := (13448351/8388608) }
    logK := { lower := (11530195/8388608), upper := (11563287/8388608) }
    logDArg := { lower := (464545/2097152), upper := (1918155/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk238LogOuterInput_eq :
    sk238RoundedInputs.logOuter = outerEnclosure 24
      (sk238LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk238LogKInput_eq :
    sk238RoundedInputs.logK = outerEnclosure 24
      (sk238LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk238LogDArgInput_eq :
    sk238RoundedInputs.logDArg = outerEnclosure 24
      (sk238LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk238RoundedFacts : SKRoundedFacts 8
    sk238LogOuterCertificate sk238LogKCertificate
    sk238LogDArgCertificate sk238RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk238LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk238LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk238LogDArgInput_eq }

noncomputable def sk239Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64) }

noncomputable def sk239LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10419715/8388608) }, upper := { exponent := 2, mantissa := (319/256) } }

noncomputable def sk239LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (127/64) }, upper := { exponent := 1, mantissa := (255/128) } }

noncomputable def sk239LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1764393981/1414922240) }, upper := { exponent := 0, mantissa := (319/254) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk239LogOuter_valid :
    sk239LogOuterCertificate.check sk239Slice.outerAD.value = true := by
  norm_num [sk239LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk239Slice,
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
private theorem sk239LogK_valid :
    sk239LogKCertificate.check sk239Slice.kAD.value = true := by
  norm_num [sk239LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk239Slice,
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
private theorem sk239LogDArg_valid :
    sk239LogDArgCertificate.check sk239Slice.dArgAD.value = true := by
  norm_num [sk239LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk239Slice,
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

theorem sk239ValidityFacts : SKFacts sk239Slice
    sk239LogOuterCertificate sk239LogKCertificate
    sk239LogDArgCertificate :=
  { domain := by norm_num [sk239Slice]
    kPositive := by
      norm_num [sk239Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk239LogOuter_valid
    logK := sk239LogK_valid
    logDArg := sk239LogDArg_valid }

noncomputable def sk239RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26895881/16777216), upper := (13474689/8388608) }
    logK := { lower := (23126573/16777216), upper := (23192497/16777216) }
    logDArg := { lower := (231455/1048576), upper := (955701/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk239LogOuterInput_eq :
    sk239RoundedInputs.logOuter = outerEnclosure 24
      (sk239LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk239LogKInput_eq :
    sk239RoundedInputs.logK = outerEnclosure 24
      (sk239LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk239LogDArgInput_eq :
    sk239RoundedInputs.logDArg = outerEnclosure 24
      (sk239LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk239RoundedFacts : SKRoundedFacts 8
    sk239LogOuterCertificate sk239LogKCertificate
    sk239LogDArgCertificate sk239RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk239LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk239LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk239LogDArgInput_eq }

noncomputable def sk240Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4) }

noncomputable def sk240LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (10452481/8388608) }, upper := { exponent := 2, mantissa := (5/4) } }

noncomputable def sk240LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (255/128) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk240LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1776910677/1426063360) }, upper := { exponent := 0, mantissa := (64/51) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk240LogOuter_valid :
    sk240LogOuterCertificate.check sk240Slice.outerAD.value = true := by
  norm_num [sk240LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk240Slice,
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
private theorem sk240LogK_valid :
    sk240LogKCertificate.check sk240Slice.kAD.value = true := by
  norm_num [sk240LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk240Slice,
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
private theorem sk240LogDArg_valid :
    sk240LogDArgCertificate.check sk240Slice.dArgAD.value = true := by
  norm_num [sk240LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk240Slice,
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

theorem sk240ValidityFacts : SKFacts sk240Slice
    sk240LogOuterCertificate sk240LogKCertificate
    sk240LogDArgCertificate :=
  { domain := by norm_num [sk240Slice]
    kPositive := by
      norm_num [sk240Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk240LogOuter_valid
    logK := sk240LogK_valid
    logDArg := sk240LogDArg_valid }

noncomputable def sk240RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (6737139/4194304), upper := (27001889/16777216) }
    logK := { lower := (23192495/16777216), upper := (23258161/16777216) }
    logDArg := { lower := (3690291/16777216), upper := (238087/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk240LogOuterInput_eq :
    sk240RoundedInputs.logOuter = outerEnclosure 24
      (sk240LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk240LogKInput_eq :
    sk240RoundedInputs.logK = outerEnclosure 24
      (sk240LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk240LogDArgInput_eq :
    sk240RoundedInputs.logDArg = outerEnclosure 24
      (sk240LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk240RoundedFacts : SKRoundedFacts 8
    sk240LogOuterCertificate sk240LogKCertificate
    sk240LogDArgCertificate sk240RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk240LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk240LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk240LogDArgInput_eq }

noncomputable def sk241Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (503/128) }

noncomputable def sk241LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20642835/16777216) }, upper := { exponent := 2, mantissa := (631/512) } }

noncomputable def sk241LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (251/128) }, upper := { exponent := 1, mantissa := (503/256) } }

noncomputable def sk241LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (20725372567/16548233216) }, upper := { exponent := 0, mantissa := (631/502) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk241LogOuter_valid :
    sk241LogOuterCertificate.check sk241Slice.outerAD.value = true := by
  norm_num [sk241LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk241Slice,
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
private theorem sk241LogK_valid :
    sk241LogKCertificate.check sk241Slice.kAD.value = true := by
  norm_num [sk241LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk241Slice,
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
private theorem sk241LogDArg_valid :
    sk241LogDArgCertificate.check sk241Slice.dArgAD.value = true := by
  norm_num [sk241LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk241Slice,
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

theorem sk241ValidityFacts : SKFacts sk241Slice
    sk241LogOuterCertificate sk241LogKCertificate
    sk241LogDArgCertificate :=
  { domain := by norm_num [sk241Slice]
    kPositive := by
      norm_num [sk241Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk241LogOuter_valid
    logK := sk241LogK_valid
    logDArg := sk241LogDArg_valid }

noncomputable def sk241RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26736857/16777216), upper := (6691071/4194304) }
    logK := { lower := (22927237/16777216), upper := (11480313/8388608) }
    logDArg := { lower := (944051/4194304), upper := (1918523/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk241LogOuterInput_eq :
    sk241RoundedInputs.logOuter = outerEnclosure 24
      (sk241LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk241LogKInput_eq :
    sk241RoundedInputs.logK = outerEnclosure 24
      (sk241LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk241LogDArgInput_eq :
    sk241RoundedInputs.logDArg = outerEnclosure 24
      (sk241LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk241RoundedFacts : SKRoundedFacts 8
    sk241LogOuterCertificate sk241LogKCertificate
    sk241LogDArgCertificate sk241RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk241LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk241LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk241LogDArgInput_eq }

noncomputable def sk242Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (503/128), kHi := (63/16) }

noncomputable def sk242LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20675601/16777216) }, upper := { exponent := 2, mantissa := (79/64) } }

noncomputable def sk242LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (503/256) }, upper := { exponent := 1, mantissa := (63/32) } }

noncomputable def sk242LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (20799620831/16614162432) }, upper := { exponent := 0, mantissa := (632/503) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk242LogOuter_valid :
    sk242LogOuterCertificate.check sk242Slice.outerAD.value = true := by
  norm_num [sk242LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk242Slice,
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
private theorem sk242LogK_valid :
    sk242LogKCertificate.check sk242Slice.kAD.value = true := by
  norm_num [sk242LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk242Slice,
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
private theorem sk242LogDArg_valid :
    sk242LogDArgCertificate.check sk242Slice.dArgAD.value = true := by
  norm_num [sk242LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk242Slice,
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

theorem sk242ValidityFacts : SKFacts sk242Slice
    sk242LogOuterCertificate sk242LogKCertificate
    sk242LogDArgCertificate :=
  { domain := by norm_num [sk242Slice]
    kPositive := by
      norm_num [sk242Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk242LogOuter_valid
    logK := sk242LogK_valid
    logDArg := sk242LogDArg_valid }

noncomputable def sk242RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13381733/8388608), upper := (6697713/4194304) }
    logK := { lower := (22960625/16777216), upper := (22993947/16777216) }
    logDArg := { lower := (942373/4194304), upper := (1915113/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk242LogOuterInput_eq :
    sk242RoundedInputs.logOuter = outerEnclosure 24
      (sk242LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk242LogKInput_eq :
    sk242RoundedInputs.logK = outerEnclosure 24
      (sk242LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk242LogDArgInput_eq :
    sk242RoundedInputs.logDArg = outerEnclosure 24
      (sk242LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk242RoundedFacts : SKRoundedFacts 8
    sk242LogOuterCertificate sk242LogKCertificate
    sk242LogDArgCertificate sk242RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk242LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk242LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk242LogDArgInput_eq }

noncomputable def sk243Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (505/128) }

noncomputable def sk243LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20708367/16777216) }, upper := { exponent := 2, mantissa := (633/512) } }

noncomputable def sk243LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (63/32) }, upper := { exponent := 1, mantissa := (505/256) } }

noncomputable def sk243LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (2319333351/1853358080) }, upper := { exponent := 0, mantissa := (211/168) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk243LogOuter_valid :
    sk243LogOuterCertificate.check sk243Slice.outerAD.value = true := by
  norm_num [sk243LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk243Slice,
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
private theorem sk243LogK_valid :
    sk243LogKCertificate.check sk243Slice.kAD.value = true := by
  norm_num [sk243LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk243Slice,
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
private theorem sk243LogDArg_valid :
    sk243LogDArgCertificate.check sk243Slice.dArgAD.value = true := by
  norm_num [sk243LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk243Slice,
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

theorem sk243ValidityFacts : SKFacts sk243Slice
    sk243LogOuterCertificate sk243LogKCertificate
    sk243LogDArgCertificate :=
  { domain := by norm_num [sk243Slice]
    kPositive := by
      norm_num [sk243Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk243LogOuter_valid
    logK := sk243LogK_valid
    logDArg := sk243LogDArg_valid }

noncomputable def sk243RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26790033/16777216), upper := (26817377/16777216) }
    logK := { lower := (11496973/8388608), upper := (11513601/8388608) }
    logDArg := { lower := (940701/4194304), upper := (1911715/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk243LogOuterInput_eq :
    sk243RoundedInputs.logOuter = outerEnclosure 24
      (sk243LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk243LogKInput_eq :
    sk243RoundedInputs.logK = outerEnclosure 24
      (sk243LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk243LogDArgInput_eq :
    sk243RoundedInputs.logDArg = outerEnclosure 24
      (sk243LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk243RoundedFacts : SKRoundedFacts 8
    sk243LogOuterCertificate sk243LogKCertificate
    sk243LogDArgCertificate sk243RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk243LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk243LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk243LogDArgInput_eq }

noncomputable def sk244Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (505/128), kHi := (253/64) }

noncomputable def sk244LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20741133/16777216) }, upper := { exponent := 2, mantissa := (317/256) } }

noncomputable def sk244LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (505/256) }, upper := { exponent := 1, mantissa := (253/128) } }

noncomputable def sk244LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (20948510551/16746414080) }, upper := { exponent := 0, mantissa := (634/505) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk244LogOuter_valid :
    sk244LogOuterCertificate.check sk244Slice.outerAD.value = true := by
  norm_num [sk244LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk244Slice,
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
private theorem sk244LogK_valid :
    sk244LogKCertificate.check sk244Slice.kAD.value = true := by
  norm_num [sk244LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk244Slice,
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
private theorem sk244LogDArg_valid :
    sk244LogDArgCertificate.check sk244Slice.dArgAD.value = true := by
  norm_num [sk244LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk244Slice,
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

theorem sk244ValidityFacts : SKFacts sk244Slice
    sk244LogOuterCertificate sk244LogKCertificate
    sk244LogDArgCertificate :=
  { domain := by norm_num [sk244Slice]
    kPositive := by
      norm_num [sk244Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk244LogOuter_valid
    logK := sk244LogK_valid
    logDArg := sk244LogDArg_valid }

noncomputable def sk244RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26816557/16777216), upper := (6710965/4194304) }
    logK := { lower := (23027201/16777216), upper := (2882549/2097152) }
    logDArg := { lower := (939035/4194304), upper := (1908329/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk244LogOuterInput_eq :
    sk244RoundedInputs.logOuter = outerEnclosure 24
      (sk244LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk244LogKInput_eq :
    sk244RoundedInputs.logK = outerEnclosure 24
      (sk244LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk244LogDArgInput_eq :
    sk244RoundedInputs.logDArg = outerEnclosure 24
      (sk244LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk244RoundedFacts : SKRoundedFacts 8
    sk244LogOuterCertificate sk244LogKCertificate
    sk244LogDArgCertificate sk244RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk244LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk244LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk244LogDArgInput_eq }

noncomputable def sk245Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (507/128) }

noncomputable def sk245LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20773899/16777216) }, upper := { exponent := 2, mantissa := (635/512) } }

noncomputable def sk245LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (253/128) }, upper := { exponent := 1, mantissa := (507/256) } }

noncomputable def sk245LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (147015049/117571584) }, upper := { exponent := 0, mantissa := (635/506) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk245LogOuter_valid :
    sk245LogOuterCertificate.check sk245Slice.outerAD.value = true := by
  norm_num [sk245LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk245Slice,
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
private theorem sk245LogK_valid :
    sk245LogKCertificate.check sk245Slice.kAD.value = true := by
  norm_num [sk245LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk245Slice,
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
private theorem sk245LogDArg_valid :
    sk245LogDArgCertificate.check sk245Slice.dArgAD.value = true := by
  norm_num [sk245LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk245Slice,
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

theorem sk245ValidityFacts : SKFacts sk245Slice
    sk245LogOuterCertificate sk245LogKCertificate
    sk245LogDArgCertificate :=
  { domain := by norm_num [sk245Slice]
    kPositive := by
      norm_num [sk245Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk245LogOuter_valid
    logK := sk245LogK_valid
    logDArg := sk245LogDArg_valid }

noncomputable def sk245RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26843041/16777216), upper := (13435151/8388608) }
    logK := { lower := (11530195/8388608), upper := (5773379/4194304) }
    logDArg := { lower := (3749499/16777216), upper := (1904955/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk245LogOuterInput_eq :
    sk245RoundedInputs.logOuter = outerEnclosure 24
      (sk245LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk245LogKInput_eq :
    sk245RoundedInputs.logK = outerEnclosure 24
      (sk245LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk245LogDArgInput_eq :
    sk245RoundedInputs.logDArg = outerEnclosure 24
      (sk245LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk245RoundedFacts : SKRoundedFacts 8
    sk245LogOuterCertificate sk245LogKCertificate
    sk245LogDArgCertificate sk245RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk245LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk245LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk245LogDArgInput_eq }

noncomputable def sk246Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (507/128), kHi := (127/32) }

noncomputable def sk246LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20806665/16777216) }, upper := { exponent := 2, mantissa := (159/128) } }

noncomputable def sk246LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (507/256) }, upper := { exponent := 1, mantissa := (127/64) } }

noncomputable def sk246LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (7032641509/5626396672) }, upper := { exponent := 0, mantissa := (212/169) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk246LogOuter_valid :
    sk246LogOuterCertificate.check sk246Slice.outerAD.value = true := by
  norm_num [sk246LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk246Slice,
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
private theorem sk246LogK_valid :
    sk246LogKCertificate.check sk246Slice.kAD.value = true := by
  norm_num [sk246LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk246Slice,
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
private theorem sk246LogDArg_valid :
    sk246LogDArgCertificate.check sk246Slice.dArgAD.value = true := by
  norm_num [sk246LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk246Slice,
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

theorem sk246ValidityFacts : SKFacts sk246Slice
    sk246LogOuterCertificate sk246LogKCertificate
    sk246LogDArgCertificate :=
  { domain := by norm_num [sk246Slice]
    kPositive := by
      norm_num [sk246Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk246LogOuter_valid
    logK := sk246LogK_valid
    logDArg := sk246LogDArg_valid }

noncomputable def sk246RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13434741/8388608), upper := (13448351/8388608) }
    logK := { lower := (11546757/8388608), upper := (11563287/8388608) }
    logDArg := { lower := (1871441/8388608), upper := (3803187/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk246LogOuterInput_eq :
    sk246RoundedInputs.logOuter = outerEnclosure 24
      (sk246LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk246LogKInput_eq :
    sk246RoundedInputs.logK = outerEnclosure 24
      (sk246LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk246LogDArgInput_eq :
    sk246RoundedInputs.logDArg = outerEnclosure 24
      (sk246LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk246RoundedFacts : SKRoundedFacts 8
    sk246LogOuterCertificate sk246LogKCertificate
    sk246LogDArgCertificate sk246RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk246LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk246LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk246LogDArgInput_eq }

noncomputable def sk247Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (509/128) }

noncomputable def sk247LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20839431/16777216) }, upper := { exponent := 2, mantissa := (637/512) } }

noncomputable def sk247LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (127/64) }, upper := { exponent := 1, mantissa := (509/256) } }

noncomputable def sk247LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (21172828111/16945774592) }, upper := { exponent := 0, mantissa := (637/508) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk247LogOuter_valid :
    sk247LogOuterCertificate.check sk247Slice.outerAD.value = true := by
  norm_num [sk247LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk247Slice,
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
private theorem sk247LogK_valid :
    sk247LogKCertificate.check sk247Slice.kAD.value = true := by
  norm_num [sk247LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk247Slice,
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
private theorem sk247LogDArg_valid :
    sk247LogDArgCertificate.check sk247Slice.dArgAD.value = true := by
  norm_num [sk247LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk247Slice,
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

theorem sk247ValidityFacts : SKFacts sk247Slice
    sk247LogOuterCertificate sk247LogKCertificate
    sk247LogDArgCertificate :=
  { domain := by norm_num [sk247Slice]
    kPositive := by
      norm_num [sk247Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk247LogOuter_valid
    logK := sk247LogK_valid
    logDArg := sk247LogDArg_valid }

noncomputable def sk247RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (13447941/8388608), upper := (6730765/4194304) }
    logK := { lower := (23126573/16777216), upper := (1447473/1048576) }
    logDArg := { lower := (116759/524288), upper := (3796487/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk247LogOuterInput_eq :
    sk247RoundedInputs.logOuter = outerEnclosure 24
      (sk247LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk247LogKInput_eq :
    sk247RoundedInputs.logK = outerEnclosure 24
      (sk247LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk247LogDArgInput_eq :
    sk247RoundedInputs.logDArg = outerEnclosure 24
      (sk247LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk247RoundedFacts : SKRoundedFacts 8
    sk247LogOuterCertificate sk247LogKCertificate
    sk247LogDArgCertificate sk247RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk247LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk247LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk247LogDArgInput_eq }

noncomputable def sk248Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (509/128), kHi := (255/64) }

noncomputable def sk248LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20872197/16777216) }, upper := { exponent := 2, mantissa := (319/256) } }

noncomputable def sk248LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (509/256) }, upper := { exponent := 1, mantissa := (255/128) } }

noncomputable def sk248LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (21247862759/17012490240) }, upper := { exponent := 0, mantissa := (638/509) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk248LogOuter_valid :
    sk248LogOuterCertificate.check sk248Slice.outerAD.value = true := by
  norm_num [sk248LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk248Slice,
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
private theorem sk248LogK_valid :
    sk248LogKCertificate.check sk248Slice.kAD.value = true := by
  norm_num [sk248LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk248Slice,
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
private theorem sk248LogDArg_valid :
    sk248LogDArgCertificate.check sk248Slice.dArgAD.value = true := by
  norm_num [sk248LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk248Slice,
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

theorem sk248ValidityFacts : SKFacts sk248Slice
    sk248LogOuterCertificate sk248LogKCertificate
    sk248LogDArgCertificate :=
  { domain := by norm_num [sk248Slice]
    kPositive := by
      norm_num [sk248Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk248LogOuter_valid
    logK := sk248LogK_valid
    logDArg := sk248LogDArg_valid }

noncomputable def sk248RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (105165/65536), upper := (13474689/8388608) }
    logK := { lower := (11579783/8388608), upper := (23192497/16777216) }
    logDArg := { lower := (1864859/8388608), upper := (1894905/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk248LogOuterInput_eq :
    sk248RoundedInputs.logOuter = outerEnclosure 24
      (sk248LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk248LogKInput_eq :
    sk248RoundedInputs.logK = outerEnclosure 24
      (sk248LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk248LogDArgInput_eq :
    sk248RoundedInputs.logDArg = outerEnclosure 24
      (sk248LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk248RoundedFacts : SKRoundedFacts 8
    sk248LogOuterCertificate sk248LogKCertificate
    sk248LogDArgCertificate sk248RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk248LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk248LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk248LogDArgInput_eq }

noncomputable def sk249Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (511/128) }

noncomputable def sk249LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20904963/16777216) }, upper := { exponent := 2, mantissa := (639/512) } }

noncomputable def sk249LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (255/128) }, upper := { exponent := 1, mantissa := (511/256) } }

noncomputable def sk249LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (7107676157/5693112320) }, upper := { exponent := 0, mantissa := (213/170) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk249LogOuter_valid :
    sk249LogOuterCertificate.check sk249Slice.outerAD.value = true := by
  norm_num [sk249LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk249Slice,
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
private theorem sk249LogK_valid :
    sk249LogKCertificate.check sk249Slice.kAD.value = true := by
  norm_num [sk249LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk249Slice,
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
private theorem sk249LogDArg_valid :
    sk249LogDArgCertificate.check sk249Slice.dArgAD.value = true := by
  norm_num [sk249LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk249Slice,
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

theorem sk249ValidityFacts : SKFacts sk249Slice
    sk249LogOuterCertificate sk249LogKCertificate
    sk249LogDArgCertificate :=
  { domain := by norm_num [sk249Slice]
    kPositive := by
      norm_num [sk249Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk249LogOuter_valid
    logK := sk249LogK_valid
    logDArg := sk249LogDArg_valid }

noncomputable def sk249RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (26948557/16777216), upper := (13487827/8388608) }
    logK := { lower := (23192495/16777216), upper := (23225361/16777216) }
    logDArg := { lower := (1861585/8388608), upper := (3783157/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk249LogOuterInput_eq :
    sk249RoundedInputs.logOuter = outerEnclosure 24
      (sk249LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk249LogKInput_eq :
    sk249RoundedInputs.logK = outerEnclosure 24
      (sk249LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk249LogDArgInput_eq :
    sk249RoundedInputs.logDArg = outerEnclosure 24
      (sk249LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk249RoundedFacts : SKRoundedFacts 8
    sk249LogOuterCertificate sk249LogKCertificate
    sk249LogDArgCertificate sk249RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk249LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk249LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk249LogDArgInput_eq }

noncomputable def sk250Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (511/128), kHi := (4) }

noncomputable def sk250LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (20937729/16777216) }, upper := { exponent := 2, mantissa := (5/4) } }

noncomputable def sk250LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (511/256) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk250LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (21398325247/17146314752) }, upper := { exponent := 0, mantissa := (640/511) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk250LogOuter_valid :
    sk250LogOuterCertificate.check sk250Slice.outerAD.value = true := by
  norm_num [sk250LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk250Slice,
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
private theorem sk250LogK_valid :
    sk250LogKCertificate.check sk250Slice.kAD.value = true := by
  norm_num [sk250LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk250Slice,
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
private theorem sk250LogDArg_valid :
    sk250LogDArgCertificate.check sk250Slice.dArgAD.value = true := by
  norm_num [sk250LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk250Slice,
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

theorem sk250ValidityFacts : SKFacts sk250Slice
    sk250LogOuterCertificate sk250LogKCertificate
    sk250LogDArgCertificate :=
  { domain := by norm_num [sk250Slice]
    kPositive := by
      norm_num [sk250Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk250LogOuter_valid
    logK := sk250LogK_valid
    logDArg := sk250LogDArg_valid }

noncomputable def sk250RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1685927/1048576), upper := (27001889/16777216) }
    logK := { lower := (23225359/16777216), upper := (23258161/16777216) }
    logDArg := { lower := (1858323/8388608), upper := (236033/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk250LogOuterInput_eq :
    sk250RoundedInputs.logOuter = outerEnclosure 24
      (sk250LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk250LogKInput_eq :
    sk250RoundedInputs.logK = outerEnclosure 24
      (sk250LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk250LogDArgInput_eq :
    sk250RoundedInputs.logDArg = outerEnclosure 24
      (sk250LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk250RoundedFacts : SKRoundedFacts 8
    sk250LogOuterCertificate sk250LogKCertificate
    sk250LogDArgCertificate sk250RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk250LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk250LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk250LogDArgInput_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
