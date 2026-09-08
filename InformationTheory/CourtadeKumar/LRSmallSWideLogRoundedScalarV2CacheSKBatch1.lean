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

noncomputable def sk64Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4) }

noncomputable def sk64LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1671097/1048576) }, upper := { exponent := 1, mantissa := (13/8) } }

noncomputable def sk64LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (35/32) }, upper := { exponent := 1, mantissa := (9/8) } }

noncomputable def sk64LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (38981317/27525120) }, upper := { exponent := 0, mantissa := (52/35) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk64LogOuter_valid :
    sk64LogOuterCertificate.check sk64Slice.outerAD.value = true := by
  norm_num [sk64LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk64Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk64LogK_valid :
    sk64LogKCertificate.check sk64Slice.kAD.value = true := by
  norm_num [sk64LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk64Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk64LogDArg_valid :
    sk64LogDArgCertificate.check sk64Slice.dArgAD.value = true := by
  norm_num [sk64LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk64Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk64ValidityFacts : SKFacts sk64Slice
    sk64LogOuterCertificate sk64LogKCertificate
    sk64LogDArgCertificate :=
  { domain := by norm_num [sk64Slice]
    kPositive := by
      norm_num [sk64Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk64LogOuter_valid
    logK := sk64LogK_valid
    logDArg := sk64LogDArg_valid }

noncomputable def sk64RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (19448055/16777216), upper := (9887275/8388608) }
    logK := { lower := (6566261/8388608), upper := (425161/524288) }
    logDArg := { lower := (5838193/16777216), upper := (6642027/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk64LogOuterInput_eq :
    sk64RoundedInputs.logOuter = outerEnclosure 24
      (sk64LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk64LogKInput_eq :
    sk64RoundedInputs.logK = outerEnclosure 24
      (sk64LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk64LogDArgInput_eq :
    sk64RoundedInputs.logDArg = outerEnclosure 24
      (sk64LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk64RoundedFacts : SKRoundedFacts 8
    sk64LogOuterCertificate sk64LogKCertificate
    sk64LogDArgCertificate sk64RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk64LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk64LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk64LogDArgInput_eq }

noncomputable def sk65Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8) }

noncomputable def sk65LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (851931/524288) }, upper := { exponent := 1, mantissa := (27/16) } }

noncomputable def sk65LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (9/8) }, upper := { exponent := 1, mantissa := (19/16) } }

noncomputable def sk65LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3404079/2490368) }, upper := { exponent := 0, mantissa := (3/2) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk65LogOuter_valid :
    sk65LogOuterCertificate.check sk65Slice.outerAD.value = true := by
  norm_num [sk65LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk65Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk65LogK_valid :
    sk65LogKCertificate.check sk65Slice.kAD.value = true := by
  norm_num [sk65LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk65Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk65LogDArg_valid :
    sk65LogDArgCertificate.check sk65Slice.dArgAD.value = true := by
  norm_num [sk65LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk65Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk65ValidityFacts : SKFacts sk65Slice
    sk65LogOuterCertificate sk65LogKCertificate
    sk65LogDArgCertificate :=
  { domain := by norm_num [sk65Slice]
    kPositive := by
      norm_num [sk65Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk65LogOuter_valid
    logK := sk65LogK_valid
    logDArg := sk65LogDArg_valid }

noncomputable def sk65RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (4943455/4194304), upper := (1275483/1048576) }
    logK := { lower := (13605151/16777216), upper := (7256125/8388608) }
    logDArg := { lower := (163863/524288), upper := (425161/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk65LogOuterInput_eq :
    sk65RoundedInputs.logOuter = outerEnclosure 24
      (sk65LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk65LogKInput_eq :
    sk65RoundedInputs.logK = outerEnclosure 24
      (sk65LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk65LogDArgInput_eq :
    sk65RoundedInputs.logDArg = outerEnclosure 24
      (sk65LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk65RoundedFacts : SKRoundedFacts 8
    sk65LogOuterCertificate sk65LogKCertificate
    sk65LogDArgCertificate sk65RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk65LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk65LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk65LogDArgInput_eq }

noncomputable def sk66Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2) }

noncomputable def sk66LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (884697/524288) }, upper := { exponent := 1, mantissa := (7/4) } }

noncomputable def sk66LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (19/16) }, upper := { exponent := 1, mantissa := (5/4) } }

noncomputable def sk66LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (33585679/24903680) }, upper := { exponent := 0, mantissa := (28/19) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk66LogOuter_valid :
    sk66LogOuterCertificate.check sk66Slice.outerAD.value = true := by
  norm_num [sk66LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk66Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk66LogK_valid :
    sk66LogKCertificate.check sk66Slice.kAD.value = true := by
  norm_num [sk66LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk66Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk66LogDArg_valid :
    sk66LogDArgCertificate.check sk66Slice.dArgAD.value = true := by
  norm_num [sk66LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk66Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk66ValidityFacts : SKFacts sk66Slice
    sk66LogOuterCertificate sk66LogKCertificate
    sk66LogDArgCertificate :=
  { domain := by norm_num [sk66Slice]
    kPositive := by
      norm_num [sk66Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk66LogOuter_valid
    logK := sk66LogK_valid
    logDArg := sk66LogDArg_valid }

noncomputable def sk66RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (20406987/16777216), upper := (5254469/4194304) }
    logK := { lower := (1814031/2097152), upper := (1921601/2097152) }
    logDArg := { lower := (5017799/16777216), upper := (6505627/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk66LogOuterInput_eq :
    sk66RoundedInputs.logOuter = outerEnclosure 24
      (sk66LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk66LogKInput_eq :
    sk66RoundedInputs.logK = outerEnclosure 24
      (sk66LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk66LogDArgInput_eq :
    sk66RoundedInputs.logDArg = outerEnclosure 24
      (sk66LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk66RoundedFacts : SKRoundedFacts 8
    sk66LogOuterCertificate sk66LogKCertificate
    sk66LogDArgCertificate sk66RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk66LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk66LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk66LogDArgInput_eq }

noncomputable def sk67Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16) }

noncomputable def sk67LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1769395/1048576) }, upper := { exponent := 1, mantissa := (55/32) } }

noncomputable def sk67LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (19/16) }, upper := { exponent := 1, mantissa := (39/32) } }

noncomputable def sk67LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (44813725/32374784) }, upper := { exponent := 0, mantissa := (55/38) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk67LogOuter_valid :
    sk67LogOuterCertificate.check sk67Slice.outerAD.value = true := by
  norm_num [sk67LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk67Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk67LogK_valid :
    sk67LogKCertificate.check sk67Slice.kAD.value = true := by
  norm_num [sk67LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk67Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk67LogDArg_valid :
    sk67LogDArgCertificate.check sk67Slice.dArgAD.value = true := by
  norm_num [sk67LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk67Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk67ValidityFacts : SKFacts sk67Slice
    sk67LogOuterCertificate sk67LogKCertificate
    sk67LogDArgCertificate :=
  { domain := by norm_num [sk67Slice]
    kPositive := by
      norm_num [sk67Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk67LogOuter_valid
    logK := sk67LogK_valid
    logDArg := sk67LogDArg_valid }

noncomputable def sk67RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5101749/4194304), upper := (20715575/16777216) }
    logK := { lower := (1814031/2097152), upper := (7474023/8388608) }
    logDArg := { lower := (5454853/16777216), upper := (3101663/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk67LogOuterInput_eq :
    sk67RoundedInputs.logOuter = outerEnclosure 24
      (sk67LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk67LogKInput_eq :
    sk67RoundedInputs.logK = outerEnclosure 24
      (sk67LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk67LogDArgInput_eq :
    sk67RoundedInputs.logDArg = outerEnclosure 24
      (sk67LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk67RoundedFacts : SKRoundedFacts 8
    sk67LogOuterCertificate sk67LogKCertificate
    sk67LogDArgCertificate sk67RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk67LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk67LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk67LogDArgInput_eq }

noncomputable def sk68Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2) }

noncomputable def sk68LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1802161/1048576) }, upper := { exponent := 1, mantissa := (7/4) } }

noncomputable def sk68LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (39/32) }, upper := { exponent := 1, mantissa := (5/4) } }

noncomputable def sk68LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (46845237/34078720) }, upper := { exponent := 0, mantissa := (56/39) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk68LogOuter_valid :
    sk68LogOuterCertificate.check sk68Slice.outerAD.value = true := by
  norm_num [sk68LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk68Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk68LogK_valid :
    sk68LogKCertificate.check sk68Slice.kAD.value = true := by
  norm_num [sk68LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk68Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk68LogDArg_valid :
    sk68LogDArgCertificate.check sk68Slice.dArgAD.value = true := by
  norm_num [sk68LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk68Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk68ValidityFacts : SKFacts sk68Slice
    sk68LogOuterCertificate sk68LogKCertificate
    sk68LogDArgCertificate :=
  { domain := by norm_num [sk68Slice]
    kPositive := by
      norm_num [sk68Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk68LogOuter_valid
    logK := sk68LogK_valid
    logDArg := sk68LogDArg_valid }

noncomputable def sk68RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (20714839/16777216), upper := (5254469/4194304) }
    logK := { lower := (14948045/16777216), upper := (1921601/2097152) }
    logDArg := { lower := (2669055/8388608), upper := (3034915/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk68LogOuterInput_eq :
    sk68RoundedInputs.logOuter = outerEnclosure 24
      (sk68LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk68LogKInput_eq :
    sk68RoundedInputs.logK = outerEnclosure 24
      (sk68LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk68LogDArgInput_eq :
    sk68RoundedInputs.logDArg = outerEnclosure 24
      (sk68LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk68RoundedFacts : SKRoundedFacts 8
    sk68LogOuterCertificate sk68LogKCertificate
    sk68LogDArgCertificate sk68RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk68LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk68LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk68LogDArgInput_eq }

noncomputable def sk69Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16) }

noncomputable def sk69LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1703863/1048576) }, upper := { exponent := 1, mantissa := (53/32) } }

noncomputable def sk69LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (9/8) }, upper := { exponent := 1, mantissa := (37/32) } }

noncomputable def sk69LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (13627255/9699328) }, upper := { exponent := 0, mantissa := (53/36) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk69LogOuter_valid :
    sk69LogOuterCertificate.check sk69Slice.outerAD.value = true := by
  norm_num [sk69LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk69Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk69LogK_valid :
    sk69LogKCertificate.check sk69Slice.kAD.value = true := by
  norm_num [sk69LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk69Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk69LogDArg_valid :
    sk69LogDArgCertificate.check sk69Slice.dArgAD.value = true := by
  norm_num [sk69LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk69Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk69ValidityFacts : SKFacts sk69Slice
    sk69LogOuterCertificate sk69LogKCertificate
    sk69LogDArgCertificate :=
  { domain := by norm_num [sk69Slice]
    kPositive := by
      norm_num [sk69Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk69LogOuter_valid
    logK := sk69LogK_valid
    logDArg := sk69LogDArg_valid }

noncomputable def sk69RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (9886915/8388608), upper := (10047063/8388608) }
    logK := { lower := (13605151/16777216), upper := (14064831/16777216) }
    logDArg := { lower := (1426127/4194304), upper := (3244487/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk69LogOuterInput_eq :
    sk69RoundedInputs.logOuter = outerEnclosure 24
      (sk69LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk69LogKInput_eq :
    sk69RoundedInputs.logK = outerEnclosure 24
      (sk69LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk69LogDArgInput_eq :
    sk69RoundedInputs.logDArg = outerEnclosure 24
      (sk69LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk69RoundedFacts : SKRoundedFacts 8
    sk69LogOuterCertificate sk69LogKCertificate
    sk69LogDArgCertificate sk69RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk69LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk69LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk69LogDArgInput_eq }

noncomputable def sk70Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8) }

noncomputable def sk70LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1736629/1048576) }, upper := { exponent := 1, mantissa := (27/16) } }

noncomputable def sk70LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (37/32) }, upper := { exponent := 1, mantissa := (19/16) } }

noncomputable def sk70LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (128477703/92143616) }, upper := { exponent := 0, mantissa := (54/37) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk70LogOuter_valid :
    sk70LogOuterCertificate.check sk70Slice.outerAD.value = true := by
  norm_num [sk70LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk70Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk70LogK_valid :
    sk70LogKCertificate.check sk70Slice.kAD.value = true := by
  norm_num [sk70LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk70Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk70LogDArg_valid :
    sk70LogDArgCertificate.check sk70Slice.dArgAD.value = true := by
  norm_num [sk70LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk70Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk70ValidityFacts : SKFacts sk70Slice
    sk70LogOuterCertificate sk70LogKCertificate
    sk70LogDArgCertificate :=
  { domain := by norm_num [sk70Slice]
    kPositive := by
      norm_num [sk70Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk70LogOuter_valid
    logK := sk70LogK_valid
    logDArg := sk70LogDArg_valid }

noncomputable def sk70RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2511675/2097152), upper := (1275483/1048576) }
    logK := { lower := (14064829/16777216), upper := (7256125/8388608) }
    logDArg := { lower := (5576863/16777216), upper := (3171449/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk70LogOuterInput_eq :
    sk70RoundedInputs.logOuter = outerEnclosure 24
      (sk70LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk70LogKInput_eq :
    sk70RoundedInputs.logK = outerEnclosure 24
      (sk70LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk70LogDArgInput_eq :
    sk70RoundedInputs.logDArg = outerEnclosure 24
      (sk70LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk70RoundedFacts : SKRoundedFacts 8
    sk70LogOuterCertificate sk70LogKCertificate
    sk70LogDArgCertificate sk70RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk70LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk70LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk70LogDArgInput_eq }

noncomputable def sk71Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (65/32) }

noncomputable def sk71LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3145599/2097152) }, upper := { exponent := 1, mantissa := (97/64) } }

noncomputable def sk71LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1) }, upper := { exponent := 1, mantissa := (65/64) } }

noncomputable def sk71LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (80520755/54525952) }, upper := { exponent := 0, mantissa := (97/64) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk71LogOuter_valid :
    sk71LogOuterCertificate.check sk71Slice.outerAD.value = true := by
  norm_num [sk71LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk71Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk71LogK_valid :
    sk71LogKCertificate.check sk71Slice.kAD.value = true := by
  norm_num [sk71LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk71Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk71LogDArg_valid :
    sk71LogDArgCertificate.check sk71Slice.dArgAD.value = true := by
  norm_num [sk71LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk71Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk71ValidityFacts : SKFacts sk71Slice
    sk71LogOuterCertificate sk71LogKCertificate
    sk71LogDArgCertificate :=
  { domain := by norm_num [sk71Slice]
    kPositive := by
      norm_num [sk71Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk71LogOuter_valid
    logK := sk71LogK_valid
    logDArg := sk71LogDArg_valid }

noncomputable def sk71RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (18430967/16777216), upper := (18605515/16777216) }
    logK := { lower := (11629079/16777216), upper := (5944599/8388608) }
    logDArg := { lower := (6540399/16777216), upper := (6976435/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk71LogOuterInput_eq :
    sk71RoundedInputs.logOuter = outerEnclosure 24
      (sk71LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk71LogKInput_eq :
    sk71RoundedInputs.logK = outerEnclosure 24
      (sk71LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk71LogDArgInput_eq :
    sk71RoundedInputs.logDArg = outerEnclosure 24
      (sk71LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk71RoundedFacts : SKRoundedFacts 8
    sk71LogOuterCertificate sk71LogKCertificate
    sk71LogDArgCertificate sk71RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk71LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk71LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk71LogDArgInput_eq }

noncomputable def sk72Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (65/32), kHi := (33/16) }

noncomputable def sk72LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3178365/2097152) }, upper := { exponent := 1, mantissa := (49/32) } }

noncomputable def sk72LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (65/64) }, upper := { exponent := 1, mantissa := (33/32) } }

noncomputable def sk72LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (413154551/281149440) }, upper := { exponent := 0, mantissa := (98/65) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk72LogOuter_valid :
    sk72LogOuterCertificate.check sk72Slice.outerAD.value = true := by
  norm_num [sk72LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk72Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk72LogK_valid :
    sk72LogKCertificate.check sk72Slice.kAD.value = true := by
  norm_num [sk72LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk72Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk72LogDArg_valid :
    sk72LogDArgCertificate.check sk72Slice.dArgAD.value = true := by
  norm_num [sk72LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk72Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk72ValidityFacts : SKFacts sk72Slice
    sk72LogOuterCertificate sk72LogKCertificate
    sk72LogDArgCertificate :=
  { domain := by norm_num [sk72Slice]
    kPositive := by
      norm_num [sk72Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk72LogOuter_valid
    logK := sk72LogK_valid
    logDArg := sk72LogDArg_valid }

noncomputable def sk72RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (9302411/8388608), upper := (18777591/16777216) }
    logK := { lower := (11889197/16777216), upper := (189771/262144) }
    logDArg := { lower := (201817/524288), upper := (6888393/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk72LogOuterInput_eq :
    sk72RoundedInputs.logOuter = outerEnclosure 24
      (sk72LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk72LogKInput_eq :
    sk72RoundedInputs.logK = outerEnclosure 24
      (sk72LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk72LogDArgInput_eq :
    sk72RoundedInputs.logDArg = outerEnclosure 24
      (sk72LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk72RoundedFacts : SKRoundedFacts 8
    sk72LogOuterCertificate sk72LogKCertificate
    sk72LogDArgCertificate sk72RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk72LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk72LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk72LogDArgInput_eq }

noncomputable def sk73Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (67/32) }

noncomputable def sk73LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3211131/2097152) }, upper := { exponent := 1, mantissa := (99/64) } }

noncomputable def sk73LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (33/32) }, upper := { exponent := 1, mantissa := (67/64) } }

noncomputable def sk73LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (12843527/8781824) }, upper := { exponent := 0, mantissa := (3/2) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk73LogOuter_valid :
    sk73LogOuterCertificate.check sk73Slice.outerAD.value = true := by
  norm_num [sk73LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk73Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk73LogK_valid :
    sk73LogKCertificate.check sk73Slice.kAD.value = true := by
  norm_num [sk73LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk73Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk73LogDArg_valid :
    sk73LogDArgCertificate.check sk73Slice.dArgAD.value = true := by
  norm_num [sk73LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk73Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk73ValidityFacts : SKFacts sk73Slice
    sk73LogOuterCertificate sk73LogKCertificate
    sk73LogDArgCertificate :=
  { domain := by norm_num [sk73Slice]
    kPositive := by
      norm_num [sk73Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk73LogOuter_valid
    logK := sk73LogK_valid
    logDArg := sk73LogDArg_valid }

noncomputable def sk73RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (18776895/16777216), upper := (18947919/16777216) }
    logK := { lower := (6072671/8388608), upper := (12397637/16777216) }
    logDArg := { lower := (1594489/4194304), upper := (425161/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk73LogOuterInput_eq :
    sk73RoundedInputs.logOuter = outerEnclosure 24
      (sk73LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk73LogKInput_eq :
    sk73RoundedInputs.logK = outerEnclosure 24
      (sk73LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk73LogDArgInput_eq :
    sk73RoundedInputs.logDArg = outerEnclosure 24
      (sk73LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk73RoundedFacts : SKRoundedFacts 8
    sk73LogOuterCertificate sk73LogKCertificate
    sk73LogDArgCertificate sk73RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk73LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk73LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk73LogDArgInput_eq }

noncomputable def sk74Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (67/32), kHi := (17/8) }

noncomputable def sk74LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3243897/2097152) }, upper := { exponent := 1, mantissa := (25/16) } }

noncomputable def sk74LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (67/64) }, upper := { exponent := 1, mantissa := (17/16) } }

noncomputable def sk74LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (434649295/298582016) }, upper := { exponent := 0, mantissa := (100/67) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk74LogOuter_valid :
    sk74LogOuterCertificate.check sk74Slice.outerAD.value = true := by
  norm_num [sk74LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk74Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk74LogK_valid :
    sk74LogKCertificate.check sk74Slice.kAD.value = true := by
  norm_num [sk74LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk74Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk74LogDArg_valid :
    sk74LogDArgCertificate.check sk74Slice.dArgAD.value = true := by
  norm_num [sk74LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk74Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk74ValidityFacts : SKFacts sk74Slice
    sk74LogOuterCertificate sk74LogKCertificate
    sk74LogDArgCertificate :=
  { domain := by norm_num [sk74Slice]
    kPositive := by
      norm_num [sk74Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk74LogOuter_valid
    logK := sk74LogK_valid
    logDArg := sk74LogDArg_valid }

noncomputable def sk74RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (4736805/4194304), upper := (2389567/2097152) }
    logK := { lower := (3099409/4194304), upper := (12646193/16777216) }
    logDArg := { lower := (6299757/16777216), upper := (6718899/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk74LogOuterInput_eq :
    sk74RoundedInputs.logOuter = outerEnclosure 24
      (sk74LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk74LogKInput_eq :
    sk74RoundedInputs.logK = outerEnclosure 24
      (sk74LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk74LogDArgInput_eq :
    sk74RoundedInputs.logDArg = outerEnclosure 24
      (sk74LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk74RoundedFacts : SKRoundedFacts 8
    sk74LogOuterCertificate sk74LogKCertificate
    sk74LogDArgCertificate sk74RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk74LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk74LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk74LogDArgInput_eq }

noncomputable def sk75Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (69/32) }

noncomputable def sk75LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3276663/2097152) }, upper := { exponent := 1, mantissa := (101/64) } }

noncomputable def sk75LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (17/16) }, upper := { exponent := 1, mantissa := (69/64) } }

noncomputable def sk75LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (445593263/307494912) }, upper := { exponent := 0, mantissa := (101/68) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk75LogOuter_valid :
    sk75LogOuterCertificate.check sk75Slice.outerAD.value = true := by
  norm_num [sk75LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk75Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk75LogK_valid :
    sk75LogKCertificate.check sk75Slice.kAD.value = true := by
  norm_num [sk75LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk75Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk75LogDArg_valid :
    sk75LogDArgCertificate.check sk75Slice.dArgAD.value = true := by
  norm_num [sk75LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk75Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk75ValidityFacts : SKFacts sk75Slice
    sk75LogOuterCertificate sk75LogKCertificate
    sk75LogDArgCertificate :=
  { domain := by norm_num [sk75Slice]
    kPositive := by
      norm_num [sk75Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk75LogOuter_valid
    logK := sk75LogK_valid
    logDArg := sk75LogDArg_valid }

noncomputable def sk75RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (19115833/16777216), upper := (19283475/16777216) }
    logK := { lower := (790387/1048576), upper := (805695/1048576) }
    logDArg := { lower := (6223475/16777216), upper := (3318641/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk75LogOuterInput_eq :
    sk75RoundedInputs.logOuter = outerEnclosure 24
      (sk75LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk75LogKInput_eq :
    sk75RoundedInputs.logK = outerEnclosure 24
      (sk75LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk75LogDArgInput_eq :
    sk75RoundedInputs.logDArg = outerEnclosure 24
      (sk75LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk75RoundedFacts : SKRoundedFacts 8
    sk75LogOuterCertificate sk75LogKCertificate
    sk75LogDArgCertificate sk75RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk75LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk75LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk75LogDArgInput_eq }

noncomputable def sk76Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (69/32), kHi := (35/16) }

noncomputable def sk76LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3309429/2097152) }, upper := { exponent := 1, mantissa := (51/32) } }

noncomputable def sk76LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (69/64) }, upper := { exponent := 1, mantissa := (35/32) } }

noncomputable def sk76LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (30444553/21102592) }, upper := { exponent := 0, mantissa := (34/23) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk76LogOuter_valid :
    sk76LogOuterCertificate.check sk76Slice.outerAD.value = true := by
  norm_num [sk76LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk76Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk76LogK_valid :
    sk76LogKCertificate.check sk76Slice.kAD.value = true := by
  norm_num [sk76LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk76Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk76LogDArg_valid :
    sk76LogDArgCertificate.check sk76Slice.dArgAD.value = true := by
  norm_num [sk76LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk76Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk76ValidityFacts : SKFacts sk76Slice
    sk76LogOuterCertificate sk76LogKCertificate
    sk76LogDArgCertificate :=
  { domain := by norm_num [sk76Slice]
    kPositive := by
      norm_num [sk76Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk76LogOuter_valid
    logK := sk76LogK_valid
    logDArg := sk76LogDArg_valid }

noncomputable def sk76RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (19282769/16777216), upper := (19448769/16777216) }
    logK := { lower := (12891119/16777216), upper := (13132523/16777216) }
    logDArg := { lower := (6149037/16777216), upper := (6557649/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk76LogOuterInput_eq :
    sk76RoundedInputs.logOuter = outerEnclosure 24
      (sk76LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk76LogKInput_eq :
    sk76RoundedInputs.logK = outerEnclosure 24
      (sk76LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk76LogDArgInput_eq :
    sk76RoundedInputs.logDArg = outerEnclosure 24
      (sk76LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk76RoundedFacts : SKRoundedFacts 8
    sk76LogOuterCertificate sk76LogKCertificate
    sk76LogDArgCertificate sk76RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk76LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk76LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk76LogDArgInput_eq }

noncomputable def sk77Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (71/32) }

noncomputable def sk77LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3342195/2097152) }, upper := { exponent := 1, mantissa := (103/64) } }

noncomputable def sk77LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (35/32) }, upper := { exponent := 1, mantissa := (71/64) } }

noncomputable def sk77LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (467874391/325713920) }, upper := { exponent := 0, mantissa := (103/70) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk77LogOuter_valid :
    sk77LogOuterCertificate.check sk77Slice.outerAD.value = true := by
  norm_num [sk77LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk77Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk77LogK_valid :
    sk77LogKCertificate.check sk77Slice.kAD.value = true := by
  norm_num [sk77LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk77Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk77LogDArg_valid :
    sk77LogDArgCertificate.check sk77Slice.dArgAD.value = true := by
  norm_num [sk77LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk77Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk77ValidityFacts : SKFacts sk77Slice
    sk77LogOuterCertificate sk77LogKCertificate
    sk77LogDArgCertificate :=
  { domain := by norm_num [sk77Slice]
    kPositive := by
      norm_num [sk77Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk77LogOuter_valid
    logK := sk77LogK_valid
    logDArg := sk77LogDArg_valid }

noncomputable def sk77RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (4862015/4194304), upper := (9806225/8388608) }
    logK := { lower := (6566261/8388608), upper := (6685251/8388608) }
    logDArg := { lower := (6076379/16777216), upper := (6479927/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk77LogOuterInput_eq :
    sk77RoundedInputs.logOuter = outerEnclosure 24
      (sk77LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk77LogKInput_eq :
    sk77RoundedInputs.logK = outerEnclosure 24
      (sk77LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk77LogDArgInput_eq :
    sk77RoundedInputs.logDArg = outerEnclosure 24
      (sk77LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk77RoundedFacts : SKRoundedFacts 8
    sk77LogOuterCertificate sk77LogKCertificate
    sk77LogDArgCertificate sk77RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk77LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk77LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk77LogDArgInput_eq }

noncomputable def sk78Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (71/32), kHi := (9/4) }

noncomputable def sk78LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3374961/2097152) }, upper := { exponent := 1, mantissa := (13/8) } }

noncomputable def sk78LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (71/64) }, upper := { exponent := 1, mantissa := (9/8) } }

noncomputable def sk78LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (479211551/335020032) }, upper := { exponent := 0, mantissa := (104/71) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk78LogOuter_valid :
    sk78LogOuterCertificate.check sk78Slice.outerAD.value = true := by
  norm_num [sk78LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk78Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk78LogK_valid :
    sk78LogKCertificate.check sk78Slice.kAD.value = true := by
  norm_num [sk78LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk78Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk78LogDArg_valid :
    sk78LogDArgCertificate.check sk78Slice.dArgAD.value = true := by
  norm_num [sk78LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk78Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk78ValidityFacts : SKFacts sk78Slice
    sk78LogOuterCertificate sk78LogKCertificate
    sk78LogDArgCertificate :=
  { domain := by norm_num [sk78Slice]
    kPositive := by
      norm_num [sk78Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk78LogOuter_valid
    logK := sk78LogK_valid
    logDArg := sk78LogDArg_valid }

noncomputable def sk78RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (9805869/8388608), upper := (9887275/8388608) }
    logK := { lower := (13370501/16777216), upper := (425161/524288) }
    logDArg := { lower := (6005435/16777216), upper := (6404049/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk78LogOuterInput_eq :
    sk78RoundedInputs.logOuter = outerEnclosure 24
      (sk78LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk78LogKInput_eq :
    sk78RoundedInputs.logK = outerEnclosure 24
      (sk78LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk78LogDArgInput_eq :
    sk78RoundedInputs.logDArg = outerEnclosure 24
      (sk78LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk78RoundedFacts : SKRoundedFacts 8
    sk78LogOuterCertificate sk78LogKCertificate
    sk78LogDArgCertificate sk78RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk78LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk78LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk78LogDArgInput_eq }

noncomputable def sk79Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32) }

noncomputable def sk79LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3473259/2097152) }, upper := { exponent := 1, mantissa := (107/64) } }

noncomputable def sk79LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (37/32) }, upper := { exponent := 1, mantissa := (75/64) } }

noncomputable def sk79LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (102801883/72744960) }, upper := { exponent := 0, mantissa := (107/74) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk79LogOuter_valid :
    sk79LogOuterCertificate.check sk79Slice.outerAD.value = true := by
  norm_num [sk79LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk79Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk79LogK_valid :
    sk79LogKCertificate.check sk79Slice.kAD.value = true := by
  norm_num [sk79LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk79Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk79LogDArg_valid :
    sk79LogDArgCertificate.check sk79Slice.dArgAD.value = true := by
  norm_num [sk79LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk79Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk79ValidityFacts : SKFacts sk79Slice
    sk79LogOuterCertificate sk79LogKCertificate
    sk79LogDArgCertificate :=
  { domain := by norm_num [sk79Slice]
    kPositive := by
      norm_num [sk79Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk79LogOuter_valid
    logK := sk79LogK_valid
    logDArg := sk79LogDArg_valid }

noncomputable def sk79RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (20093405/16777216), upper := (5062915/4194304) }
    logK := { lower := (14064829/16777216), upper := (893127/1048576) }
    logDArg := { lower := (1450575/4194304), upper := (6186829/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk79LogOuterInput_eq :
    sk79RoundedInputs.logOuter = outerEnclosure 24
      (sk79LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk79LogKInput_eq :
    sk79RoundedInputs.logK = outerEnclosure 24
      (sk79LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk79LogDArgInput_eq :
    sk79RoundedInputs.logDArg = outerEnclosure 24
      (sk79LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk79RoundedFacts : SKRoundedFacts 8
    sk79LogOuterCertificate sk79LogKCertificate
    sk79LogDArgCertificate sk79RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk79LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk79LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk79LogDArgInput_eq }

noncomputable def sk80Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8) }

noncomputable def sk80LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3506025/2097152) }, upper := { exponent := 1, mantissa := (27/16) } }

noncomputable def sk80LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (75/64) }, upper := { exponent := 1, mantissa := (19/16) } }

noncomputable def sk80LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (175290277/124518400) }, upper := { exponent := 0, mantissa := (36/25) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk80LogOuter_valid :
    sk80LogOuterCertificate.check sk80Slice.outerAD.value = true := by
  norm_num [sk80LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk80Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk80LogK_valid :
    sk80LogKCertificate.check sk80Slice.kAD.value = true := by
  norm_num [sk80LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk80Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk80LogDArg_valid :
    sk80LogDArgCertificate.check sk80Slice.dArgAD.value = true := by
  norm_num [sk80LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk80Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk80ValidityFacts : SKFacts sk80Slice
    sk80LogOuterCertificate sk80LogKCertificate
    sk80LogDArgCertificate :=
  { domain := by norm_num [sk80Slice]
    kPositive := by
      norm_num [sk80Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk80LogOuter_valid
    logK := sk80LogK_valid
    logDArg := sk80LogDArg_valid }

noncomputable def sk80RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2531367/2097152), upper := (1275483/1048576) }
    logK := { lower := (7145015/8388608), upper := (7256125/8388608) }
    logDArg := { lower := (5737637/16777216), upper := (6117697/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk80LogOuterInput_eq :
    sk80RoundedInputs.logOuter = outerEnclosure 24
      (sk80LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk80LogKInput_eq :
    sk80RoundedInputs.logK = outerEnclosure 24
      (sk80LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk80LogDArgInput_eq :
    sk80RoundedInputs.logDArg = outerEnclosure 24
      (sk80LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk80RoundedFacts : SKRoundedFacts 8
    sk80LogOuterCertificate sk80LogKCertificate
    sk80LogDArgCertificate sk80RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk80LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk80LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk80LogDArgInput_eq }

noncomputable def sk81Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32) }

noncomputable def sk81LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3538791/2097152) }, upper := { exponent := 1, mantissa := (109/64) } }

noncomputable def sk81LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (19/16) }, upper := { exponent := 1, mantissa := (77/64) } }

noncomputable def sk81LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (537863311/383516672) }, upper := { exponent := 0, mantissa := (109/76) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk81LogOuter_valid :
    sk81LogOuterCertificate.check sk81Slice.outerAD.value = true := by
  norm_num [sk81LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk81Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk81LogK_valid :
    sk81LogKCertificate.check sk81Slice.kAD.value = true := by
  norm_num [sk81LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk81Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk81LogDArg_valid :
    sk81LogDArgCertificate.check sk81Slice.dArgAD.value = true := by
  norm_num [sk81LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk81Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk81ValidityFacts : SKFacts sk81Slice
    sk81LogOuterCertificate sk81LogKCertificate
    sk81LogDArgCertificate :=
  { domain := by norm_num [sk81Slice]
    kPositive := by
      norm_num [sk81Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk81LogOuter_valid
    logK := sk81LogK_valid
    logDArg := sk81LogDArg_valid }

noncomputable def sk81RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (20407001/16777216), upper := (10281179/8388608) }
    logK := { lower := (1814031/2097152), upper := (14731563/16777216) }
    logDArg := { lower := (1418603/4194304), upper := (6050109/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk81LogOuterInput_eq :
    sk81RoundedInputs.logOuter = outerEnclosure 24
      (sk81LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk81LogKInput_eq :
    sk81RoundedInputs.logK = outerEnclosure 24
      (sk81LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk81LogDArgInput_eq :
    sk81RoundedInputs.logDArg = outerEnclosure 24
      (sk81LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk81RoundedFacts : SKRoundedFacts 8
    sk81LogOuterCertificate sk81LogKCertificate
    sk81LogDArgCertificate sk81RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk81LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk81LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk81LogDArgInput_eq }

noncomputable def sk82Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16) }

noncomputable def sk82LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3571557/2097152) }, upper := { exponent := 1, mantissa := (55/32) } }

noncomputable def sk82LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (77/64) }, upper := { exponent := 1, mantissa := (39/32) } }

noncomputable def sk82LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (49998805/35782656) }, upper := { exponent := 0, mantissa := (10/7) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk82LogOuter_valid :
    sk82LogOuterCertificate.check sk82Slice.outerAD.value = true := by
  norm_num [sk82LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk82Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk82LogK_valid :
    sk82LogKCertificate.check sk82Slice.kAD.value = true := by
  norm_num [sk82LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk82Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk82LogDArg_valid :
    sk82LogDArgCertificate.check sk82Slice.dArgAD.value = true := by
  norm_num [sk82LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk82Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk82ValidityFacts : SKFacts sk82Slice
    sk82LogOuterCertificate sk82LogKCertificate
    sk82LogDArgCertificate :=
  { domain := by norm_num [sk82Slice]
    kPositive := by
      norm_num [sk82Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk82LogOuter_valid
    logK := sk82LogK_valid
    logDArg := sk82LogDArg_valid }

noncomputable def sk82RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5140407/4194304), upper := (20715575/16777216) }
    logK := { lower := (14731561/16777216), upper := (7474023/8388608) }
    logDArg := { lower := (5612579/16777216), upper := (5984013/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk82LogOuterInput_eq :
    sk82RoundedInputs.logOuter = outerEnclosure 24
      (sk82LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk82LogKInput_eq :
    sk82RoundedInputs.logK = outerEnclosure 24
      (sk82LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk82LogDArgInput_eq :
    sk82RoundedInputs.logDArg = outerEnclosure 24
      (sk82LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk82RoundedFacts : SKRoundedFacts 8
    sk82LogOuterCertificate sk82LogKCertificate
    sk82LogDArgCertificate sk82RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk82LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk82LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk82LogDArgInput_eq }

noncomputable def sk83Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32) }

noncomputable def sk83LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3604323/2097152) }, upper := { exponent := 1, mantissa := (111/64) } }

noncomputable def sk83LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (39/32) }, upper := { exponent := 1, mantissa := (79/64) } }

noncomputable def sk83LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (187413821/134610944) }, upper := { exponent := 0, mantissa := (37/26) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk83LogOuter_valid :
    sk83LogOuterCertificate.check sk83Slice.outerAD.value = true := by
  norm_num [sk83LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk83Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk83LogK_valid :
    sk83LogKCertificate.check sk83Slice.kAD.value = true := by
  norm_num [sk83LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk83Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk83LogDArg_valid :
    sk83LogDArgCertificate.check sk83Slice.dArgAD.value = true := by
  norm_num [sk83LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk83Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk83ValidityFacts : SKFacts sk83Slice
    sk83LogOuterCertificate sk83LogKCertificate
    sk83LogDArgCertificate :=
  { domain := by norm_num [sk83Slice]
    kPositive := by
      norm_num [sk83Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk83LogOuter_valid
    logK := sk83LogK_valid
    logDArg := sk83LogDArg_valid }

noncomputable def sk83RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (20714843/16777216), upper := (10433703/8388608) }
    logK := { lower := (14948045/16777216), upper := (15161771/16777216) }
    logDArg := { lower := (2776045/8388608), upper := (5919361/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk83LogOuterInput_eq :
    sk83RoundedInputs.logOuter = outerEnclosure 24
      (sk83LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk83LogKInput_eq :
    sk83RoundedInputs.logK = outerEnclosure 24
      (sk83LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk83LogDArgInput_eq :
    sk83RoundedInputs.logDArg = outerEnclosure 24
      (sk83LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk83RoundedFacts : SKRoundedFacts 8
    sk83LogOuterCertificate sk83LogKCertificate
    sk83LogDArgCertificate sk83RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk83LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk83LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk83LogDArgInput_eq }

noncomputable def sk84Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2) }

noncomputable def sk84LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3637089/2097152) }, upper := { exponent := 1, mantissa := (7/4) } }

noncomputable def sk84LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (79/64) }, upper := { exponent := 1, mantissa := (5/4) } }

noncomputable def sk84LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (114925427/82837504) }, upper := { exponent := 0, mantissa := (112/79) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk84LogOuter_valid :
    sk84LogOuterCertificate.check sk84Slice.outerAD.value = true := by
  norm_num [sk84LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk84Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk84LogK_valid :
    sk84LogKCertificate.check sk84Slice.kAD.value = true := by
  norm_num [sk84LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk84Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk84LogDArg_valid :
    sk84LogDArgCertificate.check sk84Slice.dArgAD.value = true := by
  norm_num [sk84LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk84Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk84ValidityFacts : SKFacts sk84Slice
    sk84LogOuterCertificate sk84LogKCertificate
    sk84LogDArgCertificate :=
  { domain := by norm_num [sk84Slice]
    kPositive := by
      norm_num [sk84Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk84LogOuter_valid
    logK := sk84LogK_valid
    logDArg := sk84LogDArg_valid }

noncomputable def sk84RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1304167/1048576), upper := (5254469/4194304) }
    logK := { lower := (7580885/8388608), upper := (1921601/2097152) }
    logDArg := { lower := (5492903/16777216), upper := (5856105/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk84LogOuterInput_eq :
    sk84RoundedInputs.logOuter = outerEnclosure 24
      (sk84LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk84LogKInput_eq :
    sk84RoundedInputs.logK = outerEnclosure 24
      (sk84LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk84LogDArgInput_eq :
    sk84RoundedInputs.logDArg = outerEnclosure 24
      (sk84LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk84RoundedFacts : SKRoundedFacts 8
    sk84LogOuterCertificate sk84LogKCertificate
    sk84LogDArgCertificate sk84RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk84LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk84LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk84LogDArgInput_eq }

noncomputable def sk85Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32) }

noncomputable def sk85LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3407727/2097152) }, upper := { exponent := 1, mantissa := (105/64) } }

noncomputable def sk85LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (9/8) }, upper := { exponent := 1, mantissa := (73/64) } }

noncomputable def sk85LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (54519975/38273024) }, upper := { exponent := 0, mantissa := (35/24) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk85LogOuter_valid :
    sk85LogOuterCertificate.check sk85Slice.outerAD.value = true := by
  norm_num [sk85LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk85Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk85LogK_valid :
    sk85LogKCertificate.check sk85Slice.kAD.value = true := by
  norm_num [sk85LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk85Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk85LogDArg_valid :
    sk85LogDArgCertificate.check sk85Slice.dArgAD.value = true := by
  norm_num [sk85LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk85Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk85ValidityFacts : SKFacts sk85Slice
    sk85LogOuterCertificate sk85LogKCertificate
    sk85LogDArgCertificate :=
  { domain := by norm_num [sk85Slice]
    kPositive := by
      norm_num [sk85Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk85LogOuter_valid
    logK := sk85LogK_valid
    logDArg := sk85LogDArg_valid }

noncomputable def sk85RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (19773835/16777216), upper := (19935099/16777216) }
    logK := { lower := (13605151/16777216), upper := (6918283/8388608) }
    logDArg := { lower := (5936145/16777216), upper := (6329947/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk85LogOuterInput_eq :
    sk85RoundedInputs.logOuter = outerEnclosure 24
      (sk85LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk85LogKInput_eq :
    sk85RoundedInputs.logK = outerEnclosure 24
      (sk85LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk85LogDArgInput_eq :
    sk85RoundedInputs.logDArg = outerEnclosure 24
      (sk85LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk85RoundedFacts : SKRoundedFacts 8
    sk85LogOuterCertificate sk85LogKCertificate
    sk85LogDArgCertificate sk85RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk85LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk85LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk85LogDArgInput_eq }

noncomputable def sk86Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16) }

noncomputable def sk86LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3440493/2097152) }, upper := { exponent := 1, mantissa := (53/32) } }

noncomputable def sk86LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (73/64) }, upper := { exponent := 1, mantissa := (37/32) } }

noncomputable def sk86LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (502279063/354025472) }, upper := { exponent := 0, mantissa := (106/73) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk86LogOuter_valid :
    sk86LogOuterCertificate.check sk86Slice.outerAD.value = true := by
  norm_num [sk86LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk86Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk86LogK_valid :
    sk86LogKCertificate.check sk86Slice.kAD.value = true := by
  norm_num [sk86LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk86Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk86LogDArg_valid :
    sk86LogDArgCertificate.check sk86Slice.dArgAD.value = true := by
  norm_num [sk86LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk86Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk86ValidityFacts : SKFacts sk86Slice
    sk86LogOuterCertificate sk86LogKCertificate
    sk86LogDArgCertificate :=
  { domain := by norm_num [sk86Slice]
    kPositive := by
      norm_num [sk86Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk86LogOuter_valid
    logK := sk86LogK_valid
    logDArg := sk86LogDArg_valid }

noncomputable def sk86RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (19934381/16777216), upper := (10047063/8388608) }
    logK := { lower := (3459141/4194304), upper := (14064831/16777216) }
    logDArg := { lower := (1467113/4194304), upper := (6257561/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk86LogOuterInput_eq :
    sk86RoundedInputs.logOuter = outerEnclosure 24
      (sk86LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk86LogKInput_eq :
    sk86RoundedInputs.logK = outerEnclosure 24
      (sk86LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk86LogDArgInput_eq :
    sk86RoundedInputs.logDArg = outerEnclosure 24
      (sk86LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk86RoundedFacts : SKRoundedFacts 8
    sk86LogOuterCertificate sk86LogKCertificate
    sk86LogDArgCertificate sk86RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk86LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk86LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk86LogDArgInput_eq }

noncomputable def sk87Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8) }

noncomputable def sk87LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (917463/524288) }, upper := { exponent := 1, mantissa := (29/16) } }

noncomputable def sk87LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (5/4) }, upper := { exponent := 1, mantissa := (21/16) } }

noncomputable def sk87LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (36665711/27525120) }, upper := { exponent := 0, mantissa := (29/20) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk87LogOuter_valid :
    sk87LogOuterCertificate.check sk87Slice.outerAD.value = true := by
  norm_num [sk87LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk87Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk87LogK_valid :
    sk87LogKCertificate.check sk87Slice.kAD.value = true := by
  norm_num [sk87LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk87Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk87LogDArg_valid :
    sk87LogDArgCertificate.check sk87Slice.dArgAD.value = true := by
  norm_num [sk87LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk87Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk87ValidityFacts : SKFacts sk87Slice
    sk87LogOuterCertificate sk87LogKCertificate
    sk87LogDArgCertificate :=
  { domain := by norm_num [sk87Slice]
    kPositive := by
      norm_num [sk87Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk87LogOuter_valid
    logK := sk87LogK_valid
    logDArg := sk87LogDArg_valid }

noncomputable def sk87RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (21017125/16777216), upper := (10803305/8388608) }
    logK := { lower := (15372807/16777216), upper := (16191371/16777216) }
    logDArg := { lower := (1202687/4194304), upper := (6233803/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk87LogOuterInput_eq :
    sk87RoundedInputs.logOuter = outerEnclosure 24
      (sk87LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk87LogKInput_eq :
    sk87RoundedInputs.logK = outerEnclosure 24
      (sk87LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk87LogDArgInput_eq :
    sk87RoundedInputs.logDArg = outerEnclosure 24
      (sk87LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk87RoundedFacts : SKRoundedFacts 8
    sk87LogOuterCertificate sk87LogKCertificate
    sk87LogDArgCertificate sk87RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk87LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk87LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk87LogDArgInput_eq }

noncomputable def sk88Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4) }

noncomputable def sk88LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (950229/524288) }, upper := { exponent := 1, mantissa := (15/8) } }

noncomputable def sk88LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (21/16) }, upper := { exponent := 1, mantissa := (11/8) } }

noncomputable def sk88LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (13292269/10092544) }, upper := { exponent := 0, mantissa := (10/7) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk88LogOuter_valid :
    sk88LogOuterCertificate.check sk88Slice.outerAD.value = true := by
  norm_num [sk88LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk88Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk88LogK_valid :
    sk88LogKCertificate.check sk88Slice.kAD.value = true := by
  norm_num [sk88LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk88Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk88LogDArg_valid :
    sk88LogDArgCertificate.check sk88Slice.dArgAD.value = true := by
  norm_num [sk88LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk88Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk88ValidityFacts : SKFacts sk88Slice
    sk88LogOuterCertificate sk88LogKCertificate
    sk88LogDArgCertificate :=
  { domain := by norm_num [sk88Slice]
    kPositive := by
      norm_num [sk88Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk88LogOuter_valid
    logK := sk88LogK_valid
    logDArg := sk88LogDArg_valid }

noncomputable def sk88RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (10802925/8388608), upper := (2771923/2097152) }
    logK := { lower := (8095685/8388608), upper := (2121481/2097152) }
    logDArg := { lower := (1155051/4194304), upper := (5984013/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk88LogOuterInput_eq :
    sk88RoundedInputs.logOuter = outerEnclosure 24
      (sk88LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk88LogKInput_eq :
    sk88RoundedInputs.logK = outerEnclosure 24
      (sk88LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk88LogDArgInput_eq :
    sk88RoundedInputs.logDArg = outerEnclosure 24
      (sk88LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk88RoundedFacts : SKRoundedFacts 8
    sk88LogOuterCertificate sk88LogKCertificate
    sk88LogDArgCertificate sk88RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk88LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk88LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk88LogDArgInput_eq }

noncomputable def sk89Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16) }

noncomputable def sk89LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1834927/1048576) }, upper := { exponent := 1, mantissa := (57/32) } }

noncomputable def sk89LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (5/4) }, upper := { exponent := 1, mantissa := (41/32) } }

noncomputable def sk89LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (146761311/107479040) }, upper := { exponent := 0, mantissa := (57/40) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk89LogOuter_valid :
    sk89LogOuterCertificate.check sk89Slice.outerAD.value = true := by
  norm_num [sk89LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk89Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk89LogK_valid :
    sk89LogKCertificate.check sk89Slice.kAD.value = true := by
  norm_num [sk89LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk89Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk89LogDArg_valid :
    sk89LogDArgCertificate.check sk89Slice.dArgAD.value = true := by
  norm_num [sk89LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk89Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk89ValidityFacts : SKFacts sk89Slice
    sk89LogOuterCertificate sk89LogKCertificate
    sk89LogDArgCertificate :=
  { domain := by norm_num [sk89Slice]
    kPositive := by
      norm_num [sk89Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk89LogOuter_valid
    logK := sk89LogK_valid
    logDArg := sk89LogDArg_valid }

noncomputable def sk89RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (10508567/8388608), upper := (21314825/16777216) }
    logK := { lower := (15372807/16777216), upper := (7893541/8388608) }
    logDArg := { lower := (2613149/8388608), upper := (2971009/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk89LogOuterInput_eq :
    sk89RoundedInputs.logOuter = outerEnclosure 24
      (sk89LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk89LogKInput_eq :
    sk89RoundedInputs.logK = outerEnclosure 24
      (sk89LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk89LogDArgInput_eq :
    sk89RoundedInputs.logDArg = outerEnclosure 24
      (sk89LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk89RoundedFacts : SKRoundedFacts 8
    sk89LogOuterCertificate sk89LogKCertificate
    sk89LogDArgCertificate sk89RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk89LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk89LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk89LogDArgInput_eq }

noncomputable def sk90Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8) }

noncomputable def sk90LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1867693/1048576) }, upper := { exponent := 1, mantissa := (29/16) } }

noncomputable def sk90LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (41/32) }, upper := { exponent := 1, mantissa := (21/16) } }

noncomputable def sk90LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (51039325/37617664) }, upper := { exponent := 0, mantissa := (58/41) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk90LogOuter_valid :
    sk90LogOuterCertificate.check sk90Slice.outerAD.value = true := by
  norm_num [sk90LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk90Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk90LogK_valid :
    sk90LogKCertificate.check sk90Slice.kAD.value = true := by
  norm_num [sk90LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk90Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk90LogDArg_valid :
    sk90LogDArgCertificate.check sk90Slice.dArgAD.value = true := by
  norm_num [sk90LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk90Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk90ValidityFacts : SKFacts sk90Slice
    sk90LogOuterCertificate sk90LogKCertificate
    sk90LogDArgCertificate :=
  { domain := by norm_num [sk90Slice]
    kPositive := by
      norm_num [sk90Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk90LogOuter_valid
    logK := sk90LogK_valid
    logDArg := sk90LogDArg_valid }

noncomputable def sk90RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (10657039/8388608), upper := (10803305/8388608) }
    logK := { lower := (1973385/2097152), upper := (16191371/16777216) }
    logDArg := { lower := (5119109/16777216), upper := (5819529/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk90LogOuterInput_eq :
    sk90RoundedInputs.logOuter = outerEnclosure 24
      (sk90LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk90LogKInput_eq :
    sk90RoundedInputs.logK = outerEnclosure 24
      (sk90LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk90LogDArgInput_eq :
    sk90RoundedInputs.logDArg = outerEnclosure 24
      (sk90LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk90RoundedFacts : SKRoundedFacts 8
    sk90LogOuterCertificate sk90LogKCertificate
    sk90LogDArgCertificate sk90RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk90LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk90LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk90LogDArgInput_eq }

noncomputable def sk91Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16) }

noncomputable def sk91LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1900459/1048576) }, upper := { exponent := 1, mantissa := (59/32) } }

noncomputable def sk91LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (21/16) }, upper := { exponent := 1, mantissa := (43/32) } }

noncomputable def sk91LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (53201901/39452672) }, upper := { exponent := 0, mantissa := (59/42) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk91LogOuter_valid :
    sk91LogOuterCertificate.check sk91Slice.outerAD.value = true := by
  norm_num [sk91LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk91Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk91LogK_valid :
    sk91LogKCertificate.check sk91Slice.kAD.value = true := by
  norm_num [sk91LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk91Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk91LogDArg_valid :
    sk91LogDArgCertificate.check sk91Slice.dArgAD.value = true := by
  norm_num [sk91LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk91Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk91ValidityFacts : SKFacts sk91Slice
    sk91LogOuterCertificate sk91LogKCertificate
    sk91LogDArgCertificate :=
  { domain := by norm_num [sk91Slice]
    kPositive := by
      norm_num [sk91Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk91LogOuter_valid
    logK := sk91LogK_valid
    logDArg := sk91LogDArg_valid }

noncomputable def sk91RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (21605859/16777216), upper := (21893407/16777216) }
    logK := { lower := (8095685/8388608), upper := (4146537/4194304) }
    logDArg := { lower := (5016259/16777216), upper := (1425509/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk91LogOuterInput_eq :
    sk91RoundedInputs.logOuter = outerEnclosure 24
      (sk91LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk91LogKInput_eq :
    sk91RoundedInputs.logK = outerEnclosure 24
      (sk91LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk91LogDArgInput_eq :
    sk91RoundedInputs.logDArg = outerEnclosure 24
      (sk91LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk91RoundedFacts : SKRoundedFacts 8
    sk91LogOuterCertificate sk91LogKCertificate
    sk91LogDArgCertificate sk91RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk91LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk91LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk91LogDArgInput_eq }

noncomputable def sk92Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4) }

noncomputable def sk92LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1933225/1048576) }, upper := { exponent := 1, mantissa := (15/8) } }

noncomputable def sk92LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (43/32) }, upper := { exponent := 1, mantissa := (11/8) } }

noncomputable def sk92LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (166224495/123994112) }, upper := { exponent := 0, mantissa := (60/43) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk92LogOuter_valid :
    sk92LogOuterCertificate.check sk92Slice.outerAD.value = true := by
  norm_num [sk92LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk92Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk92LogK_valid :
    sk92LogKCertificate.check sk92Slice.kAD.value = true := by
  norm_num [sk92LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk92Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk92LogDArg_valid :
    sk92LogDArgCertificate.check sk92Slice.dArgAD.value = true := by
  norm_num [sk92LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk92Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk92ValidityFacts : SKFacts sk92Slice
    sk92LogOuterCertificate sk92LogKCertificate
    sk92LogDArgCertificate :=
  { domain := by norm_num [sk92Slice]
    kPositive := by
      norm_num [sk92Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk92LogOuter_valid
    logK := sk92LogK_valid
    logDArg := sk92LogDArg_valid }

noncomputable def sk92RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (21892651/16777216), upper := (2771923/2097152) }
    logK := { lower := (8293073/8388608), upper := (2121481/2097152) }
    logDArg := { lower := (307343/1048576), upper := (5589237/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk92LogOuterInput_eq :
    sk92RoundedInputs.logOuter = outerEnclosure 24
      (sk92LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk92LogKInput_eq :
    sk92RoundedInputs.logK = outerEnclosure 24
      (sk92LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk92LogDArgInput_eq :
    sk92RoundedInputs.logDArg = outerEnclosure 24
      (sk92LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk92RoundedFacts : SKRoundedFacts 8
    sk92LogOuterCertificate sk92LogKCertificate
    sk92LogDArgCertificate sk92RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk92LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk92LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk92LogDArgInput_eq }

noncomputable def sk93Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8) }

noncomputable def sk93LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (982995/524288) }, upper := { exponent := 1, mantissa := (31/16) } }

noncomputable def sk93LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (11/8) }, upper := { exponent := 1, mantissa := (23/16) } }

noncomputable def sk93LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3928997/3014656) }, upper := { exponent := 0, mantissa := (31/22) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk93LogOuter_valid :
    sk93LogOuterCertificate.check sk93Slice.outerAD.value = true := by
  norm_num [sk93LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk93Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk93LogK_valid :
    sk93LogKCertificate.check sk93Slice.kAD.value = true := by
  norm_num [sk93LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk93Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk93LogDArg_valid :
    sk93LogDArgCertificate.check sk93Slice.dArgAD.value = true := by
  norm_num [sk93LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk93Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk93ValidityFacts : SKFacts sk93Slice
    sk93LogOuterCertificate sk93LogKCertificate
    sk93LogDArgCertificate :=
  { domain := by norm_num [sk93Slice]
    kPositive := by
      norm_num [sk93Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk93LogOuter_valid
    logK := sk93LogK_valid
    logDArg := sk93LogDArg_valid }

noncomputable def sk93RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (22174615/16777216), upper := (11362753/8388608) }
    logK := { lower := (8485923/8388608), upper := (17717625/16777216) }
    logDArg := { lower := (2222129/8388608), upper := (5753659/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk93LogOuterInput_eq :
    sk93RoundedInputs.logOuter = outerEnclosure 24
      (sk93LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk93LogKInput_eq :
    sk93RoundedInputs.logK = outerEnclosure 24
      (sk93LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk93LogDArgInput_eq :
    sk93RoundedInputs.logDArg = outerEnclosure 24
      (sk93LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk93RoundedFacts : SKRoundedFacts 8
    sk93LogOuterCertificate sk93LogKCertificate
    sk93LogDArgCertificate sk93RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk93LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk93LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk93LogDArgInput_eq }

noncomputable def sk94Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3) }

noncomputable def sk94LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1015761/524288) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk94LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (23/16) }, upper := { exponent := 1, mantissa := (3/2) } }

noncomputable def sk94LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (46692191/36175872) }, upper := { exponent := 0, mantissa := (32/23) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk94LogOuter_valid :
    sk94LogOuterCertificate.check sk94Slice.outerAD.value = true := by
  norm_num [sk94LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk94Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk94LogK_valid :
    sk94LogKCertificate.check sk94Slice.kAD.value = true := by
  norm_num [sk94LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk94Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk94LogDArg_valid :
    sk94LogDArgCertificate.check sk94Slice.dArgAD.value = true := by
  norm_num [sk94LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk94Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk94ValidityFacts : SKFacts sk94Slice
    sk94LogOuterCertificate sk94LogKCertificate
    sk94LogDArgCertificate :=
  { domain := by norm_num [sk94Slice]
    kPositive := by
      norm_num [sk94Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk94LogOuter_valid
    logK := sk94LogK_valid
    logDArg := sk94LogDArg_valid }

noncomputable def sk94RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2840591/2097152), upper := (23258161/16777216) }
    logK := { lower := (17717623/16777216), upper := (2303957/2097152) }
    logDArg := { lower := (2140643/8388608), upper := (5540537/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk94LogOuterInput_eq :
    sk94RoundedInputs.logOuter = outerEnclosure 24
      (sk94LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk94LogKInput_eq :
    sk94RoundedInputs.logK = outerEnclosure 24
      (sk94LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk94LogDArgInput_eq :
    sk94RoundedInputs.logDArg = outerEnclosure 24
      (sk94LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk94RoundedFacts : SKRoundedFacts 8
    sk94LogOuterCertificate sk94LogKCertificate
    sk94LogDArgCertificate sk94RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk94LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk94LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk94LogDArgInput_eq }

noncomputable def sk95Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16) }

noncomputable def sk95LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1965991/1048576) }, upper := { exponent := 1, mantissa := (61/32) } }

noncomputable def sk95LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (11/8) }, upper := { exponent := 1, mantissa := (45/32) } }

noncomputable def sk95LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (5241647/3932160) }, upper := { exponent := 0, mantissa := (61/44) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk95LogOuter_valid :
    sk95LogOuterCertificate.check sk95Slice.outerAD.value = true := by
  norm_num [sk95LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk95Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk95LogK_valid :
    sk95LogKCertificate.check sk95Slice.kAD.value = true := by
  norm_num [sk95LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk95Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk95LogDArg_valid :
    sk95LogDArgCertificate.check sk95Slice.dArgAD.value = true := by
  norm_num [sk95LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk95Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk95ValidityFacts : SKFacts sk95Slice
    sk95LogOuterCertificate sk95LogKCertificate
    sk95LogDArgCertificate :=
  { domain := by norm_num [sk95Slice]
    kPositive := by
      norm_num [sk95Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk95LogOuter_valid
    logK := sk95LogK_valid
    logDArg := sk95LogDArg_valid }

noncomputable def sk95RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (22174623/16777216), upper := (5613175/4194304) }
    logK := { lower := (8485923/8388608), upper := (1084305/1048576) }
    logDArg := { lower := (2411279/8388608), upper := (1370213/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk95LogOuterInput_eq :
    sk95RoundedInputs.logOuter = outerEnclosure 24
      (sk95LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk95LogKInput_eq :
    sk95RoundedInputs.logK = outerEnclosure 24
      (sk95LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk95LogDArgInput_eq :
    sk95RoundedInputs.logDArg = outerEnclosure 24
      (sk95LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk95RoundedFacts : SKRoundedFacts 8
    sk95LogOuterCertificate sk95LogKCertificate
    sk95LogDArgCertificate sk95RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk95LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk95LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk95LogDArgInput_eq }

noncomputable def sk96Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8) }

noncomputable def sk96LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1998757/1048576) }, upper := { exponent := 1, mantissa := (31/16) } }

noncomputable def sk96LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (45/32) }, upper := { exponent := 1, mantissa := (23/16) } }

noncomputable def sk96LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (19983919/15073280) }, upper := { exponent := 0, mantissa := (62/45) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk96LogOuter_valid :
    sk96LogOuterCertificate.check sk96Slice.outerAD.value = true := by
  norm_num [sk96LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk96Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk96LogK_valid :
    sk96LogKCertificate.check sk96Slice.kAD.value = true := by
  norm_num [sk96LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk96Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk96LogDArg_valid :
    sk96LogDArgCertificate.check sk96Slice.dArgAD.value = true := by
  norm_num [sk96LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk96Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk96ValidityFacts : SKFacts sk96Slice
    sk96LogOuterCertificate sk96LogKCertificate
    sk96LogDArgCertificate :=
  { domain := by norm_num [sk96Slice]
    kPositive := by
      norm_num [sk96Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk96LogOuter_valid
    logK := sk96LogK_valid
    logDArg := sk96LogDArg_valid }

noncomputable def sk96RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (22451935/16777216), upper := (11362753/8388608) }
    logK := { lower := (8674439/8388608), upper := (17717625/16777216) }
    logDArg := { lower := (2365623/8388608), upper := (5376627/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk96LogOuterInput_eq :
    sk96RoundedInputs.logOuter = outerEnclosure 24
      (sk96LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk96LogKInput_eq :
    sk96RoundedInputs.logK = outerEnclosure 24
      (sk96LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk96LogDArgInput_eq :
    sk96RoundedInputs.logDArg = outerEnclosure 24
      (sk96LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk96RoundedFacts : SKRoundedFacts 8
    sk96LogOuterCertificate sk96LogKCertificate
    sk96LogDArgCertificate sk96RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk96LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk96LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk96LogDArgInput_eq }

noncomputable def sk97Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16) }

noncomputable def sk97LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2031523/1048576) }, upper := { exponent := 1, mantissa := (63/32) } }

noncomputable def sk97LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (23/16) }, upper := { exponent := 1, mantissa := (47/32) } }

noncomputable def sk97LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (186867255/141688832) }, upper := { exponent := 0, mantissa := (63/46) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk97LogOuter_valid :
    sk97LogOuterCertificate.check sk97Slice.outerAD.value = true := by
  norm_num [sk97LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk97Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk97LogK_valid :
    sk97LogKCertificate.check sk97Slice.kAD.value = true := by
  norm_num [sk97LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk97Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk97LogDArg_valid :
    sk97LogDArgCertificate.check sk97Slice.dArgAD.value = true := by
  norm_num [sk97LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk97Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk97ValidityFacts : SKFacts sk97Slice
    sk97LogOuterCertificate sk97LogKCertificate
    sk97LogDArgCertificate :=
  { domain := by norm_num [sk97Slice]
    kPositive := by
      norm_num [sk97Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk97LogOuter_valid
    logK := sk97LogK_valid
    logDArg := sk97LogDArg_valid }

noncomputable def sk97RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (22724737/16777216), upper := (22993947/16777216) }
    logK := { lower := (17717623/16777216), upper := (18078439/16777216) }
    logDArg := { lower := (4643349/16777216), upper := (5276323/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk97LogOuterInput_eq :
    sk97RoundedInputs.logOuter = outerEnclosure 24
      (sk97LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk97LogKInput_eq :
    sk97RoundedInputs.logK = outerEnclosure 24
      (sk97LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk97LogDArgInput_eq :
    sk97RoundedInputs.logDArg = outerEnclosure 24
      (sk97LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk97RoundedFacts : SKRoundedFacts 8
    sk97LogOuterCertificate sk97LogKCertificate
    sk97LogDArgCertificate sk97RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk97LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk97LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk97LogDArgInput_eq }

noncomputable def sk98Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3) }

noncomputable def sk98LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2064289/1048576) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk98LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (47/32) }, upper := { exponent := 1, mantissa := (3/2) } }

noncomputable def sk98LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (64670101/49283072) }, upper := { exponent := 0, mantissa := (64/47) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk98LogOuter_valid :
    sk98LogOuterCertificate.check sk98Slice.outerAD.value = true := by
  norm_num [sk98LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk98Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk98LogK_valid :
    sk98LogKCertificate.check sk98Slice.kAD.value = true := by
  norm_num [sk98LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk98Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk98LogDArg_valid :
    sk98LogDArgCertificate.check sk98Slice.dArgAD.value = true := by
  norm_num [sk98LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk98Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk98ValidityFacts : SKFacts sk98Slice
    sk98LogOuterCertificate sk98LogKCertificate
    sk98LogDArgCertificate :=
  { domain := by norm_num [sk98Slice]
    kPositive := by
      norm_num [sk98Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk98LogOuter_valid
    logK := sk98LogK_valid
    logDArg := sk98LogDArg_valid }

noncomputable def sk98RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11496587/8388608), upper := (23258161/16777216) }
    logK := { lower := (9039219/8388608), upper := (2303957/2097152) }
    logDArg := { lower := (1139669/4194304), upper := (2589861/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk98LogOuterInput_eq :
    sk98RoundedInputs.logOuter = outerEnclosure 24
      (sk98LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk98LogKInput_eq :
    sk98RoundedInputs.logK = outerEnclosure 24
      (sk98LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk98LogDArgInput_eq :
    sk98RoundedInputs.logDArg = outerEnclosure 24
      (sk98LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk98RoundedFacts : SKRoundedFacts 8
    sk98LogOuterCertificate sk98LogKCertificate
    sk98LogDArgCertificate sk98RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk98LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk98LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk98LogDArgInput_eq }

noncomputable def sk99Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32) }

noncomputable def sk99LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3669855/2097152) }, upper := { exponent := 1, mantissa := (113/64) } }

noncomputable def sk99LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (5/4) }, upper := { exponent := 1, mantissa := (81/64) } }

noncomputable def sk99LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (587143871/424673280) }, upper := { exponent := 0, mantissa := (113/80) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk99LogOuter_valid :
    sk99LogOuterCertificate.check sk99Slice.outerAD.value = true := by
  norm_num [sk99LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk99Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk99LogK_valid :
    sk99LogKCertificate.check sk99Slice.kAD.value = true := by
  norm_num [sk99LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk99Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk99LogDArg_valid :
    sk99LogDArgCertificate.check sk99Slice.dArgAD.value = true := by
  norm_num [sk99LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk99Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk99ValidityFacts : SKFacts sk99Slice
    sk99LogOuterCertificate sk99LogKCertificate
    sk99LogDArgCertificate :=
  { domain := by norm_num [sk99Slice]
    kPositive := by
      norm_num [sk99Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk99LogOuter_valid
    logK := sk99LogK_valid
    logDArg := sk99LogDArg_valid }

noncomputable def sk99RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (10508569/8388608), upper := (21167007/16777216) }
    logK := { lower := (15372807/16777216), upper := (1947653/2097152) }
    logDArg := { lower := (5434975/16777216), upper := (724275/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk99LogOuterInput_eq :
    sk99RoundedInputs.logOuter = outerEnclosure 24
      (sk99LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk99LogKInput_eq :
    sk99RoundedInputs.logK = outerEnclosure 24
      (sk99LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk99LogDArgInput_eq :
    sk99RoundedInputs.logDArg = outerEnclosure 24
      (sk99LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk99RoundedFacts : SKRoundedFacts 8
    sk99LogOuterCertificate sk99LogKCertificate
    sk99LogDArgCertificate sk99RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk99LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk99LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk99LogDArgInput_eq }

noncomputable def sk100Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16) }

noncomputable def sk100LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3702621/2097152) }, upper := { exponent := 1, mantissa := (57/32) } }

noncomputable def sk100LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (81/64) }, upper := { exponent := 1, mantissa := (41/32) } }

noncomputable def sk100LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (66643519/48365568) }, upper := { exponent := 0, mantissa := (38/27) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk100LogOuter_valid :
    sk100LogOuterCertificate.check sk100Slice.outerAD.value = true := by
  norm_num [sk100LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk100Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk100LogK_valid :
    sk100LogKCertificate.check sk100Slice.kAD.value = true := by
  norm_num [sk100LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk100Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk100LogDArg_valid :
    sk100LogDArgCertificate.check sk100Slice.dArgAD.value = true := by
  norm_num [sk100LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk100Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk100ValidityFacts : SKFacts sk100Slice
    sk100LogOuterCertificate sk100LogKCertificate
    sk100LogDArgCertificate :=
  { domain := by norm_num [sk100Slice]
    kPositive := by
      norm_num [sk100Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk100LogOuter_valid
    logK := sk100LogK_valid
    logDArg := sk100LogDArg_valid }

noncomputable def sk100RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5291567/4194304), upper := (21314825/16777216) }
    logK := { lower := (7790611/8388608), upper := (7893541/8388608) }
    logDArg := { lower := (2689133/8388608), upper := (2866801/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk100LogOuterInput_eq :
    sk100RoundedInputs.logOuter = outerEnclosure 24
      (sk100LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk100LogKInput_eq :
    sk100RoundedInputs.logK = outerEnclosure 24
      (sk100LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk100LogDArgInput_eq :
    sk100RoundedInputs.logDArg = outerEnclosure 24
      (sk100LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk100RoundedFacts : SKRoundedFacts 8
    sk100LogOuterCertificate sk100LogKCertificate
    sk100LogDArgCertificate sk100RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk100LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk100LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk100LogDArgInput_eq }

noncomputable def sk101Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32) }

noncomputable def sk101LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3735387/2097152) }, upper := { exponent := 1, mantissa := (115/64) } }

noncomputable def sk101LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (41/32) }, upper := { exponent := 1, mantissa := (83/64) } }

noncomputable def sk101LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (612570535/446038016) }, upper := { exponent := 0, mantissa := (115/82) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk101LogOuter_valid :
    sk101LogOuterCertificate.check sk101Slice.outerAD.value = true := by
  norm_num [sk101LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk101Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk101LogK_valid :
    sk101LogKCertificate.check sk101Slice.kAD.value = true := by
  norm_num [sk101LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk101Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk101LogDArg_valid :
    sk101LogDArgCertificate.check sk101Slice.dArgAD.value = true := by
  norm_num [sk101LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk101Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk101ValidityFacts : SKFacts sk101Slice
    sk101LogOuterCertificate sk101LogKCertificate
    sk101LogDArgCertificate :=
  { domain := by norm_num [sk101Slice]
    kPositive := by
      norm_num [sk101Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk101LogOuter_valid
    logK := sk101LogK_valid
    logDArg := sk101LogDArg_valid }

noncomputable def sk101RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (21314083/16777216), upper := (2682669/2097152) }
    logK := { lower := (1973385/2097152), upper := (3997611/4194304) }
    logDArg := { lower := (2661369/8388608), upper := (5674271/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk101LogOuterInput_eq :
    sk101RoundedInputs.logOuter = outerEnclosure 24
      (sk101LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk101LogKInput_eq :
    sk101RoundedInputs.logK = outerEnclosure 24
      (sk101LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk101LogDArgInput_eq :
    sk101RoundedInputs.logDArg = outerEnclosure 24
      (sk101LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk101RoundedFacts : SKRoundedFacts 8
    sk101LogOuterCertificate sk101LogKCertificate
    sk101LogDArgCertificate sk101RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk101LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk101LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk101LogDArgInput_eq }

noncomputable def sk102Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8) }

noncomputable def sk102LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3768153/2097152) }, upper := { exponent := 1, mantissa := (29/16) } }

noncomputable def sk102LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (83/64) }, upper := { exponent := 1, mantissa := (21/16) } }

noncomputable def sk102LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (625480463/456916992) }, upper := { exponent := 0, mantissa := (116/83) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk102LogOuter_valid :
    sk102LogOuterCertificate.check sk102Slice.outerAD.value = true := by
  norm_num [sk102LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk102Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk102LogK_valid :
    sk102LogKCertificate.check sk102Slice.kAD.value = true := by
  norm_num [sk102LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk102Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk102LogDArg_valid :
    sk102LogDArgCertificate.check sk102Slice.dArgAD.value = true := by
  norm_num [sk102LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk102Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk102ValidityFacts : SKFacts sk102Slice
    sk102LogOuterCertificate sk102LogKCertificate
    sk102LogDArgCertificate :=
  { domain := by norm_num [sk102Slice]
    kPositive := by
      norm_num [sk102Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk102LogOuter_valid
    logK := sk102LogK_valid
    logDArg := sk102LogDArg_valid }

noncomputable def sk102RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (21460607/16777216), upper := (10803305/8388608) }
    logK := { lower := (15990443/16777216), upper := (16191371/16777216) }
    logDArg := { lower := (5268353/16777216), upper := (5616167/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk102LogOuterInput_eq :
    sk102RoundedInputs.logOuter = outerEnclosure 24
      (sk102LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk102LogKInput_eq :
    sk102RoundedInputs.logK = outerEnclosure 24
      (sk102LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk102LogDArgInput_eq :
    sk102RoundedInputs.logDArg = outerEnclosure 24
      (sk102LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk102RoundedFacts : SKRoundedFacts 8
    sk102LogOuterCertificate sk102LogKCertificate
    sk102LogDArgCertificate sk102RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk102LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk102LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk102LogDArgInput_eq }

noncomputable def sk103Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32) }

noncomputable def sk103LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3866451/2097152) }, upper := { exponent := 1, mantissa := (119/64) } }

noncomputable def sk103LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (43/32) }, upper := { exponent := 1, mantissa := (87/64) } }

noncomputable def sk103LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (664996631/490340352) }, upper := { exponent := 0, mantissa := (119/86) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk103LogOuter_valid :
    sk103LogOuterCertificate.check sk103Slice.outerAD.value = true := by
  norm_num [sk103LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk103Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk103LogK_valid :
    sk103LogKCertificate.check sk103Slice.kAD.value = true := by
  norm_num [sk103LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk103Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk103LogDArg_valid :
    sk103LogDArgCertificate.check sk103Slice.dArgAD.value = true := by
  norm_num [sk103LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk103Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk103ValidityFacts : SKFacts sk103Slice
    sk103LogOuterCertificate sk103LogKCertificate
    sk103LogDArgCertificate :=
  { domain := by norm_num [sk103Slice]
    kPositive := by
      norm_num [sk103Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk103LogOuter_valid
    logK := sk103LogK_valid
    logDArg := sk103LogDArg_valid }

noncomputable def sk103RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (21892655/16777216), upper := (5508747/4194304) }
    logK := { lower := (8293073/8388608), upper := (8390053/8388608) }
    logDArg := { lower := (5111719/16777216), upper := (5448841/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk103LogOuterInput_eq :
    sk103RoundedInputs.logOuter = outerEnclosure 24
      (sk103LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk103LogKInput_eq :
    sk103RoundedInputs.logK = outerEnclosure 24
      (sk103LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk103LogDArgInput_eq :
    sk103RoundedInputs.logDArg = outerEnclosure 24
      (sk103LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk103RoundedFacts : SKRoundedFacts 8
    sk103LogOuterCertificate sk103LogKCertificate
    sk103LogDArgCertificate sk103RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk103LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk103LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk103LogDArgInput_eq }

noncomputable def sk104Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4) }

noncomputable def sk104LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3899217/2097152) }, upper := { exponent := 1, mantissa := (15/8) } }

noncomputable def sk104LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (87/64) }, upper := { exponent := 1, mantissa := (11/8) } }

noncomputable def sk104LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (226143605/167247872) }, upper := { exponent := 0, mantissa := (40/29) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk104LogOuter_valid :
    sk104LogOuterCertificate.check sk104Slice.outerAD.value = true := by
  norm_num [sk104LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk104Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk104LogK_valid :
    sk104LogKCertificate.check sk104Slice.kAD.value = true := by
  norm_num [sk104LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk104Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk104LogDArg_valid :
    sk104LogDArgCertificate.check sk104Slice.dArgAD.value = true := by
  norm_num [sk104LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk104Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk104ValidityFacts : SKFacts sk104Slice
    sk104LogOuterCertificate sk104LogKCertificate
    sk104LogDArgCertificate :=
  { domain := by norm_num [sk104Slice]
    kPositive := by
      norm_num [sk104Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk104LogOuter_valid
    logK := sk104LogK_valid
    logDArg := sk104LogDArg_valid }

noncomputable def sk104RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11017117/8388608), upper := (2771923/2097152) }
    logK := { lower := (16780105/16777216), upper := (2121481/2097152) }
    logDArg := { lower := (1265393/4194304), upper := (2697639/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk104LogOuterInput_eq :
    sk104RoundedInputs.logOuter = outerEnclosure 24
      (sk104LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk104LogKInput_eq :
    sk104RoundedInputs.logK = outerEnclosure 24
      (sk104LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk104LogDArgInput_eq :
    sk104RoundedInputs.logDArg = outerEnclosure 24
      (sk104LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk104RoundedFacts : SKRoundedFacts 8
    sk104LogOuterCertificate sk104LogKCertificate
    sk104LogDArgCertificate sk104RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk104LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk104LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk104LogDArgInput_eq }

noncomputable def sk105Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32) }

noncomputable def sk105LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3800919/2097152) }, upper := { exponent := 1, mantissa := (117/64) } }

noncomputable def sk105LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (21/16) }, upper := { exponent := 1, mantissa := (85/64) } }

noncomputable def sk105LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (42568097/31195136) }, upper := { exponent := 0, mantissa := (39/28) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk105LogOuter_valid :
    sk105LogOuterCertificate.check sk105Slice.outerAD.value = true := by
  norm_num [sk105LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk105Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk105LogK_valid :
    sk105LogKCertificate.check sk105Slice.kAD.value = true := by
  norm_num [sk105LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk105Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk105LogDArg_valid :
    sk105LogDArgCertificate.check sk105Slice.dArgAD.value = true := by
  norm_num [sk105LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk105Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk105ValidityFacts : SKFacts sk105Slice
    sk105LogOuterCertificate sk105LogKCertificate
    sk105LogDArgCertificate :=
  { domain := by norm_num [sk105Slice]
    kPositive := by
      norm_num [sk105Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk105LogOuter_valid
    logK := sk105LogK_valid
    logDArg := sk105LogDArg_valid }

noncomputable def sk105RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (21605863/16777216), upper := (10875311/8388608) }
    logK := { lower := (8095685/8388608), upper := (16389921/16777216) }
    logDArg := { lower := (2607539/8388608), upper := (5559251/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk105LogOuterInput_eq :
    sk105RoundedInputs.logOuter = outerEnclosure 24
      (sk105LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk105LogKInput_eq :
    sk105RoundedInputs.logK = outerEnclosure 24
      (sk105LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk105LogDArgInput_eq :
    sk105RoundedInputs.logDArg = outerEnclosure 24
      (sk105LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk105RoundedFacts : SKRoundedFacts 8
    sk105LogOuterCertificate sk105LogKCertificate
    sk105LogDArgCertificate sk105RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk105LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk105LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk105LogDArgInput_eq }

noncomputable def sk106Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16) }

noncomputable def sk106LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3833685/2097152) }, upper := { exponent := 1, mantissa := (59/32) } }

noncomputable def sk106LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (85/64) }, upper := { exponent := 1, mantissa := (43/32) } }

noncomputable def sk106LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (651693511/479068160) }, upper := { exponent := 0, mantissa := (118/85) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk106LogOuter_valid :
    sk106LogOuterCertificate.check sk106Slice.outerAD.value = true := by
  norm_num [sk106LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk106Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk106LogK_valid :
    sk106LogKCertificate.check sk106Slice.kAD.value = true := by
  norm_num [sk106LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk106Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk106LogDArg_valid :
    sk106LogDArgCertificate.check sk106Slice.dArgAD.value = true := by
  norm_num [sk106LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk106Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk106ValidityFacts : SKFacts sk106Slice
    sk106LogOuterCertificate sk106LogKCertificate
    sk106LogDArgCertificate :=
  { domain := by norm_num [sk106Slice]
    kPositive := by
      norm_num [sk106Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk106LogOuter_valid
    logK := sk106LogK_valid
    logDArg := sk106LogDArg_valid }

noncomputable def sk106RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (1359367/1048576), upper := (21893407/16777216) }
    logK := { lower := (16389919/16777216), upper := (4146537/4194304) }
    logDArg := { lower := (5162877/16777216), upper := (5503487/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk106LogOuterInput_eq :
    sk106RoundedInputs.logOuter = outerEnclosure 24
      (sk106LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk106LogKInput_eq :
    sk106RoundedInputs.logK = outerEnclosure 24
      (sk106LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk106LogDArgInput_eq :
    sk106RoundedInputs.logDArg = outerEnclosure 24
      (sk106LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk106RoundedFacts : SKRoundedFacts 8
    sk106LogOuterCertificate sk106LogKCertificate
    sk106LogDArgCertificate sk106RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk106LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk106LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk106LogDArgInput_eq }

noncomputable def sk107Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32) }

noncomputable def sk107LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3931983/2097152) }, upper := { exponent := 1, mantissa := (121/64) } }

noncomputable def sk107LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (11/8) }, upper := { exponent := 1, mantissa := (89/64) } }

noncomputable def sk107LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (62908733/46661632) }, upper := { exponent := 0, mantissa := (11/8) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk107LogOuter_valid :
    sk107LogOuterCertificate.check sk107Slice.outerAD.value = true := by
  norm_num [sk107LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk107Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk107LogK_valid :
    sk107LogKCertificate.check sk107Slice.kAD.value = true := by
  norm_num [sk107LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk107Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk107LogDArg_valid :
    sk107LogDArgCertificate.check sk107Slice.dArgAD.value = true := by
  norm_num [sk107LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk107Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk107ValidityFacts : SKFacts sk107Slice
    sk107LogOuterCertificate sk107LogKCertificate
    sk107LogDArgCertificate :=
  { domain := by norm_num [sk107Slice]
    kPositive := by
      norm_num [sk107Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk107LogOuter_valid
    logK := sk107LogK_valid
    logDArg := sk107LogDArg_valid }

noncomputable def sk107RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (22174627/16777216), upper := (22314615/16777216) }
    logK := { lower := (8485923/8388608), upper := (17161423/16777216) }
    logDArg := { lower := (5012407/16777216), upper := (333923/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk107LogOuterInput_eq :
    sk107RoundedInputs.logOuter = outerEnclosure 24
      (sk107LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk107LogKInput_eq :
    sk107RoundedInputs.logK = outerEnclosure 24
      (sk107LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk107LogDArgInput_eq :
    sk107RoundedInputs.logDArg = outerEnclosure 24
      (sk107LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk107RoundedFacts : SKRoundedFacts 8
    sk107LogOuterCertificate sk107LogKCertificate
    sk107LogDArgCertificate sk107RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk107LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk107LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk107LogDArgInput_eq }

noncomputable def sk108Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16) }

noncomputable def sk108LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3964749/2097152) }, upper := { exponent := 1, mantissa := (61/32) } }

noncomputable def sk108LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (89/64) }, upper := { exponent := 1, mantissa := (45/32) } }

noncomputable def sk108LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (141138475/104988672) }, upper := { exponent := 0, mantissa := (122/89) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk108LogOuter_valid :
    sk108LogOuterCertificate.check sk108Slice.outerAD.value = true := by
  norm_num [sk108LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk108Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk108LogK_valid :
    sk108LogKCertificate.check sk108Slice.kAD.value = true := by
  norm_num [sk108LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk108Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk108LogDArg_valid :
    sk108LogDArgCertificate.check sk108Slice.dArgAD.value = true := by
  norm_num [sk108LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk108Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk108ValidityFacts : SKFacts sk108Slice
    sk108LogOuterCertificate sk108LogKCertificate
    sk108LogDArgCertificate :=
  { domain := by norm_num [sk108Slice]
    kPositive := by
      norm_num [sk108Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk108LogOuter_valid
    logK := sk108LogK_valid
    logDArg := sk108LogDArg_valid }

noncomputable def sk108RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (174327/131072), upper := (5613175/4194304) }
    logK := { lower := (8580711/8388608), upper := (1084305/1048576) }
    logDArg := { lower := (2482097/8388608), upper := (5291277/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk108LogOuterInput_eq :
    sk108RoundedInputs.logOuter = outerEnclosure 24
      (sk108LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk108LogKInput_eq :
    sk108RoundedInputs.logK = outerEnclosure 24
      (sk108LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk108LogDArgInput_eq :
    sk108RoundedInputs.logDArg = outerEnclosure 24
      (sk108LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk108RoundedFacts : SKRoundedFacts 8
    sk108LogOuterCertificate sk108LogKCertificate
    sk108LogDArgCertificate sk108RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk108LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk108LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk108LogDArgInput_eq }

noncomputable def sk109Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32) }

noncomputable def sk109LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3997515/2097152) }, upper := { exponent := 1, mantissa := (123/64) } }

noncomputable def sk109LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (45/32) }, upper := { exponent := 1, mantissa := (91/64) } }

noncomputable def sk109LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (79946639/59637760) }, upper := { exponent := 0, mantissa := (41/30) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk109LogOuter_valid :
    sk109LogOuterCertificate.check sk109Slice.outerAD.value = true := by
  norm_num [sk109LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk109Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk109LogK_valid :
    sk109LogKCertificate.check sk109Slice.kAD.value = true := by
  norm_num [sk109LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk109Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk109LogDArg_valid :
    sk109LogDArgCertificate.check sk109Slice.dArgAD.value = true := by
  norm_num [sk109LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk109Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk109ValidityFacts : SKFacts sk109Slice
    sk109LogOuterCertificate sk109LogKCertificate
    sk109LogDArgCertificate :=
  { domain := by norm_num [sk109Slice]
    kPositive := by
      norm_num [sk109Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk109LogOuter_valid
    logK := sk109LogK_valid
    logDArg := sk109LogDArg_valid }

noncomputable def sk109RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (22451939/16777216), upper := (22589657/16777216) }
    logK := { lower := (8674439/8388608), upper := (17534265/16777216) }
    logDArg := { lower := (2458453/8388608), upper := (2620389/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk109LogOuterInput_eq :
    sk109RoundedInputs.logOuter = outerEnclosure 24
      (sk109LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk109LogKInput_eq :
    sk109RoundedInputs.logK = outerEnclosure 24
      (sk109LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk109LogDArgInput_eq :
    sk109RoundedInputs.logDArg = outerEnclosure 24
      (sk109LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk109RoundedFacts : SKRoundedFacts 8
    sk109LogOuterCertificate sk109LogKCertificate
    sk109LogDArgCertificate sk109RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk109LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk109LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk109LogDArgInput_eq }

noncomputable def sk110Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8) }

noncomputable def sk110LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4030281/2097152) }, upper := { exponent := 1, mantissa := (31/16) } }

noncomputable def sk110LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (91/64) }, upper := { exponent := 1, mantissa := (23/16) } }

noncomputable def sk110LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (733478191/548667392) }, upper := { exponent := 0, mantissa := (124/91) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk110LogOuter_valid :
    sk110LogOuterCertificate.check sk110Slice.outerAD.value = true := by
  norm_num [sk110LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk110Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk110LogK_valid :
    sk110LogKCertificate.check sk110Slice.kAD.value = true := by
  norm_num [sk110LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk110Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk110LogDArg_valid :
    sk110LogDArgCertificate.check sk110Slice.dArgAD.value = true := by
  norm_num [sk110LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk110Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk110ValidityFacts : SKFacts sk110Slice
    sk110LogOuterCertificate sk110LogKCertificate
    sk110LogDArgCertificate :=
  { domain := by norm_num [sk110Slice]
    kPositive := by
      norm_num [sk110Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk110LogOuter_valid
    logK := sk110LogK_valid
    logDArg := sk110LogDArg_valid }

noncomputable def sk110RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11294447/8388608), upper := (11362753/8388608) }
    logK := { lower := (2191783/2097152), upper := (17717625/16777216) }
    logDArg := { lower := (4870517/16777216), upper := (5191241/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk110LogOuterInput_eq :
    sk110RoundedInputs.logOuter = outerEnclosure 24
      (sk110LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk110LogKInput_eq :
    sk110RoundedInputs.logK = outerEnclosure 24
      (sk110LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk110LogDArgInput_eq :
    sk110RoundedInputs.logDArg = outerEnclosure 24
      (sk110LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk110RoundedFacts : SKRoundedFacts 8
    sk110LogOuterCertificate sk110LogKCertificate
    sk110LogDArgCertificate sk110RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk110LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk110LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk110LogDArgInput_eq }

noncomputable def sk111Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32) }

noncomputable def sk111LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4063047/2097152) }, upper := { exponent := 1, mantissa := (125/64) } }

noncomputable def sk111LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (23/16) }, upper := { exponent := 1, mantissa := (93/64) } }

noncomputable def sk111LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (747567695/560726016) }, upper := { exponent := 0, mantissa := (125/92) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk111LogOuter_valid :
    sk111LogOuterCertificate.check sk111Slice.outerAD.value = true := by
  norm_num [sk111LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk111Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk111LogK_valid :
    sk111LogKCertificate.check sk111Slice.kAD.value = true := by
  norm_num [sk111LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk111Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk111LogDArg_valid :
    sk111LogDArgCertificate.check sk111Slice.dArgAD.value = true := by
  norm_num [sk111LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk111Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk111ValidityFacts : SKFacts sk111Slice
    sk111LogOuterCertificate sk111LogKCertificate
    sk111LogDArgCertificate :=
  { domain := by norm_num [sk111Slice]
    kPositive := by
      norm_num [sk111Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk111LogOuter_valid
    logK := sk111LogK_valid
    logDArg := sk111LogDArg_valid }

noncomputable def sk111RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (22724741/16777216), upper := (2857533/2097152) }
    logK := { lower := (17717623/16777216), upper := (8949501/8388608) }
    logDArg := { lower := (603125/2097152), upper := (5142639/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk111LogOuterInput_eq :
    sk111RoundedInputs.logOuter = outerEnclosure 24
      (sk111LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk111LogKInput_eq :
    sk111RoundedInputs.logK = outerEnclosure 24
      (sk111LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk111LogDArgInput_eq :
    sk111RoundedInputs.logDArg = outerEnclosure 24
      (sk111LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk111RoundedFacts : SKRoundedFacts 8
    sk111LogOuterCertificate sk111LogKCertificate
    sk111LogDArgCertificate sk111RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk111LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk111LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk111LogDArgInput_eq }

noncomputable def sk112Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16) }

noncomputable def sk112LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4095813/2097152) }, upper := { exponent := 1, mantissa := (63/32) } }

noncomputable def sk112LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (93/64) }, upper := { exponent := 1, mantissa := (47/32) } }

noncomputable def sk112LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (253929421/190971904) }, upper := { exponent := 0, mantissa := (42/31) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk112LogOuter_valid :
    sk112LogOuterCertificate.check sk112Slice.outerAD.value = true := by
  norm_num [sk112LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk112Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk112LogK_valid :
    sk112LogKCertificate.check sk112Slice.kAD.value = true := by
  norm_num [sk112LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk112Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk112LogDArg_valid :
    sk112LogDArgCertificate.check sk112Slice.dArgAD.value = true := by
  norm_num [sk112LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk112Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk112ValidityFacts : SKFacts sk112Slice
    sk112LogOuterCertificate sk112LogKCertificate
    sk112LogDArgCertificate :=
  { domain := by norm_num [sk112Slice]
    kPositive := by
      norm_num [sk112Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk112LogOuter_valid
    logK := sk112LogK_valid
    logDArg := sk112LogDArg_valid }

noncomputable def sk112RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2857437/2097152), upper := (22993947/16777216) }
    logK := { lower := (2237375/2097152), upper := (18078439/16777216) }
    logDArg := { lower := (1195083/4194304), upper := (2547473/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk112LogOuterInput_eq :
    sk112RoundedInputs.logOuter = outerEnclosure 24
      (sk112LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk112LogKInput_eq :
    sk112RoundedInputs.logK = outerEnclosure 24
      (sk112LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk112LogDArgInput_eq :
    sk112RoundedInputs.logDArg = outerEnclosure 24
      (sk112LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk112RoundedFacts : SKRoundedFacts 8
    sk112LogOuterCertificate sk112LogKCertificate
    sk112LogDArgCertificate sk112RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk112LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk112LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk112LogDArgInput_eq }

noncomputable def sk113Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32) }

noncomputable def sk113LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4128579/2097152) }, upper := { exponent := 1, mantissa := (127/64) } }

noncomputable def sk113LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (47/32) }, upper := { exponent := 1, mantissa := (95/64) } }

noncomputable def sk113LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (155227979/117047296) }, upper := { exponent := 0, mantissa := (127/94) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk113LogOuter_valid :
    sk113LogOuterCertificate.check sk113Slice.outerAD.value = true := by
  norm_num [sk113LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk113Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk113LogK_valid :
    sk113LogKCertificate.check sk113Slice.kAD.value = true := by
  norm_num [sk113LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk113Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk113LogDArg_valid :
    sk113LogDArgCertificate.check sk113Slice.dArgAD.value = true := by
  norm_num [sk113LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk113Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk113ValidityFacts : SKFacts sk113Slice
    sk113LogOuterCertificate sk113LogKCertificate
    sk113LogDArgCertificate :=
  { domain := by norm_num [sk113Slice]
    kPositive := by
      norm_num [sk113Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk113LogOuter_valid
    logK := sk113LogK_valid
    logDArg := sk113LogDArg_valid }

noncomputable def sk113RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11496589/8388608), upper := (11563287/8388608) }
    logK := { lower := (9039219/8388608), upper := (18255977/16777216) }
    logDArg := { lower := (4736489/16777216), upper := (631017/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk113LogOuterInput_eq :
    sk113RoundedInputs.logOuter = outerEnclosure 24
      (sk113LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk113LogKInput_eq :
    sk113RoundedInputs.logK = outerEnclosure 24
      (sk113LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk113LogDArgInput_eq :
    sk113RoundedInputs.logDArg = outerEnclosure 24
      (sk113LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk113RoundedFacts : SKRoundedFacts 8
    sk113LogOuterCertificate sk113LogKCertificate
    sk113LogDArgCertificate sk113RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk113LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk113LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk113LogDArgInput_eq }

noncomputable def sk114Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3) }

noncomputable def sk114LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (4161345/2097152) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk114LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (95/64) }, upper := { exponent := 1, mantissa := (3/2) } }

noncomputable def sk114LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (790622591/597688320) }, upper := { exponent := 0, mantissa := (128/95) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk114LogOuter_valid :
    sk114LogOuterCertificate.check sk114Slice.outerAD.value = true := by
  norm_num [sk114LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk114Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk114LogK_valid :
    sk114LogKCertificate.check sk114Slice.kAD.value = true := by
  norm_num [sk114LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk114Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk114LogDArg_valid :
    sk114LogDArgCertificate.check sk114Slice.dArgAD.value = true := by
  norm_num [sk114LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk114Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk114ValidityFacts : SKFacts sk114Slice
    sk114LogOuterCertificate sk114LogKCertificate
    sk114LogDArgCertificate :=
  { domain := by norm_num [sk114Slice]
    kPositive := by
      norm_num [sk114Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk114LogOuter_valid
    logK := sk114LogK_valid
    logDArg := sk114LogDArg_valid }

noncomputable def sk114RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23125803/16777216), upper := (23258161/16777216) }
    logK := { lower := (2281997/2097152), upper := (2303957/2097152) }
    logDArg := { lower := (586681/2097152), upper := (625273/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk114LogOuterInput_eq :
    sk114RoundedInputs.logOuter = outerEnclosure 24
      (sk114LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk114LogKInput_eq :
    sk114RoundedInputs.logK = outerEnclosure 24
      (sk114LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk114LogDArgInput_eq :
    sk114RoundedInputs.logDArg = outerEnclosure 24
      (sk114LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk114RoundedFacts : SKRoundedFacts 8
    sk114LogOuterCertificate sk114LogKCertificate
    sk114LogDArgCertificate sk114RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk114LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk114LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk114LogDArgInput_eq }

noncomputable def sk115Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64) }

noncomputable def sk115LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (8257159/4194304) }, upper := { exponent := 1, mantissa := (253/128) } }

noncomputable def sk115LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (47/32) }, upper := { exponent := 1, mantissa := (189/128) } }

noncomputable def sk115LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (114987357/86245376) }, upper := { exponent := 0, mantissa := (253/188) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk115LogOuter_valid :
    sk115LogOuterCertificate.check sk115Slice.outerAD.value = true := by
  norm_num [sk115LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk115Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk115LogK_valid :
    sk115LogKCertificate.check sk115Slice.kAD.value = true := by
  norm_num [sk115LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk115Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk115LogDArg_valid :
    sk115LogDArgCertificate.check sk115Slice.dArgAD.value = true := by
  norm_num [sk115LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk115Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk115ValidityFacts : SKFacts sk115Slice
    sk115LogOuterCertificate sk115LogKCertificate
    sk115LogDArgCertificate :=
  { domain := by norm_num [sk115Slice]
    kPositive := by
      norm_num [sk115Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk115LogOuter_valid
    logK := sk115LogK_valid
    logDArg := sk115LogDArg_valid }

noncomputable def sk115RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (5748295/4194304), upper := (2882549/2097152) }
    logK := { lower := (9039219/8388608), upper := (18167443/16777216) }
    logDArg := { lower := (4825559/16777216), upper := (4981953/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk115LogOuterInput_eq :
    sk115RoundedInputs.logOuter = outerEnclosure 24
      (sk115LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk115LogKInput_eq :
    sk115RoundedInputs.logK = outerEnclosure 24
      (sk115LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk115LogDArgInput_eq :
    sk115RoundedInputs.logDArg = outerEnclosure 24
      (sk115LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk115RoundedFacts : SKRoundedFacts 8
    sk115LogOuterCertificate sk115LogKCertificate
    sk115LogDArgCertificate sk115RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk115LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk115LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk115LogDArgInput_eq }

noncomputable def sk116Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32) }

noncomputable def sk116LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (8289925/4194304) }, upper := { exponent := 1, mantissa := (127/64) } }

noncomputable def sk116LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (189/128) }, upper := { exponent := 1, mantissa := (95/64) } }

noncomputable def sk116LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (348173167/261488640) }, upper := { exponent := 0, mantissa := (254/189) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk116LogOuter_valid :
    sk116LogOuterCertificate.check sk116Slice.outerAD.value = true := by
  norm_num [sk116LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk116Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk116LogK_valid :
    sk116LogKCertificate.check sk116Slice.kAD.value = true := by
  norm_num [sk116LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk116Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk116LogDArg_valid :
    sk116LogDArgCertificate.check sk116Slice.dArgAD.value = true := by
  norm_num [sk116LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk116Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk116ValidityFacts : SKFacts sk116Slice
    sk116LogOuterCertificate sk116LogKCertificate
    sk116LogDArgCertificate :=
  { domain := by norm_num [sk116Slice]
    kPositive := by
      norm_num [sk116Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk116LogOuter_valid
    logK := sk116LogK_valid
    logDArg := sk116LogDArg_valid }

noncomputable def sk116RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23059623/16777216), upper := (11563287/8388608) }
    logK := { lower := (9083721/8388608), upper := (18255977/16777216) }
    logDArg := { lower := (4803469/16777216), upper := (1239783/4194304) } }

set_option maxRecDepth 1000000 in
private theorem sk116LogOuterInput_eq :
    sk116RoundedInputs.logOuter = outerEnclosure 24
      (sk116LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk116LogKInput_eq :
    sk116RoundedInputs.logK = outerEnclosure 24
      (sk116LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk116LogDArgInput_eq :
    sk116RoundedInputs.logDArg = outerEnclosure 24
      (sk116LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk116RoundedFacts : SKRoundedFacts 8
    sk116LogOuterCertificate sk116LogKCertificate
    sk116LogDArgCertificate sk116RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk116LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk116LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk116LogDArgInput_eq }

noncomputable def sk117Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64) }

noncomputable def sk117LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (8322691/4194304) }, upper := { exponent := 1, mantissa := (255/128) } }

noncomputable def sk117LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (95/64) }, upper := { exponent := 1, mantissa := (191/128) } }

noncomputable def sk117LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (3162589431/2378301440) }, upper := { exponent := 0, mantissa := (51/38) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk117LogOuter_valid :
    sk117LogOuterCertificate.check sk117Slice.outerAD.value = true := by
  norm_num [sk117LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk117Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk117LogK_valid :
    sk117LogKCertificate.check sk117Slice.kAD.value = true := by
  norm_num [sk117LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk117Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk117LogDArg_valid :
    sk117LogDArgCertificate.check sk117Slice.dArgAD.value = true := by
  norm_num [sk117LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk117Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk117ValidityFacts : SKFacts sk117Slice
    sk117LogOuterCertificate sk117LogKCertificate
    sk117LogDArgCertificate :=
  { domain := by norm_num [sk117Slice]
    kPositive := by
      norm_num [sk117Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk117LogOuter_valid
    logK := sk117LogK_valid
    logDArg := sk117LogDArg_valid }

noncomputable def sk117RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23125805/16777216), upper := (23192497/16777216) }
    logK := { lower := (2281997/2097152), upper := (18344047/16777216) }
    logDArg := { lower := (4781583/16777216), upper := (617065/2097152) } }

set_option maxRecDepth 1000000 in
private theorem sk117LogOuterInput_eq :
    sk117RoundedInputs.logOuter = outerEnclosure 24
      (sk117LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk117LogKInput_eq :
    sk117RoundedInputs.logK = outerEnclosure 24
      (sk117LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk117LogDArgInput_eq :
    sk117RoundedInputs.logDArg = outerEnclosure 24
      (sk117LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk117RoundedFacts : SKRoundedFacts 8
    sk117LogOuterCertificate sk117LogKCertificate
    sk117LogDArgCertificate sk117RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk117LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk117LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk117LogDArgInput_eq }

noncomputable def sk118Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3) }

noncomputable def sk118LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (8355457/4194304) }, upper := { exponent := 2, mantissa := (1) } }

noncomputable def sk118LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (191/128) }, upper := { exponent := 1, mantissa := (3/2) } }

noncomputable def sk118LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1063917141/801112064) }, upper := { exponent := 0, mantissa := (256/191) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk118LogOuter_valid :
    sk118LogOuterCertificate.check sk118Slice.outerAD.value = true := by
  norm_num [sk118LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk118Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk118LogK_valid :
    sk118LogKCertificate.check sk118Slice.kAD.value = true := by
  norm_num [sk118LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk118Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk118LogDArg_valid :
    sk118LogDArgCertificate.check sk118Slice.dArgAD.value = true := by
  norm_num [sk118LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk118Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk118ValidityFacts : SKFacts sk118Slice
    sk118LogOuterCertificate sk118LogKCertificate
    sk118LogDArgCertificate :=
  { domain := by norm_num [sk118Slice]
    kPositive := by
      norm_num [sk118Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk118LogOuter_valid
    logK := sk118LogK_valid
    logDArg := sk118LogDArg_valid }

noncomputable def sk118RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11595863/8388608), upper := (23258161/16777216) }
    logK := { lower := (18344045/16777216), upper := (2303957/2097152) }
    logDArg := { lower := (594987/2097152), upper := (2457057/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk118LogOuterInput_eq :
    sk118RoundedInputs.logOuter = outerEnclosure 24
      (sk118LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk118LogKInput_eq :
    sk118RoundedInputs.logK = outerEnclosure 24
      (sk118LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk118LogDArgInput_eq :
    sk118RoundedInputs.logDArg = outerEnclosure 24
      (sk118LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk118RoundedFacts : SKRoundedFacts 8
    sk118LogOuterCertificate sk118LogKCertificate
    sk118LogDArgCertificate sk118RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk118LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk118LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk118LogDArgInput_eq }

noncomputable def sk119Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (187/64) }

noncomputable def sk119LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (8191627/4194304) }, upper := { exponent := 1, mantissa := (251/128) } }

noncomputable def sk119LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (93/64) }, upper := { exponent := 1, mantissa := (187/128) } }

noncomputable def sk119LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (1015750701/759824384) }, upper := { exponent := 0, mantissa := (251/186) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk119LogOuter_valid :
    sk119LogOuterCertificate.check sk119Slice.outerAD.value = true := by
  norm_num [sk119LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk119Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk119LogK_valid :
    sk119LogKCertificate.check sk119Slice.kAD.value = true := by
  norm_num [sk119LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk119Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk119LogDArg_valid :
    sk119LogDArgCertificate.check sk119Slice.dArgAD.value = true := by
  norm_num [sk119LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk119Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk119ValidityFacts : SKFacts sk119Slice
    sk119LogOuterCertificate sk119LogKCertificate
    sk119LogDArgCertificate :=
  { domain := by norm_num [sk119Slice]
    kPositive := by
      norm_num [sk119Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk119LogOuter_valid
    logK := sk119LogK_valid
    logDArg := sk119LogDArg_valid }

noncomputable def sk119RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (11429749/8388608), upper := (22927239/16777216) }
    logK := { lower := (2237375/2097152), upper := (562155/524288) }
    logDArg := { lower := (1217589/4194304), upper := (5028237/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk119LogOuterInput_eq :
    sk119RoundedInputs.logOuter = outerEnclosure 24
      (sk119LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk119LogKInput_eq :
    sk119RoundedInputs.logK = outerEnclosure 24
      (sk119LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk119LogDArgInput_eq :
    sk119RoundedInputs.logDArg = outerEnclosure 24
      (sk119LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk119RoundedFacts : SKRoundedFacts 8
    sk119LogOuterCertificate sk119LogKCertificate
    sk119LogDArgCertificate sk119RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk119LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk119LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk119LogDArgInput_eq }

noncomputable def sk120Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (187/64), kHi := (47/16) }

noncomputable def sk120LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (8224393/4194304) }, upper := { exponent := 1, mantissa := (63/32) } }

noncomputable def sk120LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (187/128) }, upper := { exponent := 1, mantissa := (47/32) } }

noncomputable def sk120LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (279626349/209453056) }, upper := { exponent := 0, mantissa := (252/187) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk120LogOuter_valid :
    sk120LogOuterCertificate.check sk120Slice.outerAD.value = true := by
  norm_num [sk120LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk120Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk120LogK_valid :
    sk120LogKCertificate.check sk120Slice.kAD.value = true := by
  norm_num [sk120LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk120Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk120LogDArg_valid :
    sk120LogDArgCertificate.check sk120Slice.dArgAD.value = true := by
  norm_num [sk120LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk120Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk120ValidityFacts : SKFacts sk120Slice
    sk120LogOuterCertificate sk120LogKCertificate
    sk120LogDArgCertificate :=
  { domain := by norm_num [sk120Slice]
    kPositive := by
      norm_num [sk120Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk120LogOuter_valid
    logK := sk120LogK_valid
    logDArg := sk120LogDArg_valid }

noncomputable def sk120RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (2865809/2097152), upper := (22993947/16777216) }
    logK := { lower := (17988959/16777216), upper := (18078439/16777216) }
    logDArg := { lower := (4847853/16777216), upper := (5004987/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk120LogOuterInput_eq :
    sk120RoundedInputs.logOuter = outerEnclosure 24
      (sk120LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk120LogKInput_eq :
    sk120RoundedInputs.logK = outerEnclosure 24
      (sk120LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk120LogDArgInput_eq :
    sk120RoundedInputs.logDArg = outerEnclosure 24
      (sk120LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk120RoundedFacts : SKRoundedFacts 8
    sk120LogOuterCertificate sk120LogKCertificate
    sk120LogDArgCertificate sk120RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk120LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk120LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk120LogDArgInput_eq }

noncomputable def sk121Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8) }

noncomputable def sk121LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1048527/524288) }, upper := { exponent := 2, mantissa := (33/32) } }

noncomputable def sk121LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3/2) }, upper := { exponent := 1, mantissa := (25/16) } }

noncomputable def sk121LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (16765493/13107200) }, upper := { exponent := 0, mantissa := (11/8) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk121LogOuter_valid :
    sk121LogOuterCertificate.check sk121Slice.outerAD.value = true := by
  norm_num [sk121LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk121Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk121LogK_valid :
    sk121LogKCertificate.check sk121Slice.kAD.value = true := by
  norm_num [sk121LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk121Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk121LogDArg_valid :
    sk121LogDArgCertificate.check sk121Slice.dArgAD.value = true := by
  norm_num [sk121LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk121Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk121ValidityFacts : SKFacts sk121Slice
    sk121LogOuterCertificate sk121LogKCertificate
    sk121LogDArgCertificate :=
  { domain := by norm_num [sk121Slice]
    kPositive := by
      norm_num [sk121Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk121LogOuter_valid
    logK := sk121LogK_valid
    logDArg := sk121LogDArg_valid }

noncomputable def sk121RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23257375/16777216), upper := (2971803/2097152) }
    logK := { lower := (18431655/16777216), upper := (2389567/2097152) }
    logDArg := { lower := (4129897/16777216), upper := (333923/1048576) } }

set_option maxRecDepth 1000000 in
private theorem sk121LogOuterInput_eq :
    sk121RoundedInputs.logOuter = outerEnclosure 24
      (sk121LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk121LogKInput_eq :
    sk121RoundedInputs.logK = outerEnclosure 24
      (sk121LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk121LogDArgInput_eq :
    sk121RoundedInputs.logDArg = outerEnclosure 24
      (sk121LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk121RoundedFacts : SKRoundedFacts 8
    sk121LogOuterCertificate sk121LogKCertificate
    sk121LogDArgCertificate sk121RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk121LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk121LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk121LogDArgInput_eq }

noncomputable def sk122Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4) }

noncomputable def sk122LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (1081293/1048576) }, upper := { exponent := 2, mantissa := (17/16) } }

noncomputable def sk122LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (25/16) }, upper := { exponent := 1, mantissa := (13/8) } }

noncomputable def sk122LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (54031831/42598400) }, upper := { exponent := 0, mantissa := (34/25) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk122LogOuter_valid :
    sk122LogOuterCertificate.check sk122Slice.outerAD.value = true := by
  norm_num [sk122LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk122Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk122LogK_valid :
    sk122LogKCertificate.check sk122Slice.kAD.value = true := by
  norm_num [sk122LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk122Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk122LogDArg_valid :
    sk122LogDArgCertificate.check sk122Slice.dArgAD.value = true := by
  norm_num [sk122LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk122Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk122ValidityFacts : SKFacts sk122Slice
    sk122LogOuterCertificate sk122LogKCertificate
    sk122LogDArgCertificate :=
  { domain := by norm_num [sk122Slice]
    kPositive := by
      norm_num [sk122Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk122LogOuter_valid
    logK := sk122LogK_valid
    logDArg := sk122LogDArg_valid }

noncomputable def sk122RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23773631/16777216), upper := (24275273/16777216) }
    logK := { lower := (19116535/16777216), upper := (9887275/8388608) }
    logDArg := { lower := (1994447/8388608), upper := (2579369/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk122LogOuterInput_eq :
    sk122RoundedInputs.logOuter = outerEnclosure 24
      (sk122LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk122LogKInput_eq :
    sk122RoundedInputs.logK = outerEnclosure 24
      (sk122LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk122LogDArgInput_eq :
    sk122RoundedInputs.logDArg = outerEnclosure 24
      (sk122LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk122RoundedFacts : SKRoundedFacts 8
    sk122LogOuterCertificate sk122LogKCertificate
    sk122LogDArgCertificate sk122RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk122LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk122LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk122LogDArgInput_eq }

noncomputable def sk123Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16) }

noncomputable def sk123LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (2097055/1048576) }, upper := { exponent := 2, mantissa := (65/64) } }

noncomputable def sk123LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (3/2) }, upper := { exponent := 1, mantissa := (49/32) } }

noncomputable def sk123LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (67094805/51380224) }, upper := { exponent := 0, mantissa := (65/48) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk123LogOuter_valid :
    sk123LogOuterCertificate.check sk123Slice.outerAD.value = true := by
  norm_num [sk123LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk123Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk123LogK_valid :
    sk123LogKCertificate.check sk123Slice.kAD.value = true := by
  norm_num [sk123LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk123Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk123LogDArg_valid :
    sk123LogDArgCertificate.check sk123Slice.dArgAD.value = true := by
  norm_num [sk123LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk123Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk123ValidityFacts : SKFacts sk123Slice
    sk123LogOuterCertificate sk123LogKCertificate
    sk123LogDArgCertificate :=
  { domain := by norm_num [sk123Slice]
    kPositive := by
      norm_num [sk123Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk123LogOuter_valid
    logK := sk123LogK_valid
    logDArg := sk123LogDArg_valid }

noncomputable def sk123RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23257383/16777216), upper := (11759139/8388608) }
    logK := { lower := (18431655/16777216), upper := (18777591/16777216) }
    logDArg := { lower := (2238527/8388608), upper := (2543311/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk123LogOuterInput_eq :
    sk123RoundedInputs.logOuter = outerEnclosure 24
      (sk123LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk123LogKInput_eq :
    sk123RoundedInputs.logK = outerEnclosure 24
      (sk123LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk123LogDArgInput_eq :
    sk123RoundedInputs.logDArg = outerEnclosure 24
      (sk123LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk123RoundedFacts : SKRoundedFacts 8
    sk123LogOuterCertificate sk123LogKCertificate
    sk123LogDArgCertificate sk123RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk123LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk123LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk123LogDArgInput_eq }

noncomputable def sk124Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8) }

noncomputable def sk124LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2129821/2097152) }, upper := { exponent := 2, mantissa := (33/32) } }

noncomputable def sk124LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (49/32) }, upper := { exponent := 1, mantissa := (25/16) } }

noncomputable def sk124LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (208689591/160563200) }, upper := { exponent := 0, mantissa := (66/49) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk124LogOuter_valid :
    sk124LogOuterCertificate.check sk124Slice.outerAD.value = true := by
  norm_num [sk124LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk124Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk124LogK_valid :
    sk124LogKCertificate.check sk124Slice.kAD.value = true := by
  norm_num [sk124LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk124Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk124LogDArg_valid :
    sk124LogDArgCertificate.check sk124Slice.dArgAD.value = true := by
  norm_num [sk124LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk124Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk124ValidityFacts : SKFacts sk124Slice
    sk124LogOuterCertificate sk124LogKCertificate
    sk124LogDArgCertificate :=
  { domain := by norm_num [sk124Slice]
    kPositive := by
      norm_num [sk124Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk124LogOuter_valid
    logK := sk124LogK_valid
    logDArg := sk124LogDArg_valid }

noncomputable def sk124RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23517497/16777216), upper := (2971803/2097152) }
    logK := { lower := (18777589/16777216), upper := (2389567/2097152) }
    logDArg := { lower := (274895/1048576), upper := (4996833/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk124LogOuterInput_eq :
    sk124RoundedInputs.logOuter = outerEnclosure 24
      (sk124LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk124LogKInput_eq :
    sk124RoundedInputs.logK = outerEnclosure 24
      (sk124LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk124LogDArgInput_eq :
    sk124RoundedInputs.logDArg = outerEnclosure 24
      (sk124LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk124RoundedFacts : SKRoundedFacts 8
    sk124LogOuterCertificate sk124LogKCertificate
    sk124LogDArgCertificate sk124RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk124LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk124LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk124LogDArgInput_eq }

noncomputable def sk125Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16) }

noncomputable def sk125LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2162587/2097152) }, upper := { exponent := 2, mantissa := (67/64) } }

noncomputable def sk125LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (25/16) }, upper := { exponent := 1, mantissa := (51/32) } }

noncomputable def sk125LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (72075277/55705600) }, upper := { exponent := 0, mantissa := (67/50) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk125LogOuter_valid :
    sk125LogOuterCertificate.check sk125Slice.outerAD.value = true := by
  norm_num [sk125LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk125Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk125LogK_valid :
    sk125LogKCertificate.check sk125Slice.kAD.value = true := by
  norm_num [sk125LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk125Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk125LogDArg_valid :
    sk125LogDArgCertificate.check sk125Slice.dArgAD.value = true := by
  norm_num [sk125LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk125Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk125ValidityFacts : SKFacts sk125Slice
    sk125LogOuterCertificate sk125LogKCertificate
    sk125LogDArgCertificate :=
  { domain := by norm_num [sk125Slice]
    kPositive := by
      norm_num [sk125Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk125LogOuter_valid
    logK := sk125LogK_valid
    logDArg := sk125LogDArg_valid }

noncomputable def sk125RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (23773639/16777216), upper := (24026717/16777216) }
    logK := { lower := (19116535/16777216), upper := (19448769/16777216) }
    logDArg := { lower := (270145/1048576), upper := (2455091/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk125LogOuterInput_eq :
    sk125RoundedInputs.logOuter = outerEnclosure 24
      (sk125LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk125LogKInput_eq :
    sk125RoundedInputs.logK = outerEnclosure 24
      (sk125LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk125LogDArgInput_eq :
    sk125RoundedInputs.logDArg = outerEnclosure 24
      (sk125LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk125RoundedFacts : SKRoundedFacts 8
    sk125LogOuterCertificate sk125LogKCertificate
    sk125LogDArgCertificate sk125RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk125LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk125LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk125LogDArgInput_eq }

noncomputable def sk126Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4) }

noncomputable def sk126LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (2195353/2097152) }, upper := { exponent := 2, mantissa := (17/16) } }

noncomputable def sk126LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (51/32) }, upper := { exponent := 1, mantissa := (13/8) } }

noncomputable def sk126LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (74631045/57933824) }, upper := { exponent := 0, mantissa := (4/3) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk126LogOuter_valid :
    sk126LogOuterCertificate.check sk126Slice.outerAD.value = true := by
  norm_num [sk126LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk126Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk126LogK_valid :
    sk126LogKCertificate.check sk126Slice.kAD.value = true := by
  norm_num [sk126LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk126Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk126LogDArg_valid :
    sk126LogDArgCertificate.check sk126Slice.dArgAD.value = true := by
  norm_num [sk126LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk126Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk126ValidityFacts : SKFacts sk126Slice
    sk126LogOuterCertificate sk126LogKCertificate
    sk126LogDArgCertificate :=
  { domain := by norm_num [sk126Slice]
    kPositive := by
      norm_num [sk126Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk126LogOuter_valid
    logK := sk126LogK_valid
    logDArg := sk126LogDArg_valid }

noncomputable def sk126RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (24025929/16777216), upper := (24275273/16777216) }
    logK := { lower := (303887/262144), upper := (9887275/8388608) }
    logDArg := { lower := (1062229/4194304), upper := (4826505/16777216) } }

set_option maxRecDepth 1000000 in
private theorem sk126LogOuterInput_eq :
    sk126RoundedInputs.logOuter = outerEnclosure 24
      (sk126LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk126LogKInput_eq :
    sk126RoundedInputs.logK = outerEnclosure 24
      (sk126LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk126LogDArgInput_eq :
    sk126RoundedInputs.logDArg = outerEnclosure 24
      (sk126LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk126RoundedFacts : SKRoundedFacts 8
    sk126LogOuterCertificate sk126LogKCertificate
    sk126LogDArgCertificate sk126RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk126LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk126LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk126LogDArgInput_eq }

noncomputable def sk127Slice : SKSlice :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8) }

noncomputable def sk127LogOuterCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 2, mantissa := (1114059/1048576) }, upper := { exponent := 2, mantissa := (35/32) } }

noncomputable def sk127LogKCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (13/8) }, upper := { exponent := 1, mantissa := (27/16) } }

noncomputable def sk127LogDArgCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 0, mantissa := (57898247/46006272) }, upper := { exponent := 0, mantissa := (35/26) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sk127LogOuter_valid :
    sk127LogOuterCertificate.check sk127Slice.outerAD.value = true := by
  norm_num [sk127LogOuterCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk127Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk127LogK_valid :
    sk127LogKCertificate.check sk127Slice.kAD.value = true := by
  norm_num [sk127LogKCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk127Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
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
private theorem sk127LogDArg_valid :
    sk127LogDArgCertificate.check sk127Slice.dArgAD.value = true := by
  norm_num [sk127LogDArgCertificate,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, sk127Slice,
    SKSlice.sAD, SKSlice.kAD, SKSlice.rAD, SKSlice.outerAD,
    SKSlice.dArgAD, IntervalAD.const, IntervalAD.add,
    IntervalAD.neg, IntervalAD.sub, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    IntervalAD.variableS, IntervalAD.variableK,
    RationalEnclosure.point, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.sub,
    RationalEnclosure.mul, RationalEnclosure.div,
    RationalEnclosure.mulNonnegative,
    RationalEnclosure.invPositive, RationalEnclosure.center,
    RationalEnclosure.radius]

theorem sk127ValidityFacts : SKFacts sk127Slice
    sk127LogOuterCertificate sk127LogKCertificate
    sk127LogDArgCertificate :=
  { domain := by norm_num [sk127Slice]
    kPositive := by
      norm_num [sk127Slice, SKSlice.kAD, IntervalAD.variableK,
        RationalEnclosure.point]
    logOuter := sk127LogOuter_valid
    logK := sk127LogK_valid
    logDArg := sk127LogDArg_valid }

noncomputable def sk127RoundedInputs : SKRoundedInputs :=
  { logOuter := { lower := (12137237/8388608), upper := (6190401/4194304) }
    logK := { lower := (19774549/16777216), upper := (1275483/1048576) }
    logDArg := { lower := (3857239/16777216), upper := (2493527/8388608) } }

set_option maxRecDepth 1000000 in
private theorem sk127LogOuterInput_eq :
    sk127RoundedInputs.logOuter = outerEnclosure 24
      (sk127LogOuterCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk127LogKInput_eq :
    sk127RoundedInputs.logK = outerEnclosure 24
      (sk127LogKCertificate.enclosure 8) := by
  rfl'

set_option maxRecDepth 1000000 in
private theorem sk127LogDArgInput_eq :
    sk127RoundedInputs.logDArg = outerEnclosure 24
      (sk127LogDArgCertificate.enclosure 8) := by
  rfl'

theorem sk127RoundedFacts : SKRoundedFacts 8
    sk127LogOuterCertificate sk127LogKCertificate
    sk127LogDArgCertificate sk127RoundedInputs :=
  { coversLogOuter := covers_of_outerEnclosure_eq 24 sk127LogOuterInput_eq
    coversLogK := covers_of_outerEnclosure_eq 24 sk127LogKInput_eq
    coversLogDArg := covers_of_outerEnclosure_eq 24 sk127LogDArgInput_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
